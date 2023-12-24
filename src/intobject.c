/***********************************************************
Copyright 1991 by Stichting Mathematisch Centrum, Amsterdam, The
Netherlands.

                        All Rights Reserved

Permission to use, copy, modify, and distribute this software and its
documentation for any purpose and without fee is hereby granted,
provided that the above copyright notice appear in all copies and that
both that copyright notice and this permission notice appear in
supporting documentation, and that the names of Stichting Mathematisch
Centrum or CWI not be used in advertising or publicity pertaining to
distribution of the software without specific, written prior permission.

STICHTING MATHEMATISCH CENTRUM DISCLAIMS ALL WARRANTIES WITH REGARD TO
THIS SOFTWARE, INCLUDING ALL IMPLIED WARRANTIES OF MERCHANTABILITY AND
FITNESS, IN NO EVENT SHALL STICHTING MATHEMATISCH CENTRUM BE LIABLE
FOR ANY SPECIAL, INDIRECT OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT
OF OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.

******************************************************************/

/* Integer object implementation */

#include "allobjects.h"

#ifndef LONG_MAX
#define LONG_MAX 0X7FFFFFFFL
#endif

#ifndef LONG_MIN
#define LONG_MIN (-LONG_MAX-1)
#endif

#ifndef CHAR_BIT
#define CHAR_BIT 8
#endif

#ifndef LONG_BIT
#define LONG_BIT (CHAR_BIT * sizeof(long))
#endif

/* Standard Booleans */

intobject FalseObject = {
       OB_HEAD_INIT(&Inttype)
       0
};

intobject TrueObject = {
       OB_HEAD_INIT(&Inttype)
       1
};

static object *
err_ovf()
{
       err_setstr(OverflowError, "integer overflow");
       return NULL;
}

static object *
err_zdiv()
{
       err_setstr(ZeroDivisionError, "integer division by zero");
       return NULL;
}

/* Integers are quite normal objects, to make object handling uniform.
   (Using odd pointers to represent integers would save much space
   but require extra checks for this special case throughout the code.)
   Since, a typical Python program spends much of its time allocating
   and deallocating integers, these operations should be very fast.
   Therefore we use a dedicated allocation scheme with a much lower
   overhead (in space and time) than straight malloc(): a simple
   dedicated free list, filled when necessary with memory from malloc().
*/

#define BLOCK_SIZE     1000    /* 1K less typical malloc overhead */
#define N_INTOBJECTS   (BLOCK_SIZE / sizeof(intobject))

static intobject *
fill_free_list()
{
       intobject *p, *q;
       p = NEW(intobject, N_INTOBJECTS);
       if (p == NULL)
               return (intobject *)err_nomem();
       q = p + N_INTOBJECTS;
       while (--q > p)
               *(intobject **)q = q-1;
       *(intobject **)q = NULL;
       return p + N_INTOBJECTS - 1;
}

static intobject *free_list = NULL;

object *
newintobject(ival)
       long ival;
{
       register intobject *v;
       if (free_list == NULL) {
               if ((free_list = fill_free_list()) == NULL)
                       return NULL;
       }
       v = free_list;
       free_list = *(intobject **)free_list;
       NEWREF(v);
       v->ob_type = &Inttype;
       v->ob_ival = ival;
       return (object *) v;
}

static void
int_dealloc(v)
       intobject *v;
{
       *(intobject **)v = free_list;
       free_list = v;
}

long
getintvalue(op)
       register object *op;
{
       if (!is_intobject(op)) {
               err_badcall();
               return -1;
       }
       else
               return ((intobject *)op) -> ob_ival;
}

/* Methods */

static void
int_print(v, fp, flags)
       intobject *v;
       FILE *fp;
       int flags;
{
       fprintf(fp, "%ld", v->ob_ival);
}

static object *
int_repr(v)
       intobject *v;
{
       char buf[20];
       sprintf(buf, "%ld", v->ob_ival);
       return newstringobject(buf);
}

static int
int_compare(v, w)
       intobject *v, *w;
{
       register long i = v->ob_ival;
       register long j = w->ob_ival;
       return (i < j) ? -1 : (i > j) ? 1 : 0;
}

static object *
int_add(v, w)
       intobject *v;
       register object *w;
{
       register long a, b, x;
       if (!is_intobject(w)) {
               err_badarg();
               return NULL;
       }
       a = v->ob_ival;
       b = ((intobject *)w) -> ob_ival;
       x = a + b;
       if ((x^a) < 0 && (x^b) < 0)
               return err_ovf();
       return newintobject(x);
}

static object *
int_sub(v, w)
       intobject *v;
       register object *w;
{
       register long a, b, x;
       if (!is_intobject(w)) {
               err_badarg();
               return NULL;
       }
       a = v->ob_ival;
       b = ((intobject *)w) -> ob_ival;
       x = a - b;
       if ((x^a) < 0 && (x^~b) < 0)
               return err_ovf();
       return newintobject(x);
}

/*static object *
int_mul(v, w)
       intobject *v;
       register object *w;
{
       register long a, b;
       double x;
       if (!is_intobject(w)) {
               err_badarg();
               return NULL;
       }
       a = v->ob_ival;
       b = ((intobject *)w) -> ob_ival;
       x = (double)a * (double)b;
       if (x > 0x7fffffff || x < (double) (long) 0x80000000)
               return err_ovf();
       
       return newintobject(a * b);
}*/

/* NOTE: The above algorithm used to calculate integer overflow doesn't work on 64-bit systems.
         Hence, the below algorithm is taken from stable python release v1.6.
         For more info, visit Objects/intobject.h file from its source code
         Edited by M.V.Harish Kumar on 24-12-2023

         Please note that some new constants are also added at the top of the file, taken from py1.6 src
*/
static object *
int_mul(v, w)
	intobject *v;
       register object *w;
{
	register long a, b, ah, bh, x, y;
	int s = 1;
       if (!is_intobject(w)) {
               err_badarg();
               return NULL;
       }

	a = v->ob_ival;
	b = ((intobject *)w) -> ob_ival;
	ah = a >> (LONG_BIT/2);
	bh = b >> (LONG_BIT/2);

	/* Quick test for common case: two small positive ints */

	if (ah == 0 && bh == 0) {
		x = a*b;
		if (x < 0)
			goto bad;
		return newintobject(x);
	}

	/* Arrange that a >= b >= 0 */

	if (a < 0) {
		a = -a;
		if (a < 0) {
			/* Largest negative */
			if (b == 0 || b == 1) {
				x = a*b;
				goto ok;
			}
			else
				goto bad;
		}
		s = -s;
		ah = a >> (LONG_BIT/2);
	}
	if (b < 0) {
		b = -b;
		if (b < 0) {
			/* Largest negative */
			if (a == 0 || (a == 1 && s == 1)) {
				x = a*b;
				goto ok;
			}
			else
				goto bad;
		}
		s = -s;
		bh = b >> (LONG_BIT/2);
	}

	/* 1) both ah and bh > 0 : then report overflow */

	if (ah != 0 && bh != 0)
		goto bad;

	/* 2) both ah and bh = 0 : then compute a*b and report
				   overflow if it comes out negative */

	if (ah == 0 && bh == 0) {
		x = a*b;
		if (x < 0)
			goto bad;
		return newintobject(x*s);
	}

	if (a < b) {
		/* Swap */
		x = a;
		a = b;
		b = x;
		ah = bh;
		/* bh not used beyond this point */
	}

	/* 3) ah > 0 and bh = 0  : compute ah*bl and report overflow if
				   it's >= 2^31
                        compute al*bl and report overflow if it's negative
                        add (ah*bl)<<32 to al*bl and report overflow if
                        it's negative
			(NB b == bl in this case, and we make a = al) */

	y = ah*b;
	if (y >= (1L << (LONG_BIT/2 - 1)))
		goto bad;
	a &= (1L << (LONG_BIT/2)) - 1;
	x = a*b;
	if (x < 0)
		goto bad;
	x += y << (LONG_BIT/2);
	if (x < 0)
		goto bad;
 ok:
	return newintobject(x * s);

 bad:
	return err_ovf();
}

static object *
int_div(v, w)
       intobject *v;
       register object *w;
{
       if (!is_intobject(w)) {
               err_badarg();
               return NULL;
       }
       if (((intobject *)w) -> ob_ival == 0)
               return err_zdiv();
       return newintobject(v->ob_ival / ((intobject *)w) -> ob_ival);
}

static object *
int_rem(v, w)
       intobject *v;
       register object *w;
{
       if (!is_intobject(w)) {
               err_badarg();
               return NULL;
       }
       if (((intobject *)w) -> ob_ival == 0)
               return err_zdiv();
       return newintobject(v->ob_ival % ((intobject *)w) -> ob_ival);
}

static object *
int_pow(v, w)
       intobject *v;
       register object *w;
{
       register long iv, iw, ix;
       register int neg;
       if (!is_intobject(w)) {
               err_badarg();
               return NULL;
       }
       iv = v->ob_ival;
       iw = ((intobject *)w)->ob_ival;
       neg = 0;
       if (iw < 0)
               neg = 1, iw = -iw;
       ix = 1;
       for (; iw > 0; iw--)
               ix = ix * iv;
       if (neg) {
               if (ix == 0)
                       return err_zdiv();
               ix = 1/ix;
       }
       /* XXX How to check for overflow? */
       return newintobject(ix);
}

static object *
int_neg(v)
       intobject *v;
{
       register long a, x;
       a = v->ob_ival;
       x = -a;
       if (a < 0 && x < 0)
               return err_ovf();
       return newintobject(x);
}

static object *
int_pos(v)
       intobject *v;
{
       INCREF(v);
       return (object *)v;
}

static number_methods int_as_number = {
       int_add,        /*tp_add*/
       int_sub,        /*tp_subtract*/
       int_mul,        /*tp_multiply*/
       int_div,        /*tp_divide*/
       int_rem,        /*tp_remainder*/
       int_pow,        /*tp_power*/
       int_neg,        /*tp_negate*/
       int_pos,        /*tp_plus*/
};

typeobject Inttype = {
       OB_HEAD_INIT(&Typetype)
       0,
       "int",
       sizeof(intobject),
       0,
       int_dealloc,    /*tp_dealloc*/
       int_print,      /*tp_print*/
       0,              /*tp_getattr*/
       0,              /*tp_setattr*/
       int_compare,    /*tp_compare*/
       int_repr,       /*tp_repr*/
       &int_as_number,     /*tp_as_number*/
       0,              /*tp_as_sequence*/
       0,              /*tp_as_mapping*/
};
