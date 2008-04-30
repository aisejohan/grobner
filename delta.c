/*
 *	delta.c
 *
 * 	Copyright 2006 Johan de Jong
 *
 *	This file is part of Frobenius
 *
 *	Frobenius is free software; you can redistribute it and/or modify
 *	it under the terms of the GNU General Public License as published by
 *	the Free Software Foundation; either version 2 of the License, or
 *	(at your option) any later version.
 *
 *	Frobenius is distributed in the hope that it will be useful,
 *	but WITHOUT ANY WARRANTY; without even the implied warranty of
 *	MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *	GNU General Public License for more details.
 *
 *	You should have received a copy of the GNU General Public License
 *	along with Frobenius; if not, write to the Free Software Foundation, 
 *	Inc., 51 Franklin St, Fifth Floor, Boston, MA  02110-1301  USA
 *
 *									*/

#include <stddef.h>
#include <stdlib.h>
#include <stdio.h>

#include "data.h"
#include "scalar.h"
#include "pol.h"
#include "helper.h"
#include "grobner.h"
#include "compute.h"
#include "delta.h"

/* Computes p*Delta.							*
 * This will only be run once!						*/
struct polynomial compute_delta(void)
{
	int i;
	struct polynomial A, B, C;
	A.leading = NULL;
	B.leading = NULL;
	C.leading = NULL;

	A = copy_pol(myf);
	B = copy_pol(myf);
	for (i = 2; i <= p; i++)
	{
		C = pol_mult(A, B);
		free_tail(B.leading);
		B = C;
		C.leading = NULL;
		C.degree = 0;
	}
	free_tail(A.leading);
	A.leading = NULL;
	A.degree = 0;
	A = frobenius(myf);

	/* Replace A by negative. */
	times_int(-1, &A);

	/* Add -F(f) + f^p */
	C = pol_add(A, B);

	free_tail(A.leading);
	free_tail(B.leading);
	
	return(C);
}

/* This functions checks flatness in degree degree.			*
 * Returns: 								*
 * 	-1 if flat but not usable,					*
 * 	-2 if not flat,and 						*
 * 	the dimension if flat.						*
 * 									*
 * Meaning of the counts:						*
 * 		count1 = is sometimes too small				*
 * 		count2 = is sometimes too large				*
 * 		goodcount = what you are supposed to get in char 0.	*
 * 		count = the correct count using the ideal		*
 * If count1 = count2 = goodcount, then you are flat for sure. If this	*
 * doesn't happen then we do an extra check and produce the correct	*
 * count, called count. This function is ridiculously complicated due	*
 * to our choice of ordering of terms.					*/
int check_flatness(unsigned int degree)
{
	int i, j, b1, b2, blen, aantal;
	int count, count1, count2, goodcount;
	mscalar c;
	unsigned int a1, a2, a3, a4;
	struct term tmp, least;
	struct term **tt;
	struct polynomial T, TT;
	struct polynomial **bb, **aa;
	tmp.next = NULL;
	least.next = NULL;
	make_scalar(c);
	make_scalar(tmp.c);
	make_scalar(least.c);
	T.leading = NULL;
	TT.leading = NULL;
	
	if (!count_sum(degree)) {
		free_scalar(least.c);
		free_scalar(tmp.c);
		free_scalar(c);
		return(0);
	}
	count = 0;
	count1 = 0;
	count2 = 0;
	goodcount = count_sum(degree);
	
	if (degree >= d - d1) 
		goodcount -= count_sum(degree - d + d1);
	if (degree >= d - d2) 
		goodcount -= count_sum(degree - d + d2);
	if (degree >= d - d3) 
		goodcount -= count_sum(degree - d + d3);
	if (degree >= d - d4) 
		goodcount -= count_sum(degree - d + d4);
	if (degree >= 2*d - (d1 + d2)) 
		goodcount += count_sum(degree - 2*d + (d1 + d2));
	if (degree >= 2*d - (d1 + d3)) 
		goodcount += count_sum(degree - 2*d + (d1 + d3));
	if (degree >= 2*d - (d1 + d4)) 
		goodcount += count_sum(degree - 2*d + (d1 + d4));
	if (degree >= 2*d - (d2 + d3)) 
		goodcount += count_sum(degree - 2*d + (d2 + d3));
	if (degree >= 2*d - (d2 + d4)) 
		goodcount += count_sum(degree - 2*d + (d2 + d4));
	if (degree >= 2*d - (d3 + d4)) 
		goodcount += count_sum(degree - 2*d + (d3 + d4));
	if (degree >= 3*d - (d1 + d2 + d3)) 
		goodcount -= count_sum(degree - 3*d + (d1 + d2 + d3));
	if (degree >= 3*d - (d1 + d2 + d4)) 
		goodcount -= count_sum(degree - 3*d + (d1 + d2 + d4));
	if (degree >= 3*d - (d1 + d3 + d4)) 
		goodcount -= count_sum(degree - 3*d + (d1 + d3 + d4));
	if (degree >= 3*d - (d2 + d3 + d4)) 
		goodcount -= count_sum(degree - 3*d + (d2 + d3 + d4));
	if (degree >= 4*d - (d1 + d2 + d3 + d4))
		goodcount += count_sum(degree - 4*d + (d1 + d2 + d3 + d4));
	
	for (a1 = 0; (d1*a1 <= degree); a1++) {
	  for (a2 = 0; (d1*a1 + d2*a2 <= degree); a2++) {
	    for (a3 = 0; (d1*a1 + d2*a2 + d3*a3 <= degree); a3++) {
	      if ((degree - (a1*d1 + a2*d2 + a3*d3)) % d4 == 0) {
		a4 = (degree - (a1*d1 + a2*d2 + a3*d3))/d4;
		b1 = 0;
		b2 = 0;
		for (i = 0; i + 1 <= G.len; i++) {
			if ((G.ee[i]->e1 <= a1) &&
			(G.ee[i]->e2 <= a2) &&
			(G.ee[i]->e3 <= a3) &&
			(G.ee[i]->e4 <= a4)) {
				b1 = 1;
				if (G.ee[i]->e5 == 0) b2 = 1;
			}
		}
		if (!b1) count1++;
		if (!b2) count2++;
	      }
	    }
	  }
	}
	if (count2 != goodcount) {
/*		printf("Here we have degree %d, count1 %d"
		", count2 %d, and goodcount %d\n",
		degree,count1,count2,goodcount);
*/		
		aantal = count_sum(degree);
		bb = (struct polynomial **)
			malloc((G.len + aantal)*sizeof(struct polynomial *));
		if (!bb) {
			perror("Malloc failed!");
			exit(1);
		}
		for (i = 0; i + 1 <= G.len + aantal; i++) {
			bb[i] = NULL;
			make_pol(&bb[i]);
		}
		for (i = 0; i + 1 <= G.len; i++) {
			bb[i]->degree = G.ff[i]->degree;
			bb[i]->leading = G.ff[i]->leading;
		}
		blen = G.len;
		
		tt = (struct term **)
			malloc(aantal*sizeof(struct term *));
		if (!tt) {
			perror("Malloc failed!");
			exit(1);
		}
		for (i = 0; i + 1 <= aantal; i++) {
			tt[i] = NULL;
			make_term(&tt[i]);
		}
		
		/* Make sure c = p^{r-1}. */
		sc_one(c);
		for (i = 1; i + 1 <= r; i++) sc_imult_replace(p, c);
		
		/* Make list of terms. */
		i = 0;
		sc_copy(c, tmp.c);
		tmp.next = NULL;
		for (a1 = 0; (d1*a1 <= degree); a1++) {
		  for (a2 = 0; (d1*a1 + d2*a2 <= degree); a2++) {
		    for (a3 = 0; (d1*a1 + d2*a2 + d3*a3 <= degree); a3++) {
		      if ((degree - (a1*d1 + a2*d2 + a3*d3)) % d4 == 0) {
			a4 = (degree - (a1*d1 + a2*d2 + a3*d3))/d4;
			tmp.n1 = a1;
			tmp.n2 = a2;
			tmp.n3 = a3;
			tmp.n4 = a4;
			copy_term(&tmp, tt[i]);
			tt[i]->next = NULL;
			i++;
		      }
		    }
		  }
		}

#ifdef KIJKEN
		if (i > aantal) {
			printf("ERROR!\n");
			exit(1);
		}
#endif

		/* Order the list so the smallest is first.	*
		 * This is stupid sorting so hopefully		*
		 * the list is not too long!			*/
		for (i = 0; i <= aantal - 1; i++) {
			for (j = i + 1; j <= aantal - 1; j++) {
				if (kleiner(tt[i], tt[j]) == GROTER) {
					copy_term(tt[i], &tmp);
					copy_term(tt[j], tt[i]);
					copy_term(&tmp, tt[j]);
				}
			}
		}
		
		count = 0;
		for (j = 0; j <= aantal - 1; j++) {
			copy_term(tt[j], &least);
			least.next = NULL;
			T.degree = degree;
			T.leading = &least;
			if (!zero_on_division(T, blen, bb)) {
				TT = copy_pol(T);
				aa = gen_division(&TT, blen, bb);
				/* Free aa. */
				for (i = 0; i <= blen - 1; i++) {
					free_tail(aa[i]->leading);
					free(aa[i]);
				}
				free(aa);
				if (TT.leading) {
					count++;
					blen++;
					bb[blen - 1]->degree = TT.degree;
					bb[blen - 1]->leading = TT.leading;
				}
			}
		}
		
		/* Free tt */
		for (i = 0; i + 1 <= aantal; i++) {
			free_term(tt[i]);
		}
		free(tt);

		/* Free bb */
		for (i = 0; i + 1 <= G.len; i++) {
			bb[i]->leading = NULL;
		}
		for (i = G.len; i + 1 <= blen; i++) {
			free_tail(bb[i]->leading);
		}
		for (i = 0; i + 1 <= G.len + aantal; i++) {
			free(bb[i]);
		}
		free(bb);

		if (count != goodcount) {
			printf("In the final analysis we have: "
			"count = %d and goodcount = %d\n", count, goodcount);
			free_scalar(least.c);
			free_scalar(tmp.c);
			free_scalar(c);
			return(-2);
		} else {
			free_scalar(least.c);
			free_scalar(tmp.c);
			free_scalar(c);
			return(-1);
		}
	}
	free_scalar(least.c);
	free_scalar(tmp.c);
	free_scalar(c);
	return(goodcount);
}

/* Finds the basis of terms in degree degree.			*
 * This function assumes the function check_flatness has been	*
 * run previsouly and has returned a positive integer blen.	*/
struct term **find_basis(unsigned int degree, int blen)
{
	int a1, a2, a3, a4, count2, i, j, b2;	
	struct term tmp;
	struct term **tt;
	make_scalar(tmp.c);

	tt = (struct term **)malloc(blen*sizeof(struct term *));
	if (!tt) {
		perror("Malloc failed!");
		exit(1);
	}
	for (i = 0; i + 1 <= blen; i++) {
		tt[i] = NULL;
		make_term(&tt[i]);
	}
	
	count2 = 0;
	sc_one(tmp.c);
	for (a1 = 0; (d1*a1 <= degree); a1++) {
	  for (a2 = 0; (d1*a1 + d2*a2 <= degree); a2++) {
	    for (a3 = 0; (d1*a1 + d2*a2 + d3*a3 <= degree); a3++) {
	      if ((degree - (a1*d1 + a2*d2 + a3*d3)) % d4 == 0) {
		a4 = (degree - (a1*d1 + a2*d2 + a3*d3))/d4;
		b2 = 0;
		for (i = 0; i + 1 <= G.len; i++) {
			if ((G.ee[i]->e1 <= a1) &&
			(G.ee[i]->e2 <= a2) &&
			(G.ee[i]->e3 <= a3) &&
			(G.ee[i]->e4 <= a4)) {
				if (G.ee[i]->e5 == 0) b2 = 1;
			}
		}
		if (!b2) {
			count2++;
			if (count2 > blen) {
				printf("Wrong length basis!");
				exit(1);
			}
			/* tmp.c = 1 */
			tmp.n1 = a1;
			tmp.n2 = a2;
			tmp.n3 = a3;
			tmp.n4 = a4;
			copy_term(&tmp, tt[count2 - 1]);
			tt[count2 - 1]->next = NULL;
		}
	      }
	    }
	  }
	}
	
	/* Order the list so the largest is first.	*
	 * This is stupid sorting so hopefully		*
	 * the list is not too long!			*/
	for (i = 0; i <= blen - 1; i++) {
		for (j = i + 1; j <= blen- 1; j++) {
			if (kleiner(tt[i], tt[j]) == KLEINER) {
				copy_term(tt[i], &tmp);
				copy_term(tt[j], tt[i]);
				copy_term(&tmp, tt[j]);
			}
		}
	}
	free_scalar(tmp.c);
	return(tt);
}

/* Scalar multiple of a split polynomial. */
struct polynomial **copy_pol_star(mscalar c, struct polynomial **bb)
{
	struct polynomial **uit;
	int i, len;
	len = 1 + bb[0]->degree/d;
	uit = (struct polynomial **)
		malloc(len*sizeof(struct polynomial *));
	if (!uit) {
		perror("Malloc failed! (Again?)");
		exit(1);
	}
	for (i = 0; i + 1 <= len; i++) {
		uit[i] = NULL;
		make_pol(&uit[i]);
		*uit[i] = copy_pol(*bb[i]);
		times_scalar(c, uit[i]);
	}
	return(uit);
}

/* Scalar multiple of a split polynomial. */
void free_star(struct polynomial **bb)
{
	int i, len;

	len = 1 + bb[0]->degree/d;
	for (i = 0; i + 1 <= len; i++) {
		free_tail(bb[i]->leading);
		free(bb[i]);
	}
	return;
}

/* Splits up a polynomial into pieces.				*
 * Removes the tail of f, and sets f.leading=NULL		*/
struct polynomial **split_up(struct polynomial *f)
{
	int i, count;
	struct polynomial **uit;
#ifdef OLD_GROBNER
	struct polynomial *tussen;
	struct polynomial **aa;
#else
	struct polynomial *aa;
#endif

	count = 1 + f->degree/d;
	uit = (struct polynomial **)malloc(count*sizeof(struct polynomial *));
	if (!uit) {
		perror("Malloc failed!");
		exit(1);
	}
	for (i = 0; i + 1 <= count; i++) {
		uit[i] = NULL;
		make_pol(&uit[i]);
		uit[i]->degree = f->degree - i*d;
	}

	/* Zero case still has to work.	*/
	if (f->leading == NULL) {
		return(uit);
	}

#ifdef OLD_GROBNER
	tussen = &myf;
#endif
	uit[0]->leading = f->leading;
	f->leading = NULL;
	for (i = 0; i + 1 + 1 <= count; i++) {
#ifdef OLD_GROBNER
		aa = gen_division(uit[i], 1, &tussen);
		times_int(-1, aa[0]);
		uit[i + 1]->leading = aa[0]->leading;
		uit[i + 1]->degree = aa[0]->degree;
		free(aa[0]);
#else
		aa = myf_division(uit[i]);
		times_int(-1, aa);
		uit[i + 1]->leading = aa->leading;
		uit[i + 1]->degree = aa->degree;
		free(aa);
#endif
	}
	return(uit);
}

/* Replaces f by f+g. Destroys the contents of g.
 * It could happen that the result has leading term 0. */
void merge_add_split(struct polynomial ***f, struct polynomial **g)
{
	int i, flen, glen;
	struct polynomial **tussen;

	flen = 1 + (*f)[0]->degree/d;
	glen = 1 + g[0]->degree/d;

	if (flen < glen) {
		tussen = *f;
		*f = g;
		g = tussen;
		i = glen;
		glen = flen;
		flen = i;
	}

	for (i = 0; i + 1 <= glen; i++) {
		merge_add((*f)[i + flen - glen], *g[i]);
		free(g[i]);
	}

	return;
}


/* Returns the product.						*
 * Does not modify f or g. 					*
 * The main term ``f[0]*g[0] mod myf'' is NOT zero since	*
 * neither f[0] nor g[0] is divisible by myf.			*/
struct polynomial **mult_split(struct polynomial **f, struct polynomial **g)
{
	int i, j, k, uitlen, flen, glen;
	struct polynomial tmp1, tmp2;
	struct polynomial **uit, **aa;
	tmp1.leading = NULL;
	tmp2.leading = NULL;

	flen = 1 + f[0]->degree/d;
	glen = 1 + g[0]->degree/d;
	uitlen = 1 + (f[0]->degree + g[0]->degree)/d;
	uit = (struct polynomial **)malloc(uitlen*sizeof(struct polynomial *));
	if (!uit) {
		perror("Malloc failed!");
		exit(1);
	}
	for (i = 0; i + 1 <= uitlen; i++) {
		uit[i] = NULL;
		make_pol(&uit[i]);
		uit[i]->degree = f[0]->degree + g[0]->degree - i*d; 
	}
	for (i = 0; i + 1 <= uitlen; i++) {
		tmp2.degree = uit[i]->degree;
		tmp2.leading = NULL;
		j= (glen < i + 1) ? (i + 1 - glen) : 0;
		while ((j <= i) && (j + 1 <= flen)) {
			tmp1 = pol_mult(*f[j], *g[i - j]);
			merge_add(&tmp2, tmp1);
			j++;
		}
		aa = split_up(&tmp2);
		/* The number of terms of aa will be uitlen-i.	*/
		/* We should also free aa again. 		*/
		for (k = 0; k + 1 <= uitlen - i; k++) {
			merge_add(uit[i + k], *aa[k]);
			free(aa[k]);
		}
		free(aa);
	}	
	return(uit);
}


#ifdef KIJKEN
/* Warning: destroys aa! */
void test_split(struct polynomial **aa, struct polynomial orig)
{
	int i, j, aalen;
	struct polynomial tmp;
	tmp.leading = NULL;
	
	if (orig.degree != aa[0]->degree) {
		printf("Wrong degrees! Stop.");
		exit(1);
	}
	
	aalen = 1 + aa[0]->degree/d;
	
	for (i = 1; i + 1 <= aalen; i++) {
		printf(" %d \n", i);
		tmp = pol_mult(myf, *aa[i]);
		free_tail(aa[i]->leading);
		merge_add(aa[0], tmp);
		for (j = i + 1; j + 1 <= aalen; j++) {
			tmp = pol_mult(myf, *aa[j]);
			free_tail(aa[j]->leading);
			*aa[j] = tmp;
		}
	}
	times_int(-1, aa[0]);
	printf("Here is the test result: \n");
	print_pol(pol_add(*aa[0], orig));
	return;
}
#endif
