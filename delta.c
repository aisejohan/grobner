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
	int i, b1, b2;
	int count, count1, goodcount;
	unsigned int a1, a2, a3, a4;
	struct term tmp, least;
	struct polynomial T, TT;
	tmp.next = NULL;
	least.next = NULL;
	T.leading = NULL;
	TT.leading = NULL;
	
	if (!count_sum(degree)) {
		return(0);
	}
	count = 0;
	count1 = 0;
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
			}
		}
		if (!b1) count1++;
	      }
	    }
	  }
	}
	if (count1 != goodcount) {
		printf("Here we have degree %d, count1 %d"
		", and goodcount %d\n",
		degree, count1, goodcount);
	}
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
	tmp.c = 1;
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
				b2 = 1;
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
	return(tt);
}


