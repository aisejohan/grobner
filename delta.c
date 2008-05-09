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

/* This functions checks the number of left over monomials in degree	*
 * degree and compares it to what you would have gotten in char 0.	*/
int check_flatness(unsigned int degree)
{
	int i, b1, b2;
	int count, goodcount;
	unsigned int a1, a2, a3, a4;
	struct term tmp, least;
	struct polynomial T, TT;
	tmp.next = NULL;
	least.next = NULL;
	T.leading = NULL;
	TT.leading = NULL;
	
	count = 0;
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
		if (!b1) count++;
	      }
	    }
	  }
	}
	if (count != goodcount) {
		printf("Here we have degree %d, count %d"
		", and goodcount %d\n",
		degree, count, goodcount);
	}
	return(count);
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
