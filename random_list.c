/*
 *	random_list.c
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

#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>

#include "data.h"
#include "scalar.h"
#include "pol.h"
#include "grobner.h"
#include "helper.h"
#include "compute.h"
#include "delta.h"

/* Makes a random polynomial of degree degree.		*
 * The result may be the zero polynomial!		*/
static struct polynomial make_initial_pol(unsigned int degree, int print)
{
	unsigned int a1, a2, a3, a4;
	int c;
	struct polynomial uit;
	struct term *uitterm;
	struct term **ptrterm;
	uitterm = NULL;
	uit.degree = degree;
	uit.leading = NULL;

	if (!count_sum(degree)) {
		printf("No monomials of degree %d! Stop.\n", degree);
		exit(1);
	}

	for (a1 = 0; (d1*a1 <= degree);a1++) {
	  for (a2 = 0; (d1*a1 + d2*a2 <= degree);a2++) {
	    for (a3 = 0; (d1*a1 + d2*a2 + d3*a3 <= degree);a3++) {
	      if ((degree - (a1*d1 + a2*d2 + a3*d3)) % d4 == 0) {
		a4 = (degree - (a1*d1 + a2*d2 + a3*d3))/d4;
		/* Dummy input at first. */
		c = 1;
		/* Create the new term to be put in. */
		make_term(&uitterm);
		uitterm->n1 = a1;
		uitterm->n2 = a2;
		uitterm->n3 = a3;
		uitterm->n4 = a4;
		uitterm->c = c;
		ptrterm = &(uit.leading);
		while ((*ptrterm) && (kleiner(uitterm, *ptrterm) == KLEINER)) {
			ptrterm = &((*ptrterm)->next);
		}
		uitterm->next = *ptrterm;
		*ptrterm = uitterm;
		uitterm = NULL;
	      }
	    }
	  }
	}
	if (print) {
		uitterm = uit.leading;
		while (uitterm) {
			a1 = uitterm->n1;
			a2 = uitterm->n2;
			a3 = uitterm->n3;
			a4 = uitterm->n4;
			c = 0;
			printf("Coefficient of   ");
			if (a1) {
				printf("x^%d", a1);
				c++;
			}
			if ((a1) && (a2 + a3 + a4)) {
				printf(" * ");
				c++;
			}
			if (a2) {
				printf("y^%d", a2);
				c++;
			}
			if ((a2) && (a3 + a4)) {
				printf(" * ");
				c++;
			}
			if (a3) {
				printf("z^%d", a3);
				c++;
			}
			if ((a3) && (a4)) {
				printf(" * ");
				c++;
			}
			if (a4) {
				printf("w^%d", a4);
				c++;
			}
			while (8 - c) {
				printf("   ");
				c++;
			}
			printf("= ");
			print_scalar(uitterm->c);
			printf("\n");
			uitterm = uitterm->next;
		}
	}
	return(uit);
}

void next_one(unsigned int nr, int *coeff)
{
	int i = 0;

	while (i < nr) {
		coeff[i] = rand() % p;
		i++;
	}
}
	
int main()
{
	unsigned int nr;
	unsigned int good, bad, max, min;
	int i, retry;
	int *coeff;
	struct term *tt;
	struct polynomial uit;
	struct polynomial T;
	T.leading = NULL;
	
#ifdef KIJKEN
	printf("Debug is set! To unset do not define KIJKEN.\n");
#endif
	/* Setup the scalars. */
	setup_scalars();

	set_seed(0);

	uit = make_initial_pol(d, 1);
	nr = number_terms(uit);
	coeff = (int *)malloc(nr*sizeof(int));
	for (i = 0; i + 1 <= nr; i++) {
		coeff[i] = 0;
	}
	retry = 1;
	good = 0;
	bad = 0;
	min = 10000;
	max = 0;
	while (retry == 1) {
		next_one(nr, coeff);
		myf = copy_pol(uit);
		tt = myf.leading;
		i = 0;
		while (tt) {
			tt->c = coeff[i];
			i++;
			tt = tt->next;
		}
		clean_pol(&myf);
		retry = setup(1);

		/* retry == 4 means quasi-smooth */
		if (retry == 4) {
			for (i = 0; i + 1 <= nr; i++) {
				printf("%d ", coeff[i]);
			}
			printf("  %d", G.len);
			if (G.len < min) min = G.len;
			if (G.len > max) max = G.len;
			printf("\n");
			good++;
		} else {
			bad++;
		}

		if (retry >= 0) {
			/* Free up G and myf. */
			free_tail(myf.leading);
			for (i = 0; i + 1 <= G.len; i++) {
				free_tail(G.ff[i]->leading);
			}
		}
		retry = 1;
		if ((good + bad) % 100 == 0) {
			printf("Good = %d, bad = %d, max = %d and min = %d.\n",
					good, bad, max, min);
		}
	}
	
	exit(0);
}
