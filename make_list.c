/*
 *	make_list.c
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
#include "reduce.h"

/* External variables. */
static int blen1, blen2, blen3;


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
		ito_sc(c, uitterm->c);
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
			printmscalar(uitterm->c);
			printf("\n");
			uitterm = uitterm->next;
		}
	}
	return(uit);
}

void next_one(unsigned int nr, int *coeff)
{
	int i=0;

	while ((coeff[i] == p-1) && (i < nr)) i++;
	if (i == nr) exit(0);
	coeff[i]++;
	while (i > 0) {
		i--;
		coeff[i] = 0;
	}
}
	

int __mm(int e, int i, int c)
{
	int j;

	j = e;
	while (j > 0) {
		c = (c*i) % p;
		j--;
	}
	return(c);
}

int mm(int e1, int e2, int e3, int e4, int i1, int i2, int i3, int i4, int c)
{
	c = __mm(e1, i1, c);
	c = __mm(e2, i2, c);
	c = __mm(e3, i3, c);
	c = __mm(e4, i4, c);

	return(c);
}

int is_square(int c)
{
	int j = 1;

	c = c % p;
	while (j < p) {
		if (c == ((j*j) % p)) return(1);
		j++;
	}
	return(0);
}

int is_min(unsigned int nr, int *coeff, struct polynomial f)
{
	int i, i1, i2, i3, i4, t, different;
	struct term *tt;

	i1 = 1;
	while (i1 < p) {
	  i2 = 1;
	  while (i2 < p) {
	    i3 = 1;
	    while (i3 < p) {
	      i4 = 1;
	      while (i4 < p) {
		tt = f.leading;
		different = 0;
		i = 0;
		do {
			t = mm(tt->n1, tt->n2, tt->n3, tt->n4,
				i1, i2, i3, i4, coeff[i]);
			if (t != coeff[i]) {
				 different = (t < coeff[i]) - (t > coeff[i]);
			}
			i++;
			tt = tt->next;
		} while (tt);
		if (different > 0) return(0);
		i4++;
	      }
	      i3++;
	    }
	    i2++;
	  }
	  i1++;
	}

	return(1);
}

int main()
{
	unsigned int nr;
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

	uit = make_initial_pol(d, 1);
	nr = number_terms(uit);
	coeff = (int *)malloc(nr*sizeof(int));
	for (i = 0; i + 1 <= nr; i++) {
		coeff[i] = 0;
	}
	retry = 1;
	while (retry == 1) {
		while (retry == 1) {
			next_one(nr, coeff);
			if (is_min(nr, coeff, uit)) {
				myf = copy_pol(uit);
				tt = myf.leading;
				i=0;
				while (tt) {
					ito_sc(coeff[i], tt->c);
					i++;
					tt = tt->next;
				}
				clean_pol(&myf);
				retry = setup(1);
			}
		}

		if (d >= d1 + d2 + d3 + d4) {
			blen1 = check_flatness(d - d1 - d2 - d3 - d4);
			if (blen1 <= 0) {
				retry = 1;
				/* Free up G and myf. */
				free_tail(myf.leading);
				for (i = 0; i + 1 <= G.len; i++) {
					free_tail(G.BC[i]->bc1.leading);
					free_tail(G.BC[i]->bc2.leading);
					free_tail(G.BC[i]->bc3.leading);
					free_tail(G.BC[i]->bc4.leading);
					free_tail(G.BC[i]->bc5.leading);
					free_tail(G.ff[i]->leading);
				}
				for (i = 0; i + 1 <= maxlength; i++) {
					free(G.BC[i]);
					free(G.ff[i]);
					free(G.ee[i]);
				}
				free(G.BC);
				free(G.ff);
				free(G.ee);
			}
		}
		if ((retry == 0) && (2*d >= d1 + d2 + d3 + d4)) {
			blen2 = check_flatness(2*d - d1 - d2 - d3 - d4);
			if (blen2 <= 0) {
				retry = 1;
				/* Free up G and myf. */
				free_tail(myf.leading);
				for (i = 0; i + 1 <= G.len; i++) {
					free_tail(G.BC[i]->bc1.leading);
					free_tail(G.BC[i]->bc2.leading);
					free_tail(G.BC[i]->bc3.leading);
					free_tail(G.BC[i]->bc4.leading);
					free_tail(G.BC[i]->bc5.leading);
					free_tail(G.ff[i]->leading);
				}
				for (i = 0; i + 1 <= maxlength;i++) {
					free(G.BC[i]);
					free(G.ff[i]);
					free(G.ee[i]);
				}
				free(G.BC);
				free(G.ff);
				free(G.ee);
			}
		}
		if ((retry == 0) && (3*d >= d1 + d2 + d3 + d4)) { 
			blen3 = check_flatness(3*d - d1 - d2 - d3 - d4);
			if (blen3 > 0) {
				for (i = 0; i + 1 <= nr; i++) {
					printf("%d ", coeff[i]);
				}
				printf("  %d", G.len);
				printf("\n");
			}

			retry = 1;
			/* Free up G and myf. */
			free_tail(myf.leading);
			for (i = 0; i + 1 <= G.len; i++) {
				free_tail(G.BC[i]->bc1.leading);
				free_tail(G.BC[i]->bc2.leading);
				free_tail(G.BC[i]->bc3.leading);
				free_tail(G.BC[i]->bc4.leading);
				free_tail(G.BC[i]->bc5.leading);
				free_tail(G.ff[i]->leading);
			}
			for (i = 0; i + 1 <= maxlength; i++) {
				free(G.BC[i]);
				free(G.ff[i]);
				free(G.ee[i]);
			}
			free(G.BC);
			free(G.ff);
			free(G.ee);
		}
	}
	
	exit(13);
}
