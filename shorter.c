/*
 *	shorter.c
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
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>

#include "data.h"
#include "scalar.h"
#include "pol.h"
#include "grobner.h"
#include "helper.h"
#include "compute.h"
#include "reduce.h"

/* Variable used outside this file as well. */
struct lijst G;
struct polynomial myf;

/* Note that this produces a segfault or hangs if either	*
 * f.leading is NULL or if f.leading->c == 0.			*/
static struct exponents take_exponents(struct polynomial f)
{
	struct exponents uit;
	uit.e1 = f.leading->n1;
	uit.e2 = f.leading->n2;
	uit.e3 = f.leading->n3;
	uit.e4 = f.leading->n4;
	return(uit);
}

/* Least common multiple.					*/
static struct exponents lcm(struct exponents *mon1, struct exponents *mon2)
{
	struct exponents uit;
	uit.e1 = (mon1->e1 > mon2->e1) ? mon1->e1 : mon2->e1;
	uit.e2 = (mon1->e2 > mon2->e2) ? mon1->e2 : mon2->e2;
	uit.e3 = (mon1->e3 > mon2->e3) ? mon1->e3 : mon2->e3;
	uit.e4 = (mon1->e4 > mon2->e4) ? mon1->e4 : mon2->e4;
	return(uit);
}

/* Rarely the case.							*/
static unsigned int rel_prime(struct exponents mon1, struct exponents mon2)
{
	if ((mon1.e1 > 0) && (mon2.e1 > 0)) return(0);
	if ((mon1.e2 > 0) && (mon2.e2 > 0)) return(0);
	if ((mon1.e3 > 0) && (mon2.e3 > 0)) return(0);
	if ((mon1.e4 > 0) && (mon2.e4 > 0)) return(0);
	return(1);
}

static unsigned int divides(struct exponents *mon1, struct exponents *mon2)
{
	return((mon1->e1 <= mon2->e1) && (mon1->e2 <= mon2->e2) && 
	(mon1->e3 <= mon2->e3) && (mon1->e4 <= mon2->e4));
}

/* Smaller degree means smaller. Otherwise:				*
 * Make sure the ordering on the first 4 is the same as in the 		*
 * function kleiner, and finally if these are the same, then the	*
 * valuation of the coefficients being smaller means smaller.		*/
static unsigned int smaller(struct exponents mon1, struct exponents mon2)
{
	if (d1*mon1.e1 + d2*mon1.e2 + d3*mon1.e3 + d4*mon1.e4 !=
	d1*mon2.e1 + d2*mon2.e2 + d3*mon2.e3 + d4*mon2.e4) return((
		d1*mon1.e1 + d2*mon1.e2 + d3*mon1.e3 + d4*mon1.e4 < 
		d1*mon2.e1 + d2*mon2.e2 + d3*mon2.e3 + d4*mon2.e4));
	/* Same as in kleiner...				*/
#ifdef REVLEX_ORDER
	if (mon1.e4 != mon2.e4) return((mon1.e4 > mon2.e4));
	if (mon1.e3 != mon2.e3) return((mon1.e3 > mon2.e3));
	if (mon1.e2 != mon2.e2) return((mon1.e2 > mon2.e2));
#endif
#ifdef LEX_ORDER
	if (mon1.e1 != mon2.e1) return((mon1.e1 < mon2.e1));
	if (mon1.e2 != mon2.e2) return((mon1.e2 < mon2.e2));
	if (mon1.e3 != mon2.e3) return((mon1.e3 < mon2.e3));
#endif
	/* Means equal so not smaller. 				*/
	return(0);
}

/* Computes the coefficient terms needed to make the s_pol.	*/
static void s_pol_terms(struct term *a, struct term *b, struct term *fterm, struct term *gterm)
{
	if (fterm->n1 > gterm->n1) {
		a->n1 = 0;
		b->n1 = fterm->n1 - gterm->n1;
	} else {
		a->n1 = gterm->n1 - fterm->n1;
		b->n1 = 0;
	}
	if (fterm->n2 > gterm->n2) {
		a->n2 = 0;
		b->n2 = fterm->n2 - gterm->n2;
	} else {
		a->n2 = gterm->n2 - fterm->n2;
		b->n2 = 0;
	}
	if (fterm->n3 > gterm->n3) {
		a->n3 = 0;
		b->n3 = fterm->n3 - gterm->n3;
	} else {
		a->n3 = gterm->n3 - fterm->n3;
		b->n3 = 0;
	}
	if (fterm->n4 > gterm->n4) {
		a->n4 = 0;
		b->n4 = fterm->n4 - gterm->n4;
	} else {
		a->n4 = gterm->n4 - fterm->n4;
		b->n4 = 0;
	}
	a->c = gterm->c;
	b->c = fterm->c;
	/* Note sign. */
	b->c = prime - b->c;
	return;
}

/* Computes the s_pol.						*/
static struct polynomial s_pol(struct polynomial f, struct polynomial g)
{
	struct term a, b;
	struct polynomial A, B;
	A.leading = NULL;
	B.leading = NULL;

	s_pol_terms(&a, &b, f.leading, g.leading);
	A = make_times_term(a, f);
	clean_pol(&A);
	B = make_times_term(b, g);
	merge_add(&A, B);
	return(A);
}

/* Outputs G.							*/
static unsigned int print_G(void)
{
	int i, s1 = 0, s2 = 0, s3 = 0, s4 = 0, success;
	struct exponents tmp;

	for (i = 0; i + 1 <= G.len; i++) {
		tmp = *G.ee[i];
		printf("[%d, %d, %d, %d]  \t",
			tmp.e1, tmp.e2, tmp.e3, tmp.e4);
		printf("%d\t", d1*tmp.e1 + d2*tmp.e2 + d3*tmp.e3 + d4*tmp.e4);
		printf("%d ", number_terms(*G.ff[i]));
		if (tmp.e1 + tmp.e2 + tmp.e3 == 0) {
			printf(" <--- 4");
			s4 = 1;
		}
		if (tmp.e1 + tmp.e2 + tmp.e4 == 0) {
			printf(" <--- 3");
			s3 = 1;
		}
		if (tmp.e1 + tmp.e3 + tmp.e4 == 0) {
			printf(" <--- 2");
			s2 = 1;
		}
		if (tmp.e2 + tmp.e3 + tmp.e4 == 0) {
			printf(" <--- 1");
			s1 = 1;
		}
#ifdef KIJKEN
		if (
		(tmp.e1 != G.ff[i]->leading->n1) ||
		(tmp.e2 != G.ff[i]->leading->n2) ||
		(tmp.e3 != G.ff[i]->leading->n3) ||
		(tmp.e4 != G.ff[i]->leading->n4)) {
			printf("Wrong exponents!\n");
			exit(1);
		}
#endif
		printf("\n");
	}
	success = s1 + s2 + s3 + s4;
	return(success);
}

static unsigned int test_G(void)
{
	int i, s1 = 0, s2 = 0, s3 = 0, s4 = 0, success;
	struct exponents tmp;

	for (i = 0; i + 1 <= G.len; i++) {
		tmp = *G.ee[i];
		if (tmp.e1 + tmp.e2 + tmp.e3 == 0) s4 = 1;
		if (tmp.e1 + tmp.e2 + tmp.e4 == 0) s3 = 1;
		if (tmp.e1 + tmp.e3 + tmp.e4 == 0) s2 = 1;
		if (tmp.e2 + tmp.e3 + tmp.e4 == 0) s1 = 1;
#ifdef KIJKEN
		if (
		(tmp.e1 != G.ff[i]->leading->n1) ||
		(tmp.e2 != G.ff[i]->leading->n2) || 
		(tmp.e3 != G.ff[i]->leading->n3) || 
		(tmp.e4 != G.ff[i]->leading->n4)) {
			printf("Wrong exponents!\n");
			exit(1);
		}
#endif
	}
	success = s1 + s2 + s3 + s4;
	return(success);
}

/* Silly sort should be OK since the length of G is at most maxlength.	*
 * We sort the basis so that all the elements with high power of p	*
 * in the leading coefficient come last.				*/
static void sort_G(void)
{
	int i, j;
	struct exponents *s_ee;
	struct polynomial *s_ff;

	for (i = 0; i+1 <= G.len; i++) {
		for (j = i+1; j+1 <= G.len; j++) {
			if ((((*G.ff[j]).degree < (*G.ff[i]).degree))
			|| ((((*G.ff[j]).degree == (*G.ff[i]).degree)) &&
			(smaller(*G.ee[i], *G.ee[j])))) {
				s_ee = G.ee[i];
				s_ff = G.ff[i];
				G.ee[i] = G.ee[j];
				G.ff[i] = G.ff[j];
				G.ee[j] = s_ee;
				G.ff[j] = s_ff;
			}
		}
	}
}

static void check_sort_G(void)
{
	int i, j;

	for (i = 0; i+1 <= G.len; i++) {
		for (j = i+1; j+1 <= G.len; j++) {
			if ((((*G.ff[j]).degree < (*G.ff[i]).degree))
			|| ((((*G.ff[j]).degree == (*G.ff[i]).degree)) &&
			(smaller(*G.ee[i], *G.ee[j])))) {
				printf("not sorted.\n");
			}
		}
	}
}


/* Only does the right thing on a sorted G. */
static void reduce_G(void)
{
	int i, j;

	i = 1;
	while (i + 1 <= G.len) {
		gen_division(G.ff[i], i, G.ff);
		if (!(*G.ff[i]).leading) {
			j = i;
			while (j + 1 < G.len) {
				G.ff[j] = G.ff[j + 1];
				j++;
			}
			G.len--;
		} else {
			*G.ee[i] = take_exponents(*G.ff[i]);
			i++;
		}
	}
}

int setup(int silent)
{
	int i, j, k, ii, jj, old, new, check, epsilon, lG, dSS;
#ifndef TEST
	struct polynomial myf1, myf2, myf3, myf4;
#else
	int **n;
#endif
	struct polynomial SS, T;
	struct polynomial *Tff, *pff;
	struct exponents *Tee, *pee, ee;
	struct polynomial **bb;
	unsigned int m, mold, mnew;
	struct exponents lcm_new, lcm_old;
	SS.leading = NULL;
	T.leading = NULL;

#ifndef TEST
	/* Initialize myf,myf1,myf2,myf3,myf4 */
	if (!silent) {
		printf("\n\n");
		myf = make_random(d, 1);
		printf("\n");
		printf("Here is the polynomial we're using this time:\n");
		printf("\n");
		print_pol(myf);
	}
	if (!myf.leading) {
		if (!silent) printf("Polynomial is zero!\n");
		return(-1);
	}
	if (!silent) printf("\n");
	
	myf1 = deriv(myf, 1);
	if (!myf1.leading) {
		if (!silent) printf("Polynomial does not depend on x!\n");
		free_tail(myf.leading);
		return(-1);
	}
	myf2 = deriv(myf, 2);
	if (!myf2.leading) {
		if (!silent) printf("Polynomial does not depend on y!\n");
		free_tail(myf.leading);
		free_tail(myf1.leading);
		return(-1);
	}
	myf3 = deriv(myf, 3);
	if (!myf3.leading) {
		if (!silent) printf("Polynomial does not depend on z!\n");
		free_tail(myf.leading);
		free_tail(myf1.leading);
		free_tail(myf2.leading);
		return(-1);
	}
	myf4 = deriv(myf, 4);
	if (!myf4.leading) {
		if (!silent) printf("Polynomial does not depend on w!\n");
		free_tail(myf.leading);
		free_tail(myf1.leading);
		free_tail(myf2.leading);
		free_tail(myf3.leading);
		return(-1);
	}
	if (!silent) printf("\n");
#endif

	/* Allocate memory for G */
	lG = 20*maxlength;
	G.ff = (struct polynomial **)
			malloc(lG*sizeof(struct polynomial *));
	if (!G.ff) {
		perror("Malloc failed!");
		exit(1);
	}
	G.ee = (struct exponents **)
			malloc(lG*sizeof(struct exponents *));
	if (!G.ee) {
		perror("Malloc failed!");
		exit(1);
	}
	for (i = 0; i + 1 <= lG; i++) {
		G.ff[i] = NULL;
		make_pol(&G.ff[i]);
		G.ee[i] = (struct exponents *)
				malloc(sizeof(struct exponents));
		if (!G.ee[i]) {
			perror("Malloc failed!");
			exit(1);
		}
	}

#ifndef TEST
	/* Initialize G */
	*G.ff[0] = copy_pol(myf4);
	*G.ee[0] = take_exponents(myf4);
	*G.ff[1] = copy_pol(myf3);
	*G.ee[1] = take_exponents(myf3);
	*G.ff[2] = copy_pol(myf2);
	*G.ee[2] = take_exponents(myf2);
	*G.ff[3] = copy_pol(myf1);
	*G.ee[3] = take_exponents(myf1);
	*G.ff[4] = copy_pol(myf);
	*G.ee[4] = take_exponents(myf);
	G.len = 5;
#else
	i = list_relations(&n);
	j = 0;
	while (j < i) {
		*G.ff[j] = q_equation(n[j], 4);
		*G.ee[j] = take_exponents(*G.ff[j]);
		j++;
	}
	*G.ff[i] = make_random(d, 0);
	*G.ee[i] = take_exponents(*G.ff[i]);
	i++;
	*G.ff[i] = make_random(2*d, 0);
	*G.ee[i] = take_exponents(*G.ff[i]);
	i++;
	G.len = i;
	print_G();
#endif

	sort_G();
	reduce_G();
	sort_G();
	check_sort_G();

	/* Loop for computing the Grobner basis.	*
	 * Needlessly complicated.			*/
	ii = 0;
	jj = 1;
	while (jj < G.len) {
		/* Make S-pol. */
		if (rel_prime(*G.ee[ii], *G.ee[jj])) {
			SS.leading = NULL;
		} else {
			SS = s_pol(*G.ff[ii], *G.ff[jj]);
		}
		if (SS.leading) gen_division(&SS, G.len - 1, G.ff);
		if (SS.leading) {
			G.len++;		
			if (G.len > lG) {
				printf("Please increase maxlength.\n");
				free_tail(SS.leading);
				for (i = 0; i + 1 + 1 <= G.len; i++) {
					free_tail(G.ff[i]->leading);
				}
				for (i = 0; i + 1 <= lG; i++) {
					free(G.ff[i]);
					free(G.ee[i]);
				}
				free(G.ff);
				free(G.ee);
#ifndef TEST
				free_tail(myf.leading);
				free_tail(myf1.leading);
				free_tail(myf2.leading);
				free_tail(myf3.leading);
				free_tail(myf4.leading);
#endif
				return(-1);
			}
			check = 2; /* success. */
		} else {
			free_tail(SS.leading);
			check = 0;
		}
		if (check == 2) {
			check = 0;
			/* Already increased G.len so have to substract
			 * one here. */
			ee = take_exponents(SS);
			dSS = SS.degree;
			i = 0;
			j = 1;
			while (j) {
				if (i + 1 == G.len) {
					j = 0;
				} else if ((dSS < (*G.ff[i]).degree) ||
				((dSS == (*G.ff[i]).degree) &&
					(smaller(*G.ee[i], ee)))) {
					j = 0;
				} else {
					i++;
				}
			}
			j = G.len - 1;
			while (j > i) {
				*G.ff[j] = *G.ff[j - 1];
				*G.ee[j] = *G.ee[j - 1];
				j--;
			}
			*G.ff[i] = SS;
			*G.ee[i] = ee; /* Done updating G. */
		}
		if (ii + 1 < jj) {
			ii++;
		} else {
			jj++;
			i = 1;
			ii = 0;
			while ((jj < G.len) && (i)) {
				gen_division(G.ff[jj], jj, G.ff);
				if (!(*G.ff[jj]).leading) {
					j = jj;
					while (j + 1 < G.len) {
						*G.ff[j] = *G.ff[j + 1];
						*G.ee[j] = *G.ee[j + 1];
						j++;
					}
					G.len--;
				} else {
					i = 0;
					j = jj;
					while (
						(j + 1 < G.len)
					&&
					 (
					  (
						( (*G.ff[j + 1]).degree <
							(*G.ff[j]).degree )
					 
					  ||
					   (
						( (*G.ff[j + 1]).degree ==
						(*G.ff[j]).degree )
					
					   &&
						(smaller(*G.ee[j],
							*G.ee[j + 1]))
					   )
					  )
					 )
					) {
						pee = G.ee[j];
						pff = G.ff[j];
						G.ee[j] = G.ee[j + 1];
						G.ff[j] = G.ff[j + 1];
						G.ee[j + 1] = pee;
						G.ff[j + 1] = pff;
						j++;
						/* jj-th spot has change
						 * so do it all again.*/
						i = 1;
					}

				}
			}
			if (jj < G.len) *G.ee[jj] = take_exponents(*G.ff[jj]);
		}
	}/* End loop computing Grobner basis. */

#ifdef KIJKEN
	printf("The initial length of G is %d.\n", G.len);
	print_G();
	printf("\n");
#endif
	
	/* Weed out G. 						*
	 * Do not need to update M,m,V since they are no	*
	 * longer used.						*
	 * Below we order the elements of G.			*/
	old = G.len; /* Remember for freeing bb later. */
	bb = (struct polynomial **)malloc(G.len*sizeof(struct polynomial *));
	if (!bb) {
		perror("Malloc failed!");
		exit(1);
	}
	for (i = 0; i + 1 <= G.len; i++) {
		bb[i] = NULL;
		make_pol(&bb[i]);
	}
	i = 0;
	while (i + 1 <= G.len) {
		for (j = 0; j + 1 <= G.len; j++) {
			if (j != i) {
				epsilon = (j>i) ? 1 : 0;
				bb[j-epsilon]->degree = G.ff[j]->degree;
				bb[j-epsilon]->leading = G.ff[j]->leading;
			}
		}
		
		new = G.len - 1; /* Remember for freeing aa later. */
		gen_division(G.ff[i], G.len - 1, bb);

#ifdef KIJKEN
		if ((G.ff[i]->leading) && 
		((G.ff[i]->leading->n1 != G.ee[i]->e1) || 
		 (G.ff[i]->leading->n2 != G.ee[i]->e2) || 
		 (G.ff[i]->leading->n3 != G.ee[i]->e3) || 
		 (G.ff[i]->leading->n4 != G.ee[i]->e4))) {
			printf("The following should have been zero: ");
			print_pol(*G.ff[i]);
			exit(1);
		}
#endif
		
		/* Either omit G[i] or replace it. */
		if (!G.ff[i]->leading) {
			Tff = G.ff[i];
			Tee = G.ee[i];
			for (j = i; j + 1 + 1 <= G.len; j++) {
				G.ff[j] = G.ff[j + 1];
				G.ee[j] = G.ee[j + 1];
			}
			G.ff[G.len - 1] = Tff;
			G.ee[G.len - 1] = Tee;
			G.len--;
		} else {
			/* This should not be necessary. */
			*G.ee[i] = take_exponents(*G.ff[i]); 
			/* Only in this case do we update i! */
			i++;
		}

	}
	
	/* Free bb. */
	for (j = 0; j + 1 <= old; j++) {
		bb[j]->leading = NULL;
		free(bb[j]);
	}
	free(bb);

	sort_G();

	if (!silent) {
		printf("The final length of G is %d\n", G.len);
		print_G();
		printf("------\n");
	}

#ifdef KIJKEN
	/* Recheck all S-pols reduce to zero! */
	printf("Checking S-pols.\n");
	for (i = 0; i <= G.len - 1; i++) {
		printf("Doing %d out of %d.\n", i+1, G.len);
		for (j = i + 1; j <= G.len - 1; j++) {
			SS = s_pol(*G.ff[i], *G.ff[j]);
			if (zero_on_division(SS, G.len, G.ff)) {
				free_tail(SS.leading);
			} else {
				printf("Not OK at the following"
				" indices: %d and %d\n", i, j);
				print_pol(*G.ff[i]);
				printf("\n");
				print_pol(*G.ff[j]);
				printf("\n");
				print_pol(SS);
				exit(1);
			}
		}
	}
#endif /* KIJKEN */

	/* Success. */
#ifndef TEST
	free_tail(myf1.leading);
	free_tail(myf2.leading);
	free_tail(myf3.leading);
	free_tail(myf4.leading);
#endif
	return(test_G());
}
