/*
 *	grobner.c
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
#include "compute.h"

/* Generic routines... */

/* This function tests for divisibility of terms.	*/
static inline int deelbaar(struct term *mon1, struct term *mon2)
{
	return(((mon1->n1 <= mon2->n1) &&
		(mon1->n2 <= mon2->n2) &&
		(mon1->n3 <= mon2->n3) &&
		(mon1->n4 <= mon2->n4)));
}


/****************************************************************
 * Really insane and screwed up. Removes all monomials it can.	*
 * The remainder ends up in pp.					*
 * The coefficients aa[i] will be returned, so that		*
 *								*
 *	(input pp) + sum_{i=0,ss-1} aa[i] * vh[i]		*
 *								*
 *		=						*
 *								*
 *	(output pp)						*
 *								*
 * **************************************************************/
#if defined OLD_GROBNER || defined MIXED_GROBNER
void 
gen_division(struct polynomial *pp, unsigned int ss, struct polynomial **vh)
{
	struct polynomial tmp;
	struct polynomial vh_rest[ss];
	struct polynomial *ppp;
	struct term **ptrterm;
	struct term *pppterm;
	struct term mon;
	unsigned int i, dividing;

	ppp = NULL;
	tmp.leading = NULL;
	make_pol(&ppp);
	for (i = 0; i + 1 <= ss; i++) {
		vh_rest[i].leading = vh[i]->leading->next;
		vh_rest[i].degree = vh[i]->degree;
	}

	/* Copy pp into ppp. */
	ppp->degree = pp->degree;
	ppp->leading = pp->leading;
	/* Set pp equal to ``zero'' */
	pp->leading = NULL;
	ptrterm = &pp->leading;

	while (ppp->leading) {
		i = 0;
		dividing = 1;
		while (i + 1 <= ss && dividing) {
			if (deelbaar(vh[i]->leading, ppp->leading)) {
				/* No sign in front of pppterm->c */
				/* Change sign mon.c */
				mon.c = sc_neg_inv(vh[i]->leading->c);
				mon.c = sc_mul(mon.c, ppp->leading->c);
				mon.n1 = ppp->leading->n1 - vh[i]->leading->n1;
				mon.n2 = ppp->leading->n2 - vh[i]->leading->n2;
				mon.n3 = ppp->leading->n3 - vh[i]->leading->n3;
				mon.n4 = ppp->leading->n4 - vh[i]->leading->n4;

				pppterm = ppp->leading;
				ppp->leading = ppp->leading->next;
				free_term(pppterm);

				tmp = make_times_term(mon, vh_rest[i]);
				merge_add(ppp, tmp);

				dividing = 0;
			} else {
				i = i + 1;
			}
		}
		/* dividing == 1 means that we cannot get rid of the leading
		 * term. So we put it back in pp. */
		if (dividing) {
			*ptrterm = ppp->leading;
			ptrterm = &((*ptrterm)->next);
			/* Move on to the next one. */
			ppp->leading = ppp->leading->next;
			/* Terminate pp. */
			*ptrterm = NULL;
		}
	}
	free(ppp);
}
#endif


#ifdef NEW_GROBNER
void
gen_division(struct polynomial *pp, unsigned int ss, struct polynomial **vh)
{
	struct polynomial save_the_spot, uit;
	struct term test;
	struct polynomial vh_rest[ss];
	struct polynomial *ppp;
	struct term **save;
	struct term **ptrterm;
	unsigned int i, first;
	scalar c;

	ppp = NULL;
	make_pol(&ppp);
	for (i = 0; i+1 <= ss; i++) {
		vh_rest[i].degree = vh[i]->degree;
		vh_rest[i].leading = vh[i]->leading->next;
	}

	/* Copy pp into ppp. */
	ppp->degree = pp->degree;
	ppp->leading = pp->leading;
	/* Set pp equal to ``zero'' */
	pp->leading = NULL;
	ptrterm = &pp->leading;

	i = 0;
	while ((ppp->leading) && (i + 1 <= ss)) {

		if (deelbaar(vh[i]->leading, ppp->leading)) {

			save_the_spot.degree = ppp->degree - vh[i]->degree;
			save_the_spot.leading = ppp->leading;
			save = &(save_the_spot.leading);
			first = 1;

			do {
				/* No sign in front of c */
				/* Change sign c */
				c = sc_neg_inv(vh[i]->leading->c);
				c = sc_mul(c, ppp->leading->c);

				*save = ppp->leading;

				ppp->leading->n1 -= vh[i]->leading->n1;
				ppp->leading->n2 -= vh[i]->leading->n2;
				ppp->leading->n3 -= vh[i]->leading->n3;
				ppp->leading->n4 -= vh[i]->leading->n4;
				ppp->leading->c = c;

				ppp->leading = ppp->leading->next;
				(*save)->next = NULL;

				if ((first) && (vh_rest[i].leading)) {
					test.n1 = (*save)->n1 + 
						vh_rest[i].leading->n1;
					test.n2 = (*save)->n2 +
						vh_rest[i].leading->n2;
					test.n3 = (*save)->n3 +
						vh_rest[i].leading->n3;
					test.n4 = (*save)->n4 +
						vh_rest[i].leading->n4;
					first = 0;
				}

				save= &((*save)->next);

			} while ((ppp->leading) &&
				deelbaar(vh[i]->leading, ppp->leading) &&
				((!vh_rest[i].leading) ||
				(GROTER == kleiner(ppp->leading, &test))));

			uit = pol_mult(save_the_spot, vh_rest[i]);
			free_tail(save_the_spot.leading);
			merge_add(ppp, uit);

			i = 0;

		} else if (i + 1 == ss) {
			*ptrterm = ppp->leading;
			ptrterm = &((*ptrterm)->next);
			/* Move on to the next one. */
			ppp->leading = ppp->leading->next;
			/* Terminate pp. */
			*ptrterm = NULL;
			i = 0;
		} else {
			i = i + 1;
		}
	}

	free(ppp);
}
#endif

/* ppp does not get changed */
unsigned int
zero_on_division(struct polynomial ppp, unsigned int ss, struct polynomial **vh)
{
	struct polynomial tmp[ss];
	struct term mon;
	struct polynomial pp;
	unsigned int i, dividing, uit;
	pp.leading = NULL;
	for (i = 0; i + 1 <= ss; i++) {
		tmp[i].leading = NULL;
	}

	pp.degree = ppp.degree;
	copy_tail(ppp.leading,&(pp.leading));
	while (pp.leading) {
		i = 0;
		dividing = 1;
		while ((i + 1<=ss) && dividing) {
			if (deelbaar(vh[i]->leading, pp.leading)) {
				/* No sign in front of ppterm->c */
				/* Change sign mon.c */
				mon.c = sc_neg_inv(vh[i]->leading->c);
				mon.c = sc_mul(mon.c, pp.leading->c);
				mon.n1 = pp.leading->n1 - vh[i]->leading->n1;
				mon.n2 = pp.leading->n2 - vh[i]->leading->n2;
				mon.n3 = pp.leading->n3 - vh[i]->leading->n3;
				mon.n4 = pp.leading->n4 - vh[i]->leading->n4;
				if (tmp[i].leading) {
					times_term(mon, *(vh[i]), &(tmp[i]));
				} else {
					tmp[i] = make_times_term(mon, *(vh[i]));
				}
				rep_pol_add(&pp, tmp[i]);
				dividing = 0;
			} else {
				i = i + 1;
			}
		}
		if (dividing) {
			uit = 0;
			goto out;
		}
	}
	uit = 1;

out:
	for (i = 0; i + 1 <= ss; i++) {
		free_tail(tmp[i].leading);
	}
	free_tail(pp.leading);
	return(uit);
}
