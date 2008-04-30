/*
 *	pol.h
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
void times_scalar(scalar c, struct polynomial *f);
void div_p_pol(int k, struct polynomial *f);
void times_int(int c, struct polynomial *f);
void clean_pol(struct polynomial *pol);
void make_term(struct term **mon);
void make_pol(struct polynomial **f);
void free_term(struct term *mon);

/* This function assumes terms of the same degree. 	*
 * It compares the monomials not the coefficients.	*
 * Returns						*
 * 		GELIJK if equal				*
 * 		KLEINER if mon1 < mon2			*
 * 		GROTER if mon1 > mon2			*
 * 							*/
static inline int kleiner(struct term *mon1, struct term *mon2)
{
#ifdef REVLEX_ORDER
	if(mon1->n4 != mon2->n4) return((mon1->n4 > mon2->n4));
	if(mon1->n3 != mon2->n3) return((mon1->n3 > mon2->n3));
	if(mon1->n2 != mon2->n2) return((mon1->n2 > mon2->n2));
#endif
#ifdef LEX_ORDER
	if(mon1->n1 != mon2->n1) return((mon1->n1 < mon2->n1));
	if(mon1->n2 != mon2->n2) return((mon1->n2 < mon2->n2));
	if(mon1->n3 != mon2->n3) return((mon1->n3 < mon2->n3));
#endif
	return(-1);
}

void copy_term(struct term *mon1, struct term *mon2);
void times_term(struct term t, struct polynomial f, struct polynomial *g);
struct polynomial make_times_term(struct term t, struct polynomial f);
void free_tail(struct term *mon);
void copy_tail(struct term *mon, struct term **ptrterm);
struct polynomial copy_pol(struct polynomial f);
struct polynomial pol_mult(struct polynomial f, struct polynomial g);
struct polynomial pol_add(struct polynomial f, struct polynomial g);
void rep_pol_add(struct polynomial *f, struct polynomial g);
void merge_add(struct polynomial *f, struct polynomial g);
struct polynomial copy_pol(struct polynomial f);
void print_pol(struct polynomial f);
