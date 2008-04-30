/*
 *	test_scalars.c
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
#include "helper.h"

int main()
{
	mscalar ma, mb, mc, md, me;
	struct polynomial A, B, C, D, E, F, G, H;
	make_scalar(ma);
	make_scalar(mb);
	make_scalar(mc);
	make_scalar(md);
	make_scalar(me);
	A.leading = NULL;
	B.leading = NULL;
	C.leading = NULL;
	D.leading = NULL;
	E.leading = NULL;
	F.leading = NULL;
	G.leading = NULL;
	H.leading = NULL;

	printf("The prime is: %d.\n", p);
	printf("The power is: %d.\n", r);
	setup_scalars();
	set_seed(0);

	sc_zero(ma);
	printf("The number 0 is: ");
	printmscalar(ma);
	printf(".\n");
	sc_one(mb);
	printf("The number 1 is: ");
	printmscalar(mb);
	printf(".\n");
	ito_sc(541, mc);
	printf("The number 541 is: ");
	printmscalar(mc);
	printf(".\n");
	sc_inv(mc, md);
	printf("The inverse of 541 is: ");
	printmscalar(md);
	printf(".\n");
	sc_mult(md, mc, me);
	printf("The number 1 is: ");
	printmscalar(me);
	printf(".\n");

	A = make_random(10, 0);
	F = copy_pol(A);
/*	print_pol(A);
	printf("\n"); */
	B = make_random(11, 0);
	H = copy_pol(B);
/*	print_pol(B);
	printf("\n"); */
	C = pol_mult(A, B);
/*	print_pol(C);
	printf("\n"); */
	D = pol_mult(B, A);
/*	print_pol(D);
	printf("\n"); */
	times_int(-1, &D);
	E = pol_add(C, D);
	print_pol(E);
	printf("\n");
	times_int(-1, &F);
	G = pol_add(A, F);
	print_pol(G);
	printf("\n");
	times_int(-1, &H);
	G = pol_add(B, H);
	print_pol(G);
	exit(0);
}
