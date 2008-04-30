/*
 *	scalar.c
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
#include "data.h"
#include "scalar.h"

int prime;
scalar *neg_invs;
scalar **sums;
scalar **muls;

/* Only called once. */
void setup_scalars(void )
{
	int i,j;

	if (p <= 0) {
		printf("Primes are positive. Stop.\n");
		exit(1);
	}

	if (neg_invs) {
		free(neg_invs);
		i = 0;
		while (i < prime) {
			free(sums[i]);
			free(muls[i]);
			i++;
		}
		free(sums);
		free(muls);
	}
	
	neg_invs = (scalar *)malloc(p*sizeof(scalar));
	sums = (scalar **)malloc(p*sizeof(scalar *));
	muls = (scalar **)malloc(p*sizeof(scalar *));
	i = 0;
	while (i < p) {
		sums[i] = (scalar *)malloc(p*sizeof(scalar));
		muls[i] = (scalar *)malloc(p*sizeof(scalar));
		i++;
	}

	prime = p;
	i = 1;
	while (i < p) {
		j = 1;
		while ((p-1) != ((i*j) % prime)) j++;
		neg_invs[i] = j;
		i++;
	}
	i = 0;
	while (i < p) {
		j = 0;
		while (j < p) {
			sums[i][j] = (i + j) % p;
			muls[i][j] = (i * j) % p;
			j++;
		}
		i++;
	}
}

void print_scalar(scalar a)
{
	printf("%d", a);
}
