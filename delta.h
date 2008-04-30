/*
 *	delta.h
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
struct polynomial compute_delta(void);
struct polynomial **split_up(struct polynomial *f);
void test_split(struct polynomial **aa, struct polynomial orig);
void merge_add_split(struct polynomial ***f, struct polynomial **g);
struct polynomial **mult_split(struct polynomial **f, struct polynomial **g);
int check_flatness(unsigned int degree);
struct term **find_basis(unsigned int degree, int blen);
void free_star(struct polynomial **bb);
struct polynomial **copy_pol_star(mscalar c, struct polynomial **bb);
