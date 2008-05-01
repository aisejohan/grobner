/*
 *	helper.h
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

void set_seed(unsigned int zaadje);
unsigned int count_sum(unsigned int degree);
struct polynomial make_random(unsigned int degree, int print);
void rep_deriv(struct polynomial *f, unsigned int i);
struct polynomial deriv(struct polynomial f, unsigned int i);
unsigned int number_terms(struct polynomial f);
struct polynomial frobenius(struct polynomial f);
struct polynomial q_equation(int *n, unsigned int a);
int list_relations(int ***n);
