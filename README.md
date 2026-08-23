## Overview

Code that enumerates all monogenerators of certain quintic number fields.
(A monogenerator of a number field $K$ is an element $\alpha$ such that
$\mathbb Z[alpha]$ equals the ring of integers of $K$.)
Currently only works for totally real quintic number fields with Galois group $S_5$.

The implemented algorithm is based on Gaál and Györy [1], as presented in Evertse 
and Györy [2].

## Current Status

This code is work in progress, and I would describe the fact that it even works at
all as nothing short of a miracle.

Has been tested on the original example in [1], i.e., the number field with polynomial
```math
x^5 - 5x^3 + x^2 + 3x - 1,
```
and was able to enumerate all 39 monogenerators.

Also tested on the following polynomial:
```math
x^5 - 10x^4 + 29x^3 - 28x^2 + 6x + 1,
```
which defines the same number field, but the defining generator generates a power basis
of index 13 instead of 1.

Oh, and as proof that this code works, the number field defined by the polynomial
```math
x^5 - x^4 - 7x^3 + 4x^2 + 6x + 1
```
(discriminant $242773$) has
```math
-\frac{43}2\theta^4 - 8\theta^3 + \frac{279}2\theta^2 + \frac{211}2\theta + \frac{31}2
```
as a monogenerator, with minimal polynomial 
```math
x^5 - 325x^4 - 330x^3 - 118x^2 - 18x - 1.
```
(There are also nicer-looking monogenerators.)

## Known issues

Complex approximations are used throughout instead of working with number fields,
leading to potential precision issues.

Not particularly readable.

Past issues which are currently being tested:

Enumerating elements of a given norm in a number field can stall indefinitely
with the current implementation.

PARI stack size overflows.

Division-by-zero errors while sieving.

## Dependencies

SageMath 3.12.3

## References

[1] I. Gaál and K. Győry, "Index form equations in quintic fields,"
    Acta Arithmetica 89 (1999), no. 4, 379–396.
    https://doi.org/10.4064/aa-89-4-379-396

[2] J.-H. Evertse and K. Győry, Discriminant Equations in Diophantine
    Number Theory, New Mathematical Monographs 32, Cambridge University
    Press, 2017, §7.1.1.