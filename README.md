## Overview

Code that enumerates all monogenerators of certain quintic number fields.
(A monogenerator of a number field $K$ is an element $\alpha$ such that
$\mathbb Z[\alpha]$ equals the ring of integers of $K$.)
Currently only works for totally real quintic number fields with Galois group $S_5$.

The implemented algorithm is based on Gaál and Györy [1], as presented in Evertse 
and Györy [2].

## Current Status

This code has been tested on the original example in [1], i.e., the number field with polynomial
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

As another example of this code's output, the number field defined by the polynomial
```math
x^5 - x^4 - 10x^3 + x^2 + 10x - 4
```
(discriminant $827397$) has
```math
\frac 52\theta^4 - \frac 12\theta^3 - 26\theta^2 - \frac{35}2\theta + 16
```
as a monogenerator, with minimal polynomial 
```math
x^5 + 5x^4 - 28x^3 + 4x^2 + 10x - 3.
```
The code returns no other monogenerators (up to negation and rational integer shift).

## Known issues

Potential precision issues arising from the use of complex approximations.

## Dependencies

SageMath 3.12.3

## Acknowledgements

I thank Professor Andrew Sutherland, my supervisor for this project, for suggesting the algorithm and for helpful weekly discussions. I also thank the MIT UROP Program for facilitating the wonderful research opportunity, and the Paul E. Grey fund for their generous funding.

## References

[1] I. Gaál and K. Győry, "Index form equations in quintic fields,"
    Acta Arithmetica 89 (1999), no. 4, 379–396.
    https://doi.org/10.4064/aa-89-4-379-396

[2] J.-H. Evertse and K. Győry, Discriminant Equations in Diophantine
    Number Theory, New Mathematical Monographs 32, Cambridge University
    Press, 2017, §7.1.1.