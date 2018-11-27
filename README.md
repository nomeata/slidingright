Haskell code related to “Sliding Right”
=======================================

In 2017, I had the pleasure to be among the authors of *Sliding right into
disaster: Left-to-right sliding windows leak* by Daniel J. Bernstein, Joachim
Breitner, Daniel Genkin, Leon Groot Bruinderink, Nadia Heninger, Tanja Lange,
Christine van Vredendaal and Yuval Yarom, published at [CHES 2017] and on
[ePrint].

[CHES 2017]: https://link.springer.com/chapter/10.1007%2F978-3-319-66787-4_27
[ePrint]: https://eprint.iacr.org/2017/627

This repository contains the Haskell code that I wrote to that end, which,
among other things, can:

 * run the key recovery on simulated inputs with varying parameters (key size,
   percentage of leaked bits), and print the result, or the tree sizes
 * calculate entropy rates (Shannon and Renyi) by simulation, or using a direct
   calculation, both for left-to-righ and right-to-left exponentation,
 * sanity-check that the complete algorithm for recovering known (“hard”) bits
   is indeed complete,
 * generate some of the plots and tables from the paper

The code compiles with GHC-8.0, and has not been updated since. The two
programs have understand `--help`, but there is no more documentation. If you
have an interest in running or understanding these programs, please [contact
me](mailto:mail@joachim-breitner.de).

The details of these calculations did not make it into the full paper, so I
published an [“inoffical appendix” on ePrint](https://eprint.iacr.org/TODO).

It turned out that the direct calculation of the Renyi entropy was novel, and a
dedicated paper by Maciej Skorski and me, [*Analytic Formulas for Renyi Entropy
of Hidden Markov Models*](https://arxiv.org/abs/1709.09699), elaborates on that
aspect.

None of my coauthors should be held responsible for anything found in this
repository.
