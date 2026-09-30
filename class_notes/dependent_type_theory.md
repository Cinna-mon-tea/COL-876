## 1910s/20s
### Alonzo Church
lambda calculus $x, \lambda x \cdot t, t$ $u$

### Alan Turing
Turing machine

**Church-Turing hypothesis:** Lambda Calculus $\equiv$ Turing Machine

Hypothesis because not formal definition of all computable functions

### Gerhard Gentzen
Natural Deduction

## 1935
Haskell Curry. Can build all of intuitionistic logic with atoms and implies.

We use $\supset$ to denote $\implies$ in propositional logic,
and $\rightarrow$ in the type system

$p\supset q$ is equivalent to a function $p\rightarrow q$

or $p\supset q$ is a provable proposition $\iff p \rightarrow q$ is a computable function, ie propositions as types.

## 1960
Howard extends this to programs, ie proofs as programs, or proof normalisation as evaluation of programs.

$M : A, N : B$ M has type A, N has type B

$$\frac{
    \frac{M:A, N:B}{(M,N):A\times B}\times I}
    {M : A}\times E $$

is the same as $$M : A$$

## Dependent Type Theory

Adding quantifiers like $\forall$ and $\exists$ gives us dependent type theory.