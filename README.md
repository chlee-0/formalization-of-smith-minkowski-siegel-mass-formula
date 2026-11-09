# Formalization of the Smith–Minkowski–Siegel mass formula

A Lean 4 / Mathlib formalization of the Smith–Minkowski–Siegel mass formula for
positive-definite integral quadratic forms in every positive rank, mainly
developed with Codex and Claude Code.

In rank at least three the proof goes through Tamagawa numbers: the library
proves $\tau(\mathrm{Spin}) = 1$ and $\tau(SO) = 2$ for the positive-definite
rational quadratic spaces of dimension at least three.

As applications, the library determines the total mass of the positive-definite
unimodular lattices of every rank, odd and even, and the masses of explicit
lattices in ranks 1, 2, 3, 4 and 8.

Every theorem uses only the standard axioms `propext`, `Classical.choice` and
`Quot.sound`. The library has no `sorry` and no `axiom` declaration.
`Challenge.lean` is a statement template with seven intentional `sorry`
placeholders; the corresponding proofs are in `Solution.lean`.

(`SMS` in the library name stands for Smith–Minkowski–Siegel.)

The project was inspired by this remark in the Wikipedia article
[Smith–Minkowski–Siegel mass formula](https://en.wikipedia.org/wiki/Smith%E2%80%93Minkowski%E2%80%93Siegel_mass_formula):

> Many published versions of the mass formula have errors; in particular the
> 2-adic densities are difficult to get right, and it is sometimes forgotten
> that the trivial cases of dimensions 0 and 1 are different from the cases of
> dimension at least 2.

## The mass formula

Let $Q : \mathbb{Z}^n \to \mathbb{Z}$ be a positive-definite quadratic form with
integer values, $n \ge 1$. Its genus is the set of integral equivalence classes
of forms that are equivalent to $Q$ over $\mathbb{Z}_p$ for every prime $p$ and
over $\mathbb{R}$. Let

$$\mathrm{mass}(Q) = \sum_{[Q'] \in \mathrm{genus}(Q)} \frac{1}{|O(Q')|},$$

and let $\alpha_p(Q)$ be the local density of $Q$ at $p$, with the normalization
defined in `SMSFormula/LocalDensity.lean`. Then the limit

$$P = \lim_{N \to \infty} \prod_{p \le N} \alpha_p(Q)^{-1}$$

exists, $P > 0$, and

$$\mathrm{mass}(Q) = c(n) \cdot 2\,\pi^{-n(n+1)/4} \prod_{j=1}^{n} \Gamma(j/2) \cdot P,
\qquad c(1) = \tfrac12,\quad c(n) = 1 \text{ for } n \ge 2.$$

In rank one the formula without the factor $c(1)$ is false, and the
library proves this too. Rank zero is not covered.

In Lean, for a Mathlib quadratic form (`SMSFormula/MathlibMassFormula.lean`):

```lean
theorem PositiveDefiniteIntegralQuadraticForm.exists_massOfQuadraticForm_eq_positiveRank
    (hn : 1 ≤ n) (Q : QuadraticForm ℤ (Fin n → ℤ)) (hQ : Q.PosDef) :
    ∃ P : ℝ, 0 < P ∧ (ofQuadraticForm Q hQ).massLocalInverseProductTendsTo P ∧
      ((massOfQuadraticForm Q hQ : ℚ) : ℝ) =
        positiveRankMassCorrection n * (archimedeanMassFactor n * P)
```

Here `massOfQuadraticForm Q hQ` is the sum of $1/|O(Q')|$ over the integral
equivalence classes in the genus of `Q`, where $|O(Q')|$ is
`Nat.card (Q'.IsometryEquiv Q')` (`natCard_isometryGroup_ofQuadraticForm`).

Related statements in the same file:

- `exists_massOfQuadraticForm_eq_of_two_le`: the classical formula, without
  correction, for $n \ge 2$.
- `massOfQuadraticForm_eq_oddRankProductLimit` and `…_eq_evenRankProductLimit`
  ($n \ge 3$): $P$ as an explicit Euler product of zeta values (odd rank) or
  zeta and Dirichlet $L$-values (even rank), after a cutoff that contains every
  bad prime.

### Integral lattices

An integral lattice $(\mathbb{Z}^n, b)$ with an integer symmetric bilinear form
$b$ gives the integer-valued form $q(x) = b(x, x)$. Not every integer-valued
form arises this way: for $x^2 + xy + y^2$ the Gram matrix has entries $\tfrac12$.
The lattice version of the theorem,
`PositiveDefiniteIntegralLattice.exists_massFormula_positiveRank`, is the
special case for these forms, and `massOfQuadraticForm_integralLattice` shows
that the two masses agree.

## Examples

| Rank | Lattice | Mass of the genus |
| --- | --- | --- |
| 1 | $A_1$ | $1/2$ |
| 2 | $A_2$ | $1/12$ |
| 3 | $x^2 + 2y^2 + 11z^2$ | $3/8$ |
| 4 | $A_4$ | $1/240$ |
| 8 | $E_8$ | $1/696729600$ |
| every $n$ | all odd unimodular lattices (total mass) | `typeIConstant n` |
| every $n$ | all even unimodular lattices (total mass) | `typeIIConstant n` |

The total masses are sums of $1/|O(L)|$ over all isometry classes of
positive-definite unimodular lattices of rank $n$ that are odd (some vector has odd norm) or even
(every norm is even). With the Bernoulli numbers $B_k$ ($B_1 = -\tfrac12$),

$$P_r = \prod_{j=1}^{r} \frac{|B_{2j}|}{4j}, \qquad
B_{k,\chi_{-4}} = 4^{k-1}\bigl(B_k(\tfrac14) - B_k(\tfrac34)\bigr),$$

where $B_k(x)$ is the Bernoulli polynomial, they are as follows.

Even (Type II), $M_{\mathrm{II}}(n)$ = `typeIIConstant n`: $M_{\mathrm{II}}(n) = 0$
unless $8 \mid n$, and for $n = 8k > 0$

$$M_{\mathrm{II}}(n) = \frac{|B_{n/2}|}{n}\, P_{n/2-1}.$$

Odd (Type I), $M_{\mathrm{I}}(n)$ = `typeIConstant n`: $M_{\mathrm{I}}(1) = \tfrac12$.
For $n \ge 2$ let $m = \lfloor n/2 \rfloor$. If $n$ is odd,

$$M_{\mathrm{I}}(n) = \frac{2^m + \varepsilon_n}{2}\, P_m,$$

where $\varepsilon_n = +1$ if $n \equiv \pm 1 \pmod 8$ and $\varepsilon_n = -1$ otherwise.
If $n$ is even and $m$ is odd,

$$M_{\mathrm{I}}(n) = \frac{|B_{m,\chi_{-4}}|}{4m}\, P_{m-1}.$$

If $n$ and $m$ are both even,

$$M_{\mathrm{I}}(n) = \frac{(2^m - 1)(2^{m-1} + \delta_n)}{4m}\, |B_m|\, P_{m-1},$$

where $\delta_n = +1$ if $8 \mid n$ and $\delta_n = -1$ otherwise.

For example, $M_{\mathrm{I}}(1), M_{\mathrm{I}}(2), M_{\mathrm{I}}(3) = 1/2, 1/8, 1/48$
(the lattices $\mathbb{Z}^n$), and $M_{\mathrm{II}}(8) = 1/696729600$ (the lattice
$E_8$). The definitions are in `SMSFormula/Applications/Unimodular/Constants.lean`
and, with the same formulas, in `SMSFormula/Statements.lean`.

[`Challenge.lean`](Challenge.lean) states these results using only Lean and
Mathlib. Its definitions (lattices given by Gram matrices, integral isometry,
genus, $|O(L)|$, mass and the Bernoulli constants) are in
[`SMSFormula/Statements.lean`](SMSFormula/Statements.lean), which imports only
Mathlib, and the lattices are Mathlib's `CartanMatrix.A` and `CartanMatrix.E₈`.
[`Solution.lean`](Solution.lean) proves them from the library.

## Where things are

- `SMSFormula/MainResults.lean`: every main theorem restated with its full
  signature and checked for its axioms. Start here.
- `SMSFormula/MathlibMassFormula.lean`: the theorems for Mathlib quadratic forms.
- `SMSFormula/MathlibQuadraticForm.lean`: the library's types as Mathlib
  quadratic forms; integral equivalence is `QuadraticMap.Equivalent`, and
  $|O(Q)|$ is `Nat.card (Q.IsometryEquiv Q)`.
- `SMSFormula/Applications/Unimodular/`: the masses of unimodular lattices.
- `SMSFormula/Applications/Examples/`: the examples in ranks 2, 3 and 4.
- `Challenge.lean`, `Solution.lean`, `comparator.json`: the comparator check.

The library's own types are `PositiveDefiniteIntegralQuadraticForm n`, which
stores the symmetric integer matrix $A$ with even diagonal such that
$Q(x) = \tfrac12 x^{T} A x$, and `PositiveDefiniteIntegralLattice n`, which stores
the Gram matrix $F$ of an integral lattice with norm $x^{T} F x$.

## Building and using

The project uses Lean 4.30.0 and Mathlib
`c5ea00351c28e24afc9f0f84379aa41082b1188f`; the full dependency list is in
`lake-manifest.json`.

```
lake exe cache get
lake build
lake build Solution   # proofs of the statements in Challenge.lean
```

To use the library in another project, add it as a Lake dependency (with the
same Mathlib) and write `import SMSFormula`.

## License

Apache License 2.0; see [`LICENSE`](LICENSE). Citation metadata is in
[`CITATION.cff`](CITATION.cff).
