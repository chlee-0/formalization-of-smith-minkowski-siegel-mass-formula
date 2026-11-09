import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Log.Monotone
import Mathlib.Algebra.QuadraticAlgebra.NormDeterminant
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.GroupTheory.GroupAction.Quotient
import SMSFormula.MassProductDefinitions
import SMSFormula.LocalDensity
import SMSFormula.ArchimedeanMassFactor
import SMSFormula.QuadraticComplement

/-!
# The product side of the mass formula

For a prime `p`, `massLocalFactor L p` is the normalized local density
`normalizedLocalDensity L p` (Schulze--Pillot), and `massLocalInverseFactor L p`
is its inverse. Variants indexed by the subtype of primes, and the
fixed-exponent and one-exponent forms (`fixedK…`, `oneK…`), record the same
factor for products over primes.

`massBadPrimeSet L` consists of `2` and the primes dividing the polar
discriminant. This file defines the finite inverse products over prime sets,
their cutoffs, and the bad-prime part `massBadPrimeInverseProduct`. At a good
prime the inverse factor is computed from the order of the finite orthogonal
group of the Gram matrix over `𝔽_p` (section *Good-prime finite orthogonal
group*). This gives the zeta and Dirichlet Euler factors of the explicit odd-
and even-rank formulas in `SMSFormula.Final`. The archimedean factor
`archimedeanMassFactor n` and the product side
`massFormulaProductSide L P` close the file.
-/

noncomputable section

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}


/-- A fixed-admissible-exponent version of the local factor, indexed by the
subtype of rational primes.  Unlike `massLocalFactorAtPrime`,
this does not use the `k`-independent density `normalizedLocalDensity`; it keeps a
chosen admissible exponent `κ p` visible at every prime. -/
def fixedKMassLocalFactorAtPrime (L : PositiveDefiniteIntegralLattice n)
    (κ : {p : ℕ // Nat.Prime p} → ℕ)
    (hκ : ∀ p : {p : ℕ // Nat.Prime p},
      @IsLocalDensityAdmissibleExponent n L p.1 (κ p) ⟨p.2⟩)
    (p : {p : ℕ // Nat.Prime p}) : ℝ :=
  @normalizedLocalDensityAtExponent n L p.1 (κ p) ⟨p.2⟩ (hκ p)

/-- The inverse fixed-`k` local factor indexed by rational primes. -/
def fixedKMassLocalInverseFactorAtPrime (L : PositiveDefiniteIntegralLattice n)
    (κ : {p : ℕ // Nat.Prime p} → ℕ)
    (hκ : ∀ p : {p : ℕ // Nat.Prime p},
      @IsLocalDensityAdmissibleExponent n L p.1 (κ p) ⟨p.2⟩)
    (p : {p : ℕ // Nat.Prime p}) : ℝ :=
  (fixedKMassLocalFactorAtPrime L κ hκ p)⁻¹

/-- The fixed-`k` local factor using the universally coordinate-admissible
exponent
`k = 1` at every prime.  This is an alternative to the
`k`-independent factor `massLocalFactorAtPrime`: it does not
assert independence of the exponent, it simply chooses one admissible
exponent. -/
def oneKMassLocalFactorAtPrime (L : PositiveDefiniteIntegralLattice n)
    (p : {p : ℕ // Nat.Prime p}) : ℝ :=
  fixedKMassLocalFactorAtPrime L (fun _ => 1)
    (fun q => @isLocalDensityAdmissibleExponent_of_one_le n L q.1 1 ⟨q.2⟩
      (by norm_num))
    p

/-- The inverse one-`k` local factor indexed by rational primes. -/
def oneKMassLocalInverseFactorAtPrime (L : PositiveDefiniteIntegralLattice n)
    (p : {p : ℕ // Nat.Prime p}) : ℝ :=
  (oneKMassLocalFactorAtPrime L p)⁻¹

/-- The classical solution-count density indexed by the prime subtype.  This is
used to state good-prime cutoff lemmas without exposing a separate `Fact`
argument. -/
def classicalSolutionCountLocalDensityAtPrime (L : PositiveDefiniteIntegralLattice n)
    (p : {p : ℕ // Nat.Prime p}) : ℚ :=
  letI : Fact (Nat.Prime p.1) := ⟨p.2⟩
  classicalSolutionCountLocalDensity L p.1

/-- The finite product of inverse classical solution-count factors over a
chosen finite set of rational primes.  The good-prime cutoff below identifies
this with the Schulze--Pillot product away from the finite bad-prime set. -/
def massGoodPrimeClassicalInverseProduct (L : PositiveDefiniteIntegralLattice n)
    (S : Finset {p : ℕ // Nat.Prime p}) : ℝ :=
  S.prod fun p => ((((1 / 2 : ℚ) *
    classicalSolutionCountLocalDensityAtPrime L p : ℚ) : ℝ))⁻¹

/-- Half the classical solution-count local density at a prime.  At primes
away from the dyadic and discriminant bad set this equals the normalized local
density `massLocalFactorAtPrime` (see
`massLocalFactorAtPrime_eq_halfClassicalLocalDensityAtPrime`).  This is the
alpha-type normalization of Conway--Sloane (rather than their reciprocal
`p`-mass notation); in rank four it is also the normalization of Nipp's tables. -/
def halfClassicalLocalDensityAtPrime (L : PositiveDefiniteIntegralLattice n)
    (p : {p : ℕ // Nat.Prime p}) : ℝ :=
  (((1 / 2 : ℚ) * classicalSolutionCountLocalDensityAtPrime L p : ℚ) : ℝ)

lemma massLocalFactor_eq_normalizedLocalDensity
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    massLocalFactor L p = normalizedLocalDensity L p := by
  rfl

lemma massLocalFactor_pos
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    0 < massLocalFactor L p := by
  simpa [massLocalFactor] using
    normalizedLocalDensity_pos (n := n) L p

lemma massLocalFactor_eq_of_isSameGenus
    {L₀ L₁ : PositiveDefiniteIntegralLattice n} (h : L₀.IsSameGenus L₁)
    (p : ℕ) [Fact (Nat.Prime p)] :
    massLocalFactor L₀ p =
      massLocalFactor L₁ p := by
  simpa [massLocalFactor] using
    normalizedLocalDensity_eq_of_isSameGenus h p

lemma massLocalFactorAtPrime_pos
    (L : PositiveDefiniteIntegralLattice n) (p : {p : ℕ // Nat.Prime p}) :
    0 < massLocalFactorAtPrime L p := by
  letI : Fact (Nat.Prime p.1) := ⟨p.2⟩
  simpa [massLocalFactorAtPrime] using
    massLocalFactor_pos (n := n) L p.1

lemma massLocalInverseFactorAtPrime_pos
    (L : PositiveDefiniteIntegralLattice n) (p : {p : ℕ // Nat.Prime p}) :
    0 < massLocalInverseFactorAtPrime L p := by
  exact inv_pos.mpr (massLocalFactorAtPrime_pos L p)

lemma massLocalFactorAtPrime_eq_of_isSameGenus
    {L₀ L₁ : PositiveDefiniteIntegralLattice n} (h : L₀.IsSameGenus L₁)
    (p : {p : ℕ // Nat.Prime p}) :
    massLocalFactorAtPrime L₀ p =
      massLocalFactorAtPrime L₁ p := by
  letI : Fact (Nat.Prime p.1) := ⟨p.2⟩
  simpa [massLocalFactorAtPrime] using
    massLocalFactor_eq_of_isSameGenus h p.1

lemma massLocalInverseFactorAtPrime_eq_of_isSameGenus
    {L₀ L₁ : PositiveDefiniteIntegralLattice n} (h : L₀.IsSameGenus L₁)
    (p : {p : ℕ // Nat.Prime p}) :
    massLocalInverseFactorAtPrime L₀ p =
      massLocalInverseFactorAtPrime L₁ p := by
  rw [massLocalInverseFactorAtPrime,
    massLocalInverseFactorAtPrime,
    massLocalFactorAtPrime_eq_of_isSameGenus h p]


/-- Finite product of fixed-`k` inverse local factors over a chosen finite set
of rational primes. -/
def fixedKMassFinitePrimeInverseProduct (L : PositiveDefiniteIntegralLattice n)
    (κ : {p : ℕ // Nat.Prime p} → ℕ)
    (hκ : ∀ p : {p : ℕ // Nat.Prime p},
      @IsLocalDensityAdmissibleExponent n L p.1 (κ p) ⟨p.2⟩)
    (S : Finset {p : ℕ // Nat.Prime p}) : ℝ :=
  S.prod fun p => fixedKMassLocalInverseFactorAtPrime L κ hκ p

/-- Finite product of one-`k` inverse local factors over a chosen finite set of
rational primes. -/
def oneKMassFinitePrimeInverseProduct (L : PositiveDefiniteIntegralLattice n)
    (S : Finset {p : ℕ // Nat.Prime p}) : ℝ :=
  S.prod fun p => oneKMassLocalInverseFactorAtPrime L p

lemma massFinitePrimeInverseProduct_pos
    (L : PositiveDefiniteIntegralLattice n) (S : Finset {p : ℕ // Nat.Prime p}) :
    0 < massFinitePrimeInverseProduct L S := by
  refine Finset.prod_pos ?_
  intro p _hp
  exact massLocalInverseFactorAtPrime_pos L p

lemma massFinitePrimeInverseProduct_eq_of_isSameGenus
    {L₀ L₁ : PositiveDefiniteIntegralLattice n} (h : L₀.IsSameGenus L₁)
    (S : Finset {p : ℕ // Nat.Prime p}) :
    massFinitePrimeInverseProduct L₀ S =
      massFinitePrimeInverseProduct L₁ S := by
  refine Finset.prod_congr rfl ?_
  intro p _hp
  exact massLocalInverseFactorAtPrime_eq_of_isSameGenus h p

/-- The finite set of primes where the elementary good-prime cutoff may fail:
the dyadic prime and the primes dividing the bilinear Gram determinant. -/
def massBadPrimeSet (L : PositiveDefiniteIntegralLattice n) :
    Finset {p : ℕ // Nat.Prime p} :=
  insert ⟨2, Nat.prime_two⟩
    ((L.polarDeterminant.natAbs.primeFactors.attach).map
      ⟨fun p => ⟨p.1, Nat.prime_of_mem_primeFactors p.2⟩,
        by
          intro p q hpq
          exact Subtype.ext
            (show p.1 = q.1 from
              congrArg (fun r : {p : ℕ // Nat.Prime p} => r.1) hpq)⟩)

/-- The fixed bad-prime part of the finite inverse-product side.  Once a
finite prime set contains `massBadPrimeSet L`, the remaining factors
are all good-prime classical factors. -/
def massBadPrimeInverseProduct (L : PositiveDefiniteIntegralLattice n) : ℝ :=
  massFinitePrimeInverseProduct L (massBadPrimeSet L)

lemma mem_massBadPrimeSet_iff
    (L : PositiveDefiniteIntegralLattice n) (p : {p : ℕ // Nat.Prime p}) :
    p ∈ massBadPrimeSet L ↔ p.1 = 2 ∨ p.1 ∣ L.polarDeterminant.natAbs := by
  have hdisc_ne : L.polarDeterminant.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (ne_of_gt L.polarDeterminant_pos)
  simp only [massBadPrimeSet, Finset.mem_insert, Finset.mem_map,
    Finset.mem_attach]
  constructor
  · intro hp
    rcases hp with hp | ⟨q, _hqmem, hq⟩
    · exact Or.inl (congrArg (fun r : {p : ℕ // Nat.Prime p} => r.1) hp)
    · refine Or.inr ?_
      have hq_mem : q.1 ∈ L.polarDeterminant.natAbs.primeFactors := q.2
      have hq_dvd : q.1 ∣ L.polarDeterminant.natAbs :=
        (Nat.mem_primeFactors.mp hq_mem).2.1
      have hq_val : q.1 = p.1 :=
        congrArg (fun r : {p : ℕ // Nat.Prime p} => r.1) hq
      simpa [hq_val] using hq_dvd
  · intro hp
    rcases hp with hp | hp
    · exact Or.inl (Subtype.ext hp)
    · exact Or.inr
        ⟨⟨p.1, (Nat.mem_primeFactors.mpr ⟨p.2, hp, hdisc_ne⟩)⟩,
          trivial, Subtype.ext rfl⟩

lemma not_mem_massBadPrimeSet_ne_two
    (L : PositiveDefiniteIntegralLattice n) {p : {p : ℕ // Nat.Prime p}}
    (hp : p ∉ massBadPrimeSet L) :
    p.1 ≠ 2 := by
  intro hp_two
  exact hp ((mem_massBadPrimeSet_iff L p).mpr (Or.inl hp_two))

lemma not_mem_massBadPrimeSet_not_dvd_polarDeterminant_natAbs
    (L : PositiveDefiniteIntegralLattice n) {p : {p : ℕ // Nat.Prime p}}
    (hp : p ∉ massBadPrimeSet L) :
    ¬ p.1 ∣ L.polarDeterminant.natAbs := by
  intro hp_dvd
  exact hp ((mem_massBadPrimeSet_iff L p).mpr (Or.inr hp_dvd))

lemma not_mem_massBadPrimeSet_not_int_dvd_polarDeterminant
    (L : PositiveDefiniteIntegralLattice n) {p : {p : ℕ // Nat.Prime p}}
    (hp : p ∉ massBadPrimeSet L) :
    ¬ (p.1 : ℤ) ∣ L.polarDeterminant := by
  intro hdiv
  exact not_mem_massBadPrimeSet_not_dvd_polarDeterminant_natAbs L hp
    (by
      simpa using (Int.natAbs_dvd_natAbs.mpr hdiv))

lemma padicValInt_polarDeterminant_eq_zero_of_not_mem_massBadPrimeSet
    (L : PositiveDefiniteIntegralLattice n) {p : {p : ℕ // Nat.Prime p}}
    (hp : p ∉ massBadPrimeSet L) :
    padicValInt p.1 L.polarDeterminant = 0 := by
  exact padicValInt.eq_zero_of_not_dvd
    (not_mem_massBadPrimeSet_not_int_dvd_polarDeterminant L hp)

/-! ## Good-prime finite orthogonal group -/

section GoodPrimeFiniteOrthogonalGroup

open Matrix


/-- A matrix preserving a nonsingular Gram matrix over a field is invertible. -/
lemma matrix_isUnit_of_transpose_mul_mul_eq
    {K : Type*} [Field K]
    (A X : Matrix (Fin n) (Fin n) K)
    (hA : A.det ≠ 0) (hX : Xᵀ * A * X = A) : IsUnit X := by
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
  intro hdet
  have hd := congrArg Matrix.det hX
  simp only [Matrix.det_mul, Matrix.det_transpose] at hd
  rw [hdet] at hd
  simp at hd
  exact hA hd.symm

/-- The subgroup of `GL_n(K)` preserving the Gram matrix `A`. -/
def finiteGramOrthogonalGroup
    {K : Type*} [Field K]
    (A : Matrix (Fin n) (Fin n) K) :
    Subgroup (Matrix.GeneralLinearGroup (Fin n) K) where
  carrier := {X | (↑X : Matrix (Fin n) (Fin n) K)ᵀ * A * ↑X = A}
  one_mem' := by simp
  mul_mem' := by
    intro X Y hX hY
    change ((↑(X * Y) : Matrix (Fin n) (Fin n) K)ᵀ * A *
      (↑(X * Y) : Matrix (Fin n) (Fin n) K)) = A
    calc
      ((↑(X * Y) : Matrix (Fin n) (Fin n) K)ᵀ * A *
          (↑(X * Y) : Matrix (Fin n) (Fin n) K)) =
          (↑Y : Matrix (Fin n) (Fin n) K)ᵀ *
            ((↑X : Matrix (Fin n) (Fin n) K)ᵀ * A * ↑X) * ↑Y := by
            simp only [Matrix.GeneralLinearGroup.coe_mul, Matrix.transpose_mul]
            simp [Matrix.mul_assoc]
      _ = (↑Y : Matrix (Fin n) (Fin n) K)ᵀ * A * ↑Y := by rw [hX]
      _ = A := hY
  inv_mem' := by
    intro X hX
    change ((↑(X⁻¹) : Matrix (Fin n) (Fin n) K)ᵀ * A *
      (↑(X⁻¹) : Matrix (Fin n) (Fin n) K)) = A
    simp only [Matrix.GeneralLinearGroup.coe_inv]
    let U : Matrix (Fin n) (Fin n) K := X
    calc
      U⁻¹ᵀ * A * U⁻¹ =
          U⁻¹ᵀ * (Uᵀ * A * U) * U⁻¹ := by rw [hX]
      _ = (U * U⁻¹)ᵀ * A * (U * U⁻¹) := by
        simp only [Matrix.transpose_mul]
        simp [Matrix.mul_assoc]
      _ = A := by simp

/-- The Gram orthogonal group acts on column vectors by matrix
multiplication. -/
instance finiteGramOrthogonalGroupMulAction
    {K : Type*} [Field K]
    (A : Matrix (Fin n) (Fin n) K) :
    MulAction (finiteGramOrthogonalGroup A) (Fin n → K) where
  smul X v := (X.1.1 : Matrix (Fin n) (Fin n) K) *ᵥ v
  one_smul v := by
    change (1 : Matrix (Fin n) (Fin n) K) *ᵥ v = v
    simp
  mul_smul X Y v := by
    change (↑(X.1 * Y.1) : Matrix (Fin n) (Fin n) K) *ᵥ v =
      (X.1.1 : Matrix (Fin n) (Fin n) K) *ᵥ
        ((Y.1.1 : Matrix (Fin n) (Fin n) K) *ᵥ v)
    rw [Matrix.GeneralLinearGroup.coe_mul]
    exact (Matrix.mulVec_mulVec v X.1.1 Y.1.1).symm

/-- Gram orthogonal transformations preserve the represented quadratic
value. -/
lemma gramQuadraticValue_smul
    {K : Type*} [Field K]
    (A : Matrix (Fin n) (Fin n) K)
    (X : finiteGramOrthogonalGroup A) (v : Fin n → K) :
    gramQuadraticValue A (X • v) = gramQuadraticValue A v := by
  let U : Matrix (Fin n) (Fin n) K := X.1.1
  change (U *ᵥ v) ⬝ᵥ A *ᵥ (U *ᵥ v) = v ⬝ᵥ A *ᵥ v
  calc
    (U *ᵥ v) ⬝ᵥ A *ᵥ (U *ᵥ v) = ((U *ᵥ v) ᵥ* A) ⬝ᵥ (U *ᵥ v) :=
      Matrix.dotProduct_mulVec _ _ _
    _ = (v ᵥ* (Uᵀ * A)) ⬝ᵥ (U *ᵥ v) := by rw [Matrix.vecMul_mulVec]
    _ = ((v ᵥ* (Uᵀ * A)) ᵥ* U) ⬝ᵥ v := Matrix.dotProduct_mulVec _ _ _
    _ = (v ᵥ* (Uᵀ * A * U)) ⬝ᵥ v := by rw [Matrix.vecMul_vecMul]
    _ = (v ᵥ* A) ⬝ᵥ v := by rw [show Uᵀ * A * U = A by exact X.2]
    _ = v ⬝ᵥ A *ᵥ v := (Matrix.dotProduct_mulVec _ _ _).symm

/-- The vectors on which a Gram matrix takes a fixed quadratic value. -/
def finiteGramNormVectors
    {K : Type*} [Field K]
    (A : Matrix (Fin n) (Fin n) K) (c : K) :=
  {v : Fin n → K // gramQuadraticValue A v = c}

instance finiteGramNormVectorsFinite
    {K : Type*} [Field K] [Finite K]
    (A : Matrix (Fin n) (Fin n) K) (c : K) :
    Finite (finiteGramNormVectors A c) :=
  Finite.of_injective Subtype.val Subtype.val_injective

/-- Orthogonal transformations act on every fixed-norm vector subtype. -/
instance finiteGramNormVectorsMulAction
    {K : Type*} [Field K]
    (A : Matrix (Fin n) (Fin n) K) (c : K) :
    MulAction (finiteGramOrthogonalGroup A) (finiteGramNormVectors A c) where
  smul X v := ⟨X • v.1, (gramQuadraticValue_smul A X v.1).trans v.2⟩
  one_smul v := by
    apply Subtype.ext
    exact one_smul (finiteGramOrthogonalGroup A) v.1
  mul_smul X Y v := by
    apply Subtype.ext
    exact mul_smul X Y v.1

/-- Transport a fixed-norm shell along an equality of its Gram matrices. -/
noncomputable def finiteGramNormVectorsEquivOfEq
    {K : Type*} [Field K]
    {A B : Matrix (Fin n) (Fin n) K} (hAB : A = B) (c : K) :
    finiteGramNormVectors A c ≃ finiteGramNormVectors B c := by
  subst B
  exact Equiv.refl _

@[simp] lemma finiteGramNormVectorsEquivOfEq_apply_val
    {K : Type*} [Field K]
    {A B : Matrix (Fin n) (Fin n) K} (hAB : A = B) (c : K)
    (v : finiteGramNormVectors A c) :
    (finiteGramNormVectorsEquivOfEq hAB c v).1 = v.1 := by
  subst B
  rfl

@[simp] lemma finiteGramNormVectors_smul_val
    {K : Type*} [Field K]
    (A : Matrix (Fin n) (Fin n) K) (c : K)
    (X : finiteGramOrthogonalGroup A) (v : finiteGramNormVectors A c) :
    (X • v).1 = X • v.1 := rfl

/-- The stabilizer condition on a fixed-norm vector is the expected matrix
equation. -/
lemma mem_fixedNorm_stabilizer_iff_mulVec_eq
    {K : Type*} [Field K]
    (A : Matrix (Fin n) (Fin n) K) (c : K)
    (v : finiteGramNormVectors A c) (X : finiteGramOrthogonalGroup A) :
    X ∈ MulAction.stabilizer (finiteGramOrthogonalGroup A) v ↔
      (X.1.1 : Matrix (Fin n) (Fin n) K) *ᵥ v.1 = v.1 := by
  rw [MulAction.mem_stabilizer_iff]
  exact Subtype.ext_iff

/-- Orbit-stabilizer for a finite Gram orthogonal group acting on one fixed
quadratic-norm shell. This is the cardinality recurrence interface for the
higher-dimensional finite-field count. -/
lemma natCard_fixedNorm_orbit_mul_stabilizer_eq_finiteGramOrthogonalGroup
    {K : Type*} [Field K] [Finite K]
    (A : Matrix (Fin n) (Fin n) K) (c : K)
    (v : finiteGramNormVectors A c) :
    Nat.card (MulAction.orbit (finiteGramOrthogonalGroup A) v) *
        Nat.card (MulAction.stabilizer (finiteGramOrthogonalGroup A) v) =
      Nat.card (finiteGramOrthogonalGroup A) := by
  letI : Fintype K := Fintype.ofFinite K
  letI : Fintype (finiteGramOrthogonalGroup A) := Fintype.ofFinite _
  letI : Fintype (finiteGramNormVectors A c) := Fintype.ofFinite _
  letI : Fintype (MulAction.orbit (finiteGramOrthogonalGroup A) v) :=
    Fintype.ofFinite _
  letI : Fintype (MulAction.stabilizer (finiteGramOrthogonalGroup A) v) :=
    Fintype.ofFinite _
  simpa only [Nat.card_eq_fintype_card] using
    MulAction.card_orbit_mul_card_stabilizer_eq_card_group
      (finiteGramOrthogonalGroup A) v

/-- The head vector as an element of the fixed norm-`c` shell for
`diag(c,B)`. -/
def finSuccHeadNormVector
    {K : Type*} [Field K] (c : K) (B : Matrix (Fin n) (Fin n) K) :
    finiteGramNormVectors (finSuccGramBlock c B) c := by
  refine ⟨finSuccHeadVector, ?_⟩
  simp [gramQuadraticValue, finSuccHeadVector, finSuccGramBlock,
    Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

/-- Extend an orthogonal transformation of `B` by the fixed head
coordinate. -/
noncomputable def finSuccOrthogonalBlock
    {K : Type*} [Field K] (c : K) (B : Matrix (Fin n) (Fin n) K)
    (Y : finiteGramOrthogonalGroup B) :
    finiteGramOrthogonalGroup (finSuccGramBlock c B) := by
  refine ⟨finSuccGeneralLinearBlock Y.1, ?_⟩
  change (finSuccMatrixBlock (Y.1.1 : Matrix (Fin n) (Fin n) K))ᵀ *
      finSuccGramBlock c B *
        finSuccMatrixBlock (Y.1.1 : Matrix (Fin n) (Fin n) K) = _
  rw [finSuccMatrixBlock_congr, Y.2]

noncomputable def finSuccOrthogonalBlockStabilizer
    {K : Type*} [Field K] (c : K) (B : Matrix (Fin n) (Fin n) K)
    (Y : finiteGramOrthogonalGroup B) :
    MulAction.stabilizer
      (finiteGramOrthogonalGroup (finSuccGramBlock c B))
      (finSuccHeadNormVector c B) := by
  refine ⟨finSuccOrthogonalBlock c B Y, ?_⟩
  rw [mem_fixedNorm_stabilizer_iff_mulVec_eq]
  exact finSuccMatrixBlock_mulVec_head Y.1.1

/-- Extract an orthogonal transformation of `B` from an isometry of
`diag(c,B)` fixing the head vector. -/
noncomputable def finSuccStabilizerTailOrthogonal
    {K : Type*} [Field K] (c : K) (hc : c ≠ 0)
    (B : Matrix (Fin n) (Fin n) K) (hBdet : B.det ≠ 0)
    (X : MulAction.stabilizer
      (finiteGramOrthogonalGroup (finSuccGramBlock c B))
      (finSuccHeadNormVector c B)) :
    finiteGramOrthogonalGroup B := by
  let M := finSuccTailMatrix
    (X.1.1.1 : Matrix (Fin (n + 1)) (Fin (n + 1)) K)
  have hfix :
      (X.1.1.1 : Matrix (Fin (n + 1)) (Fin (n + 1)) K) *ᵥ
          finSuccHeadVector = finSuccHeadVector :=
    (mem_fixedNorm_stabilizer_iff_mulVec_eq _ _ _ X.1).mp X.2
  have hM : Mᵀ * B * M = B :=
    finSuccTailMatrix_preserves c hc B X.1.1.1 X.1.2 hfix
  exact ⟨Matrix.GeneralLinearGroup.mk'' M
      (M.isUnit_iff_isUnit_det.mp
        (matrix_isUnit_of_transpose_mul_mul_eq B M hBdet hM)), hM⟩

lemma finSuccMatrixBlock_tail_eq_of_preserves_fixed_head
    {K : Type*} [Field K] (c : K) (hc : c ≠ 0)
    (B : Matrix (Fin n) (Fin n) K)
    (X : Matrix (Fin (n + 1)) (Fin (n + 1)) K)
    (hpres : Xᵀ * finSuccGramBlock c B * X = finSuccGramBlock c B)
    (hfix : X *ᵥ finSuccHeadVector = finSuccHeadVector) :
    finSuccMatrixBlock (finSuccTailMatrix X) = X := by
  obtain ⟨h00, hcol⟩ := finSucc_fixed_head_entries X hfix
  have hrow := finSucc_fixed_head_row_zero c hc B X hpres hfix
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;>
    refine Fin.cases ?_ (fun j => ?_) j
  · simpa [finSuccMatrixBlock, finSuccGramBlock] using h00.symm
  · simpa [finSuccMatrixBlock, finSuccGramBlock] using (hrow j).symm
  · simpa [finSuccMatrixBlock, finSuccGramBlock] using (hcol i).symm
  · rfl

/-- The head-vector stabilizer of `diag(c,B)` is exactly the orthogonal group
of the lower block. -/
noncomputable def finSuccHeadStabilizerEquivOrthogonal
    {K : Type*} [Field K] (c : K) (hc : c ≠ 0)
    (B : Matrix (Fin n) (Fin n) K) (hBdet : B.det ≠ 0) :
    MulAction.stabilizer
        (finiteGramOrthogonalGroup (finSuccGramBlock c B))
        (finSuccHeadNormVector c B) ≃
      finiteGramOrthogonalGroup B where
  toFun := finSuccStabilizerTailOrthogonal c hc B hBdet
  invFun := finSuccOrthogonalBlockStabilizer c B
  left_inv X := by
    apply Subtype.ext
    apply Subtype.ext
    apply Matrix.GeneralLinearGroup.ext
    let U : Matrix (Fin (n + 1)) (Fin (n + 1)) K := X.1.1.1
    have hfix : U *ᵥ finSuccHeadVector = finSuccHeadVector :=
      (mem_fixedNorm_stabilizer_iff_mulVec_eq _ _ _ X.1).mp X.2
    have hmatrix := finSuccMatrixBlock_tail_eq_of_preserves_fixed_head
      c hc B U X.1.2 hfix
    intro i j
    exact congrFun (congrFun hmatrix i) j
  right_inv Y := by
    apply Subtype.ext
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    exact congrFun (congrFun
      (finSuccTailMatrix_finSuccMatrixBlock Y.1.1) i) j

lemma natCard_finSuccHeadStabilizer_eq_orthogonal
    {K : Type*} [Field K] (c : K) (hc : c ≠ 0)
    (B : Matrix (Fin n) (Fin n) K) (hBdet : B.det ≠ 0) :
    Nat.card (MulAction.stabilizer
        (finiteGramOrthogonalGroup (finSuccGramBlock c B))
        (finSuccHeadNormVector c B)) =
      Nat.card (finiteGramOrthogonalGroup B) :=
  Nat.card_congr (finSuccHeadStabilizerEquivOrthogonal c hc B hBdet)

/-- Orbit-stabilizer for the head vector of `diag(c,B)`, with its stabilizer
replaced by the lower-dimensional orthogonal group. -/
lemma natCard_finSuccHeadOrbit_mul_orthogonal_eq
    {K : Type*} [Field K] [Finite K]
    (c : K) (hc : c ≠ 0)
    (B : Matrix (Fin n) (Fin n) K) (hBdet : B.det ≠ 0) :
    Nat.card (MulAction.orbit
        (finiteGramOrthogonalGroup (finSuccGramBlock c B))
        (finSuccHeadNormVector c B)) *
        Nat.card (finiteGramOrthogonalGroup B) =
      Nat.card (finiteGramOrthogonalGroup (finSuccGramBlock c B)) := by
  rw [← natCard_finSuccHeadStabilizer_eq_orthogonal c hc B hBdet]
  exact natCard_fixedNorm_orbit_mul_stabilizer_eq_finiteGramOrthogonalGroup
    (finSuccGramBlock c B) c (finSuccHeadNormVector c B)

/-- The identity-form sign change on the head coordinate. -/
def identityHeadSignMatrix {K : Type*} [Field K] :
    Matrix (Fin (n + 1)) (Fin (n + 1)) K :=
  finSuccGramBlock (-1) 1

lemma identityHeadSignMatrix_mulVec
    {K : Type*} [Field K] (v : Fin (n + 1) → K) :
    Matrix.mulVec (identityHeadSignMatrix (K := K) (n := n)) v =
      Fin.cases (-v 0) (fun i => v i.succ) := by
  ext i
  refine Fin.cases ?_ (fun i => ?_) i
  · simp [identityHeadSignMatrix, finSuccGramBlock,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Matrix.one_apply]
  · simp [identityHeadSignMatrix, finSuccGramBlock,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Matrix.one_apply]

/-! ### Weighted-identity transitivity by Gram reflections -/

/-- The weighted identity Gram matrix `diag(d,Iₙ)`. -/
def finSuccIdentityGramMatrix
    {K : Type*} [Field K] (d : K) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) K :=
  finSuccGramBlock d 1

lemma finSuccIdentityGramMatrix_isSymm
    {K : Type*} [Field K] (d : K) :
    (finSuccIdentityGramMatrix (n := n) d).IsSymm := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;>
    refine Fin.cases ?_ (fun j => ?_) j
  all_goals simp [finSuccIdentityGramMatrix, finSuccGramBlock,
    Matrix.one_apply, eq_comm]

lemma finSuccIdentityGramMatrix_det
    {K : Type*} [Field K] (d : K) :
    (finSuccIdentityGramMatrix (n := n) d).det = d := by
  rw [show finSuccIdentityGramMatrix (n := n) d =
      Matrix.diagonal (Fin.cases d (fun _ => 1)) by
    ext i j
    refine Fin.cases ?_ (fun i => ?_) i <;>
      refine Fin.cases ?_ (fun j => ?_) j
    all_goals simp [finSuccIdentityGramMatrix, finSuccGramBlock,
      Matrix.diagonal, Matrix.one_apply, eq_comm]]
  rw [Matrix.det_diagonal, Fin.prod_univ_succ]
  simp

/-- For a norm-`d` target in `diag(d,Iₙ)`, the vector `e₀+v` has norm
`2d(1+v₀)`. -/
lemma finSuccIdentityHeadAdd_norm
    {K : Type*} [Field K] (d : K)
    (v : finiteGramNormVectors
      (finSuccIdentityGramMatrix (n := n) d) d) :
    gramQuadraticValue (finSuccIdentityGramMatrix (n := n) d)
        (finSuccHeadVector + v.1) =
      2 * d * (1 + v.1 0) := by
  have hv := v.2
  simp [gramQuadraticValue, finSuccIdentityGramMatrix,
    finSuccGramBlock, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
    finSuccHeadVector] at hv ⊢
  linear_combination hv

/-- The negative Gram reflection in `e₀+v`; this sends the head vector to
`v` when `v₀ ≠ -1`. -/
def finSuccIdentityHeadHouseholderMatrix
    {K : Type*} [Field K] (d : K)
    (v : Fin (n + 1) → K) : Matrix (Fin (n + 1)) (Fin (n + 1)) K :=
  -gramReflectionMatrix (finSuccIdentityGramMatrix d)
    (finSuccHeadVector + v)

lemma finSuccIdentityHeadHouseholderMatrix_preserves
    {K : Type*} [Field K] (hchar : ringChar K ≠ 2)
    (d : K) (hd : d ≠ 0)
    (v : finiteGramNormVectors
      (finSuccIdentityGramMatrix (n := n) d) d)
    (hhead : v.1 0 ≠ -1) :
    Matrix.transpose (finSuccIdentityHeadHouseholderMatrix d v.1) *
        finSuccIdentityGramMatrix d *
        finSuccIdentityHeadHouseholderMatrix d v.1 =
      finSuccIdentityGramMatrix d := by
  let A := finSuccIdentityGramMatrix (n := n) d
  let w := finSuccHeadVector + v.1
  have hq : gramQuadraticValue A w ≠ 0 := by
    rw [show gramQuadraticValue A w = 2 * d * (1 + v.1 0) by
      exact finSuccIdentityHeadAdd_norm d v]
    exact mul_ne_zero (mul_ne_zero (Ring.two_ne_zero hchar) hd) (by
      intro h
      apply hhead
      linear_combination h)
  have hM := gramReflectionMatrix_preserves A
    (finSuccIdentityGramMatrix_isSymm d) w hq
  change Matrix.transpose (-gramReflectionMatrix A w) * A *
    (-gramReflectionMatrix A w) = A
  simpa using hM

lemma finSuccIdentityHeadHouseholderMatrix_mulVec_head
    {K : Type*} [Field K] (hchar : ringChar K ≠ 2)
    (d : K) (hd : d ≠ 0)
    (v : finiteGramNormVectors
      (finSuccIdentityGramMatrix (n := n) d) d)
    (hhead : v.1 0 ≠ -1) :
    Matrix.mulVec (finSuccIdentityHeadHouseholderMatrix d v.1)
      finSuccHeadVector = v.1 := by
  let A := finSuccIdentityGramMatrix (n := n) d
  let w := finSuccHeadVector + v.1
  have hden : 1 + v.1 0 ≠ 0 := by
    intro h
    apply hhead
    linear_combination h
  have hq : gramQuadraticValue A w = 2 * d * (1 + v.1 0) :=
    finSuccIdentityHeadAdd_norm d v
  have hdot : Matrix.mulVec A w ⬝ᵥ finSuccHeadVector =
      d * (1 + v.1 0) := by
    simp [A, w, finSuccIdentityGramMatrix, finSuccGramBlock,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ, finSuccHeadVector]
  change Matrix.mulVec (-gramReflectionMatrix A w)
    finSuccHeadVector = v.1
  rw [Matrix.neg_mulVec, gramReflectionMatrix_mulVec, hq, hdot]
  ext i
  simp only [Pi.neg_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  dsimp [w]
  field_simp [Ring.two_ne_zero hchar, hd, hden]
  ring

/-- The head vector in the norm-`d` shell of `diag(d,Iₙ)`. -/
def finSuccIdentityHeadNormVector
    {K : Type*} [Field K] (d : K) :
    finiteGramNormVectors
      (finSuccIdentityGramMatrix (n := n) d) d :=
  finSuccHeadNormVector d (1 : Matrix (Fin n) (Fin n) K)

noncomputable def finSuccIdentityHeadIsometryOfHeadNeNegOne
    {K : Type*} [Field K] (hchar : ringChar K ≠ 2)
    (d : K) (hd : d ≠ 0)
    (v : finiteGramNormVectors
      (finSuccIdentityGramMatrix (n := n) d) d)
    (hhead : v.1 0 ≠ -1) :
    finiteGramOrthogonalGroup
      (finSuccIdentityGramMatrix (n := n) d) := by
  let A := finSuccIdentityGramMatrix (n := n) d
  let M := finSuccIdentityHeadHouseholderMatrix d v.1
  have hM : Matrix.transpose M * A * M = A :=
    finSuccIdentityHeadHouseholderMatrix_preserves hchar d hd v hhead
  exact ⟨Matrix.GeneralLinearGroup.mk'' M
    (M.isUnit_iff_isUnit_det.mp
      (matrix_isUnit_of_transpose_mul_mul_eq A M (by
        rw [finSuccIdentityGramMatrix_det]
        exact hd) hM)), hM⟩

lemma finSuccIdentityHeadIsometryOfHeadNeNegOne_smul
    {K : Type*} [Field K] (hchar : ringChar K ≠ 2)
    (d : K) (hd : d ≠ 0)
    (v : finiteGramNormVectors
      (finSuccIdentityGramMatrix (n := n) d) d)
    (hhead : v.1 0 ≠ -1) :
    finSuccIdentityHeadIsometryOfHeadNeNegOne
        (n := n) hchar d hd v hhead •
        (finSuccIdentityHeadNormVector (n := n) d) = v := by
  apply Subtype.ext
  exact finSuccIdentityHeadHouseholderMatrix_mulVec_head
    hchar d hd v hhead

/-- The head-coordinate sign change preserves every weighted identity form. -/
lemma identityHeadSignMatrix_preserves_finSuccIdentity
    {K : Type*} [Field K] (d : K) :
    Matrix.transpose (identityHeadSignMatrix (K := K) (n := n)) *
        finSuccIdentityGramMatrix d * identityHeadSignMatrix =
      finSuccIdentityGramMatrix d := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;>
    refine Fin.cases ?_ (fun j => ?_) j
  all_goals simp [identityHeadSignMatrix, finSuccIdentityGramMatrix,
    finSuccGramBlock, Matrix.mul_apply, Fin.sum_univ_succ,
    Matrix.one_apply, eq_comm]

noncomputable def finSuccIdentityHeadSignOrthogonal
    {K : Type*} [Field K] (d : K) (hd : d ≠ 0) :
    finiteGramOrthogonalGroup
      (finSuccIdentityGramMatrix (n := n) d) := by
  let A := finSuccIdentityGramMatrix (n := n) d
  let M := identityHeadSignMatrix (K := K) (n := n)
  have hM : Matrix.transpose M * A * M = A :=
    identityHeadSignMatrix_preserves_finSuccIdentity d
  exact ⟨Matrix.GeneralLinearGroup.mk'' M
    (M.isUnit_iff_isUnit_det.mp
      (matrix_isUnit_of_transpose_mul_mul_eq A M (by
        rw [finSuccIdentityGramMatrix_det]
        exact hd) hM)), hM⟩

lemma finSuccIdentityHeadSignOrthogonal_smul_smul
    {K : Type*} [Field K] (d : K) (hd : d ≠ 0)
    (v : finiteGramNormVectors
      (finSuccIdentityGramMatrix (n := n) d) d) :
    finSuccIdentityHeadSignOrthogonal (n := n) d hd •
        (finSuccIdentityHeadSignOrthogonal (n := n) d hd • v) = v := by
  apply Subtype.ext
  change Matrix.mulVec identityHeadSignMatrix
    (Matrix.mulVec identityHeadSignMatrix v.1) = v.1
  rw [identityHeadSignMatrix_mulVec, identityHeadSignMatrix_mulVec]
  ext i
  refine Fin.cases ?_ (fun i => ?_) i <;> simp

/-- In odd characteristic, `O(diag(d,Iₙ))` sends its head vector to every
vector of the same nonzero norm `d`. -/
theorem exists_finSuccIdentityOrthogonal_smul_head
    {K : Type*} [Field K] (hchar : ringChar K ≠ 2)
    (d : K) (hd : d ≠ 0)
    (v : finiteGramNormVectors
      (finSuccIdentityGramMatrix (n := n) d) d) :
    ∃ X : finiteGramOrthogonalGroup
        (finSuccIdentityGramMatrix (n := n) d),
      X • finSuccIdentityHeadNormVector (n := n) d = v := by
  by_cases hhead : v.1 0 ≠ -1
  · exact ⟨finSuccIdentityHeadIsometryOfHeadNeNegOne
      (n := n) hchar d hd v hhead,
      finSuccIdentityHeadIsometryOfHeadNeNegOne_smul
        hchar d hd v hhead⟩
  · let S := finSuccIdentityHeadSignOrthogonal (n := n) d hd
    let w := S • v
    have hw0 : w.1 0 ≠ -1 := by
      change (Matrix.mulVec identityHeadSignMatrix v.1) 0 ≠ -1
      rw [identityHeadSignMatrix_mulVec]
      simp only [Fin.cases_zero]
      have hv0 : v.1 0 = -1 := not_ne_iff.mp hhead
      rw [hv0, neg_neg]
      intro hone
      apply Ring.two_ne_zero hchar
      linear_combination hone
    let H := finSuccIdentityHeadIsometryOfHeadNeNegOne
      (n := n) hchar d hd w hw0
    refine ⟨S * H, ?_⟩
    rw [SemigroupAction.mul_smul,
      finSuccIdentityHeadIsometryOfHeadNeNegOne_smul]
    exact finSuccIdentityHeadSignOrthogonal_smul_smul d hd v

/-- The head orbit in the norm-`d` shell of `diag(d,Iₙ)` is the full shell. -/
theorem finSuccIdentityHeadOrbit_eq_fixedNorm
    {K : Type*} [Field K] (hchar : ringChar K ≠ 2)
    (d : K) (hd : d ≠ 0) :
    MulAction.orbit
        (finiteGramOrthogonalGroup
          (finSuccIdentityGramMatrix (n := n) d))
        (finSuccIdentityHeadNormVector (n := n) d) =
      Set.univ := by
  ext v
  simp only [Set.mem_univ, iff_true]
  obtain ⟨X, hX⟩ :=
    exists_finSuccIdentityOrthogonal_smul_head
      (n := n) hchar d hd v
  exact ⟨X, hX⟩

/-- Inverting a change-of-basis matrix reverses a Gram-matrix congruence. -/
lemma gramMatrix_congr_inv
    {K : Type*} [Field K]
    (A B : Matrix (Fin n) (Fin n) K)
    (P : Matrix.GeneralLinearGroup (Fin n) K)
    (hP : (↑P : Matrix (Fin n) (Fin n) K)ᵀ * A *
      (↑P : Matrix (Fin n) (Fin n) K) = B) :
    (↑(P⁻¹) : Matrix (Fin n) (Fin n) K)ᵀ * B *
      (↑(P⁻¹) : Matrix (Fin n) (Fin n) K) = A := by
  simp only [Matrix.GeneralLinearGroup.coe_inv]
  let U : Matrix (Fin n) (Fin n) K := P
  change U⁻¹ᵀ * B * U⁻¹ = A
  calc
    U⁻¹ᵀ * B * U⁻¹ = U⁻¹ᵀ * (Uᵀ * A * U) * U⁻¹ := by rw [hP]
    _ = (U * U⁻¹)ᵀ * A * (U * U⁻¹) := by
      simp only [Matrix.transpose_mul]
      simp [Matrix.mul_assoc]
    _ = A := by simp

lemma finiteGramOrthogonalGroup_inv_mul_mul_mem_of_congr
    {K : Type*} [Field K]
    (A B : Matrix (Fin n) (Fin n) K)
    (P : Matrix.GeneralLinearGroup (Fin n) K)
    (hP : (↑P : Matrix (Fin n) (Fin n) K)ᵀ * A *
      (↑P : Matrix (Fin n) (Fin n) K) = B)
    (X : finiteGramOrthogonalGroup A) :
    (↑(P⁻¹ * X.1 * P) : Matrix (Fin n) (Fin n) K)ᵀ * B *
      (↑(P⁻¹ * X.1 * P) : Matrix (Fin n) (Fin n) K) = B := by
  simp only [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_inv]
  let U : Matrix (Fin n) (Fin n) K := P
  let Z : Matrix (Fin n) (Fin n) K := X.1
  change (U⁻¹ * Z * U)ᵀ * B * (U⁻¹ * Z * U) = B
  calc
    (U⁻¹ * Z * U)ᵀ * B * (U⁻¹ * Z * U) =
        Uᵀ * Zᵀ * (U⁻¹ᵀ * B * U⁻¹) * Z * U := by
      simp only [Matrix.transpose_mul]
      simp [Matrix.mul_assoc]
    _ = Uᵀ * Zᵀ * A * Z * U := by
      rw [show U⁻¹ᵀ * B * U⁻¹ = A by
        simpa [U] using gramMatrix_congr_inv A B P hP]
    _ = Uᵀ * (Zᵀ * A * Z) * U := by simp [Matrix.mul_assoc]
    _ = Uᵀ * A * U := by rw [X.2]
    _ = B := hP

lemma finiteGramOrthogonalGroup_mul_mul_inv_mem_of_congr
    {K : Type*} [Field K]
    (A B : Matrix (Fin n) (Fin n) K)
    (P : Matrix.GeneralLinearGroup (Fin n) K)
    (hP : (↑P : Matrix (Fin n) (Fin n) K)ᵀ * A *
      (↑P : Matrix (Fin n) (Fin n) K) = B)
    (Y : finiteGramOrthogonalGroup B) :
    (↑(P * Y.1 * P⁻¹) : Matrix (Fin n) (Fin n) K)ᵀ * A *
      (↑(P * Y.1 * P⁻¹) : Matrix (Fin n) (Fin n) K) = A := by
  simp only [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_inv]
  let U : Matrix (Fin n) (Fin n) K := P
  let Z : Matrix (Fin n) (Fin n) K := Y.1
  change (U * Z * U⁻¹)ᵀ * A * (U * Z * U⁻¹) = A
  calc
    (U * Z * U⁻¹)ᵀ * A * (U * Z * U⁻¹) =
        U⁻¹ᵀ * Zᵀ * (Uᵀ * A * U) * Z * U⁻¹ := by
      simp only [Matrix.transpose_mul]
      simp [Matrix.mul_assoc]
    _ = U⁻¹ᵀ * Zᵀ * B * Z * U⁻¹ := by rw [hP]
    _ = U⁻¹ᵀ * (Zᵀ * B * Z) * U⁻¹ := by simp [Matrix.mul_assoc]
    _ = U⁻¹ᵀ * B * U⁻¹ := by rw [Y.2]
    _ = A := by simpa [U] using gramMatrix_congr_inv A B P hP

/-- Congruent Gram matrices have equivalent finite orthogonal groups. The
equivalence is conjugation by the change-of-basis matrix. -/
noncomputable def finiteGramOrthogonalGroupCongrEquiv
    {K : Type*} [Field K]
    (A B : Matrix (Fin n) (Fin n) K)
    (P : Matrix.GeneralLinearGroup (Fin n) K)
    (hP : (↑P : Matrix (Fin n) (Fin n) K)ᵀ * A *
      (↑P : Matrix (Fin n) (Fin n) K) = B) :
    finiteGramOrthogonalGroup A ≃ finiteGramOrthogonalGroup B where
  toFun X := ⟨P⁻¹ * X.1 * P,
    finiteGramOrthogonalGroup_inv_mul_mul_mem_of_congr A B P hP X⟩
  invFun Y := ⟨P * Y.1 * P⁻¹,
    finiteGramOrthogonalGroup_mul_mul_inv_mem_of_congr A B P hP Y⟩
  left_inv X := by
    apply Subtype.ext
    simp [mul_assoc]
  right_inv Y := by
    apply Subtype.ext
    simp [mul_assoc]

lemma natCard_finiteGramOrthogonalGroup_eq_of_congr
    {K : Type*} [Field K]
    (A B : Matrix (Fin n) (Fin n) K)
    (P : Matrix.GeneralLinearGroup (Fin n) K)
    (hP : (↑P : Matrix (Fin n) (Fin n) K)ᵀ * A *
      (↑P : Matrix (Fin n) (Fin n) K) = B) :
    Nat.card (finiteGramOrthogonalGroup A) = Nat.card (finiteGramOrthogonalGroup B) :=
  Nat.card_congr (finiteGramOrthogonalGroupCongrEquiv A B P hP)

/-- For a nonsingular Gram matrix, all preserving matrices are precisely the
elements of its Gram-orthogonal subgroup. -/
noncomputable def matrixPreserverEquivFiniteGramOrthogonalGroup
    {K : Type*} [Field K]
    (A : Matrix (Fin n) (Fin n) K) (hA : A.det ≠ 0) :
    {X : Matrix (Fin n) (Fin n) K // Xᵀ * A * X = A} ≃
      finiteGramOrthogonalGroup A :=
  { toFun := fun X =>
      ⟨Matrix.GeneralLinearGroup.mk'' X.1
          (X.1.isUnit_iff_isUnit_det.mp
            (matrix_isUnit_of_transpose_mul_mul_eq A X.1 hA X.2)),
        X.2⟩
    invFun := fun X => ⟨X.1.1, X.2⟩
    left_inv := by
      intro X
      apply Subtype.ext
      rfl
    right_inv := by
      intro X
      apply Subtype.ext
      apply Matrix.GeneralLinearGroup.ext
      intro i j
      rfl }

/-- The integral Gram matrix reduced modulo a rational prime. -/
def goodPrimeGramMatrix
    (L : PositiveDefiniteIntegralLattice n) (p : {p : ℕ // Nat.Prime p}) :
    Matrix (Fin n) (Fin n) (ZMod p.1) :=
  L.polarGramMatrix.map (Int.cast : ℤ → ZMod p.1)

lemma goodPrimeGramMatrix_det_ne_zero
    (L : PositiveDefiniteIntegralLattice n) (p : {p : ℕ // Nat.Prime p})
    (hp : p ∉ massBadPrimeSet L) :
    (goodPrimeGramMatrix L p).det ≠ 0 := by
  have hdisc : (L.polarDeterminant : ZMod p.1) ≠ 0 :=
    (CharP.intCast_eq_zero_iff (ZMod p.1) p.1 L.polarDeterminant).not.mpr
      (not_mem_massBadPrimeSet_not_int_dvd_polarDeterminant L hp)
  rw [PositiveDefiniteIntegralLattice.polarDeterminant, Int.cast_det] at hdisc
  exact hdisc

/-- The finite orthogonal group of the reduced good-prime Gram matrix. -/
def goodPrimeFiniteGramOrthogonalGroup
    (L : PositiveDefiniteIntegralLattice n) (p : {p : ℕ // Nat.Prime p}) :
    Subgroup (Matrix.GeneralLinearGroup (Fin n) (ZMod p.1)) :=
  letI : Fact (Nat.Prime p.1) := ⟨p.2⟩
  finiteGramOrthogonalGroup (goodPrimeGramMatrix L p)

noncomputable def goodPrimeGramCongruenceSolutionEquivOrthogonalGroup
    (L : PositiveDefiniteIntegralLattice n) (p : {p : ℕ // Nat.Prime p})
    (hp : p ∉ massBadPrimeSet L) :
    {X : Matrix (Fin n) (Fin n) (ZMod p.1) //
      Xᵀ * goodPrimeGramMatrix L p * X = goodPrimeGramMatrix L p} ≃
      goodPrimeFiniteGramOrthogonalGroup L p := by
  letI : Fact (Nat.Prime p.1) := ⟨p.2⟩
  exact matrixPreserverEquivFiniteGramOrthogonalGroup
    (goodPrimeGramMatrix L p) (goodPrimeGramMatrix_det_ne_zero L p hp)

/-- The good-prime congruence-solution finset is the underlying finite
orthogonal group. -/
noncomputable def goodPrimeGramCongruenceFinsetEquivOrthogonalGroup
    (L : PositiveDefiniteIntegralLattice n) (p : {p : ℕ // Nat.Prime p})
    (hp : p ∉ massBadPrimeSet L) :
    {X : Matrix (Fin n) (Fin n) (ZMod p.1) //
      X ∈ congruenceSolutionMatrices L.polarGramMatrix ⟨p.1, p.2.pos⟩} ≃
      goodPrimeFiniteGramOrthogonalGroup L p :=
  let e := goodPrimeGramCongruenceSolutionEquivOrthogonalGroup L p hp
  { toFun := fun X =>
      e ⟨X.1, mem_congruenceSolutionMatrices_iff.mp X.2⟩
    invFun := fun X =>
      ⟨(e.symm X).1, mem_congruenceSolutionMatrices_iff.mpr (e.symm X).2⟩
    left_inv := by
      intro X
      apply Subtype.ext
      change (e.symm (e ⟨X.1,
        mem_congruenceSolutionMatrices_iff.mp X.2⟩)).1 = X.1
      exact congrArg Subtype.val (e.left_inv ⟨X.1,
        mem_congruenceSolutionMatrices_iff.mp X.2⟩)
    right_inv := by
      intro X
      exact e.right_inv X }

lemma goodPrimeGramCongruenceSolutionCount_eq_natCard_orthogonalGroup
    (L : PositiveDefiniteIntegralLattice n) (p : {p : ℕ // Nat.Prime p})
    (hp : p ∉ massBadPrimeSet L) :
    congruenceSolutionCount L.polarGramMatrix ⟨p.1, p.2.pos⟩ =
      Nat.card (goodPrimeFiniteGramOrthogonalGroup L p) := by
  unfold congruenceSolutionCount
  rw [← Fintype.card_coe, ← Nat.card_eq_fintype_card]
  exact Nat.card_congr (goodPrimeGramCongruenceFinsetEquivOrthogonalGroup L p hp)

lemma goodPrimeGramCongruenceSolutionCount_one_eq_natCard_orthogonalGroup
    (L : PositiveDefiniteIntegralLattice n) (p : {p : ℕ // Nat.Prime p})
    (hp : p ∉ massBadPrimeSet L) : letI : Fact (Nat.Prime p.1) := ⟨p.2⟩
    gramCongruenceSolutionCount L p.1 1 =
      Nat.card (goodPrimeFiniteGramOrthogonalGroup L p) := by
  letI : Fact (Nat.Prime p.1) := ⟨p.2⟩
  have hm : primePowModulus p.1 1 = ⟨p.1, p.2.pos⟩ := by
    apply Subtype.ext
    exact pow_one p.1
  unfold gramCongruenceSolutionCount gramCongruenceSolutionMatrices
  rw [hm]
  exact goodPrimeGramCongruenceSolutionCount_eq_natCard_orthogonalGroup L p hp

/-- At a good prime, exponent independence reduces the preferred classical
density to the depth-one finite congruence count. -/
lemma classicalSolutionCountLocalDensityAtPrime_eq_classicalGramLocalDensity_one_of_goodPrime
    (L : PositiveDefiniteIntegralLattice n) (p : {p : ℕ // Nat.Prime p})
    (hp : p ∉ massBadPrimeSet L) :
    classicalSolutionCountLocalDensityAtPrime L p =
      letI : Fact (Nat.Prime p.1) := ⟨p.2⟩
      classicalGramLocalDensity L p.1 1 := by
  letI : Fact (Nat.Prime p.1) := ⟨p.2⟩
  have hp_two : p.1 ≠ 2 :=
    not_mem_massBadPrimeSet_ne_two L hp
  have hval : padicValInt p.1 L.polarDeterminant = 0 :=
    padicValInt_polarDeterminant_eq_zero_of_not_mem_massBadPrimeSet L hp
  have hk_one : IsLocalDensityClassicalComparisonExponent L p.1 1 :=
    isLocalDensityClassicalComparisonExponent_of_polarDeterminant_val_lt
      (n := n) L p.1 1 (by omega) hp_two
  have h := classicalComparisonValue_eq_of_classicalComparisonExponent
    (n := n) L p.1 (classicalComparisonExponent L p.1) 1
    (isLocalDensityClassicalComparisonExponent_preferred (n := n) L p.1 hp_two)
    hk_one hp_two
  rw [hval] at h
  norm_num at h
  exact_mod_cast h

/-- The good-prime classical density is the normalized order of the finite
orthogonal group of the reduced Gram form. -/
lemma classicalSolutionCountLocalDensityAtPrime_eq_orthogonalGroup_normalizedCard_of_goodPrime
    (L : PositiveDefiniteIntegralLattice n) (p : {p : ℕ // Nat.Prime p})
    (hp : p ∉ massBadPrimeSet L) :
    classicalSolutionCountLocalDensityAtPrime L p =
      ((p.1 : ℚ) ^ (n * (n - 1) / 2))⁻¹ *
        (Nat.card (goodPrimeFiniteGramOrthogonalGroup L p) : ℚ) := by
  letI : Fact (Nat.Prime p.1) := ⟨p.2⟩
  rw [classicalSolutionCountLocalDensityAtPrime_eq_classicalGramLocalDensity_one_of_goodPrime
    L p hp]
  unfold classicalGramLocalDensity
  rw [goodPrimeGramCongruenceSolutionCount_one_eq_natCard_orthogonalGroup L p hp]
  simp [localDensityDenominatorExponent]

/-- In rank one, Gram-preserving matrices are the scalar square roots of one. -/
def rankOneMatrixPreserverEquivUnitRoots
    {K : Type*} [Field K]
    (A : Matrix (Fin 1) (Fin 1) K) (hA : A.det ≠ 0) :
    {X : Matrix (Fin 1) (Fin 1) K // Xᵀ * A * X = A} ≃
      {x : K // x * x = 1} where
  toFun X := ⟨X.1 0 0, by
    have ha : A 0 0 ≠ 0 := by simpa using hA
    have h := congrFun (congrFun X.2 0) 0
    simp [Matrix.mul_apply] at h
    apply mul_left_cancel₀ ha
    calc
      A 0 0 * (X.1 0 0 * X.1 0 0) = X.1 0 0 * A 0 0 * X.1 0 0 := by ring
      _ = A 0 0 := h
      _ = A 0 0 * 1 := by simp⟩
  invFun x := ⟨fun _ _ => x.1, by
    ext i j
    fin_cases i
    fin_cases j
    simp only [Matrix.mul_apply, Finset.univ_unique, Fin.default_eq_zero,
      Finset.sum_singleton, transpose_apply]
    calc
      x.1 * A 0 0 * x.1 = A 0 0 * (x.1 * x.1) := by ring
      _ = A 0 0 := by rw [x.2, mul_one]⟩
  left_inv X := by
    apply Subtype.ext
    ext i j
    fin_cases i
    fin_cases j
    rfl
  right_inv x := by
    apply Subtype.ext
    rfl

/-- Over a field of characteristic different from two, the scalar square
roots of one are `1` and `-1`. -/
noncomputable def unitRootsEquivBool
    {K : Type*} [Field K] (hchar : ringChar K ≠ 2) :
    {x : K // x * x = 1} ≃ Bool := by
  classical
  exact
    { toFun := fun x => decide (x.1 ≠ 1)
      invFun := fun b => if b then ⟨-1, by simp⟩ else ⟨1, by simp⟩
      left_inv := by
        intro x
        apply Subtype.ext
        by_cases hx : x.1 = 1
        · simp [hx]
        · have hxneg : x.1 = -1 := (mul_self_eq_one_iff.mp x.2).resolve_left hx
          simp [hxneg, Ring.neg_one_ne_one_of_char_ne_two hchar]
      right_inv := by
        intro b
        cases b
        · simp
        · simp [Ring.neg_one_ne_one_of_char_ne_two hchar] }

noncomputable def rankOneFiniteGramOrthogonalGroupEquivBool
    {K : Type*} [Field K]
    (A : Matrix (Fin 1) (Fin 1) K) (hA : A.det ≠ 0)
    (hchar : ringChar K ≠ 2) :
    finiteGramOrthogonalGroup A ≃ Bool :=
  (matrixPreserverEquivFiniteGramOrthogonalGroup A hA).symm.trans
    ((rankOneMatrixPreserverEquivUnitRoots A hA).trans
      (unitRootsEquivBool hchar))

/-- Every nonsingular one-dimensional orthogonal group over a field of odd
characteristic has order two. -/
lemma natCard_rankOneFiniteGramOrthogonalGroup
    {K : Type*} [Field K]
    (A : Matrix (Fin 1) (Fin 1) K) (hA : A.det ≠ 0)
    (hchar : ringChar K ≠ 2) :
    Nat.card (finiteGramOrthogonalGroup A) = 2 := by
  rw [Nat.card_congr (rankOneFiniteGramOrthogonalGroupEquivBool A hA hchar)]
  simp

lemma natCard_goodPrimeFiniteGramOrthogonalGroup_rank_one
    (L : PositiveDefiniteIntegralLattice 1) (p : {p : ℕ // Nat.Prime p})
    (hp : p ∉ massBadPrimeSet L) :
    Nat.card (goodPrimeFiniteGramOrthogonalGroup L p) = 2 := by
  letI : Fact (Nat.Prime p.1) := ⟨p.2⟩
  apply natCard_rankOneFiniteGramOrthogonalGroup
  · exact goodPrimeGramMatrix_det_ne_zero L p hp
  · rw [ZMod.ringChar_zmod_n]
    exact not_mem_massBadPrimeSet_ne_two L hp

/-- The Gram matrix of the standard split hyperbolic plane. -/
def splitHyperbolicPlaneGramMatrix (K : Type*) [Zero K] [One K] :
    Matrix (Fin 2) (Fin 2) K :=
  !![0, 1; 1, 0]

/-- The four scalar equations defining an isometry of the split hyperbolic
plane. -/
lemma splitHyperbolicPlane_preserves_iff
    {K : Type*} [CommRing K]
    (X : Matrix (Fin 2) (Fin 2) K) :
    Xᵀ * splitHyperbolicPlaneGramMatrix K * X = splitHyperbolicPlaneGramMatrix K ↔
      X 0 0 * X 1 0 + X 1 0 * X 0 0 = 0 ∧
      X 0 0 * X 1 1 + X 1 0 * X 0 1 = 1 ∧
      X 0 1 * X 1 0 + X 1 1 * X 0 0 = 1 ∧
      X 0 1 * X 1 1 + X 1 1 * X 0 1 = 0 := by
  constructor
  · intro h
    have h00 := congrFun (congrFun h 0) 0
    have h01 := congrFun (congrFun h 0) 1
    have h10 := congrFun (congrFun h 1) 0
    have h11 := congrFun (congrFun h 1) 1
    simpa [splitHyperbolicPlaneGramMatrix, Matrix.mul_apply, Fin.sum_univ_two, add_comm] using
      And.intro h00 (And.intro h01 (And.intro h10 h11))
  · rintro ⟨h00, h01, h10, h11⟩
    ext i j
    fin_cases i <;> fin_cases j
    · simpa [splitHyperbolicPlaneGramMatrix, Matrix.mul_apply, Fin.sum_univ_two, add_comm] using h00
    · simpa [splitHyperbolicPlaneGramMatrix, Matrix.mul_apply, Fin.sum_univ_two, add_comm] using h01
    · simpa [splitHyperbolicPlaneGramMatrix, Matrix.mul_apply, Fin.sum_univ_two, add_comm] using h10
    · simpa [splitHyperbolicPlaneGramMatrix, Matrix.mul_apply, Fin.sum_univ_two, add_comm] using h11

/-- Diagonal and anti-diagonal unit matrices preserve the split hyperbolic
plane. -/
def splitHyperbolicPlanePreserverOfUnitBool
    {K : Type*} [Field K] : Kˣ × Bool →
      {X : Matrix (Fin 2) (Fin 2) K //
        Xᵀ * splitHyperbolicPlaneGramMatrix K * X = splitHyperbolicPlaneGramMatrix K}
  | (u, false) => ⟨!![(u : K), 0; 0, (↑(u⁻¹) : K)], by
      rw [splitHyperbolicPlane_preserves_iff]
      simp⟩
  | (u, true) => ⟨!![0, (u : K); (↑(u⁻¹) : K), 0], by
      rw [splitHyperbolicPlane_preserves_iff]
      simp⟩

/-- In characteristic different from two, every isometry of the split
hyperbolic plane is uniquely diagonal or anti-diagonal. -/
noncomputable def unitBoolEquivSplitHyperbolicPlanePreserver
    {K : Type*} [Field K] (hchar : ringChar K ≠ 2) :
    Kˣ × Bool ≃
      {X : Matrix (Fin 2) (Fin 2) K //
        Xᵀ * splitHyperbolicPlaneGramMatrix K * X = splitHyperbolicPlaneGramMatrix K} := by
  classical
  apply Equiv.ofBijective splitHyperbolicPlanePreserverOfUnitBool
  constructor
  · rintro ⟨u, b⟩ ⟨v, c⟩ h
    cases b <;> cases c
    · apply Prod.ext
      · apply Units.ext
        exact congrFun (congrFun (congrArg Subtype.val h) 0) 0
      · rfl
    · exfalso
      apply Units.ne_zero u
      exact congrFun (congrFun (congrArg Subtype.val h) 0) 0
    · exfalso
      apply Units.ne_zero v
      exact (congrFun (congrFun (congrArg Subtype.val h) 0) 0).symm
    · apply Prod.ext
      · apply Units.ext
        exact congrFun (congrFun (congrArg Subtype.val h) 0) 1
      · rfl
  · intro X
    obtain ⟨h00, h01, h10, h11⟩ := splitHyperbolicPlane_preserves_iff X.1 |>.mp X.2
    have htwo : (2 : K) ≠ 0 := Ring.two_ne_zero hchar
    have hac : X.1 0 0 * X.1 1 0 = 0 := by
      have h : (2 : K) * (X.1 0 0 * X.1 1 0) = 0 := by
        calc
          (2 : K) * (X.1 0 0 * X.1 1 0) =
              X.1 0 0 * X.1 1 0 + X.1 1 0 * X.1 0 0 := by ring
          _ = 0 := h00
      exact (mul_eq_zero.mp h).resolve_left htwo
    have hbd : X.1 0 1 * X.1 1 1 = 0 := by
      have h : (2 : K) * (X.1 0 1 * X.1 1 1) = 0 := by
        calc
          (2 : K) * (X.1 0 1 * X.1 1 1) =
              X.1 0 1 * X.1 1 1 + X.1 1 1 * X.1 0 1 := by ring
          _ = 0 := h11
      exact (mul_eq_zero.mp h).resolve_left htwo
    by_cases ha : X.1 0 0 = 0
    · have hcb : X.1 1 0 * X.1 0 1 = 1 := by simpa [ha] using h01
      have hbc : X.1 0 1 * X.1 1 0 = 1 := by simpa [ha] using h10
      have hb : X.1 0 1 ≠ 0 := by
        intro hb
        simp [hb] at hbc
      have hd : X.1 1 1 = 0 := (mul_eq_zero.mp hbd).resolve_left hb
      let u : Kˣ :=
        { val := X.1 0 1
          inv := X.1 1 0
          val_inv := hbc
          inv_val := hcb }
      refine ⟨(u, true), ?_⟩
      apply Subtype.ext
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [splitHyperbolicPlanePreserverOfUnitBool, u, ha, hd]
    · have hc : X.1 1 0 = 0 := (mul_eq_zero.mp hac).resolve_left ha
      have had : X.1 0 0 * X.1 1 1 = 1 := by simpa [hc] using h01
      have hda : X.1 1 1 * X.1 0 0 = 1 := by simpa [hc] using h10
      have hd : X.1 1 1 ≠ 0 := by
        intro hd
        simp [hd] at had
      have hb : X.1 0 1 = 0 := (mul_eq_zero.mp hbd).resolve_right hd
      let u : Kˣ :=
        { val := X.1 0 0
          inv := X.1 1 1
          val_inv := had
          inv_val := hda }
      refine ⟨(u, false), ?_⟩
      apply Subtype.ext
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [splitHyperbolicPlanePreserverOfUnitBool, u, hb, hc]

/-- The preserving matrices of a split hyperbolic plane over a finite field
have cardinality `2 * (|K| - 1)`. -/
lemma natCard_splitHyperbolicPlanePreserver
    {K : Type*} [Field K] [Finite K] (hchar : ringChar K ≠ 2) :
    Nat.card {X : Matrix (Fin 2) (Fin 2) K //
      Xᵀ * splitHyperbolicPlaneGramMatrix K * X = splitHyperbolicPlaneGramMatrix K} =
      2 * (Nat.card K - 1) := by
  rw [← Nat.card_congr (unitBoolEquivSplitHyperbolicPlanePreserver hchar)]
  simp [Nat.card_prod, Nat.card_units, Nat.mul_comm]

/-- The finite orthogonal group of a split hyperbolic plane has order
`2 * (|K| - 1)`. -/
lemma natCard_splitHyperbolicPlaneFiniteGramOrthogonalGroup
    {K : Type*} [Field K] [Finite K] (hchar : ringChar K ≠ 2) :
    Nat.card (finiteGramOrthogonalGroup (splitHyperbolicPlaneGramMatrix K)) =
      2 * (Nat.card K - 1) := by
  rw [← Nat.card_congr (matrixPreserverEquivFiniteGramOrthogonalGroup
    (splitHyperbolicPlaneGramMatrix K) (by simp [splitHyperbolicPlaneGramMatrix,
      Matrix.det_fin_two]))]
  exact natCard_splitHyperbolicPlanePreserver hchar

/-- Any binary Gram matrix explicitly congruent to the split hyperbolic plane
has orthogonal-group order `2 * (|K| - 1)`. -/
lemma natCard_finiteGramOrthogonalGroup_eq_splitHyperbolicPlane_of_congr
    {K : Type*} [Field K] [Finite K]
    (A : Matrix (Fin 2) (Fin 2) K)
    (P : Matrix.GeneralLinearGroup (Fin 2) K)
    (hP : (↑P : Matrix (Fin 2) (Fin 2) K)ᵀ * A *
      (↑P : Matrix (Fin 2) (Fin 2) K) = splitHyperbolicPlaneGramMatrix K)
    (hchar : ringChar K ≠ 2) :
    Nat.card (finiteGramOrthogonalGroup A) = 2 * (Nat.card K - 1) := by
  rw [natCard_finiteGramOrthogonalGroup_eq_of_congr A
    (splitHyperbolicPlaneGramMatrix K) P hP]
  exact natCard_splitHyperbolicPlaneFiniteGramOrthogonalGroup hchar

/-- A nonsingular symmetric binary Gram matrix with square negative
determinant is explicitly congruent to the split hyperbolic plane. -/
theorem exists_binaryGram_congr_splitHyperbolicPlane_of_neg_det_eq_sq
    {K : Type*} [Field K]
    (A : Matrix (Fin 2) (Fin 2) K) (hA_symm : A.IsSymm)
    (hA_det : A.det ≠ 0) (hchar : ringChar K ≠ 2)
    (t : K) (ht : t * t = -A.det) :
    ∃ P : Matrix.GeneralLinearGroup (Fin 2) K,
      (↑P : Matrix (Fin 2) (Fin 2) K)ᵀ * A *
        (↑P : Matrix (Fin 2) (Fin 2) K) = splitHyperbolicPlaneGramMatrix K := by
  let a := A 0 0
  let b := A 0 1
  let c := A 1 1
  have hsymm : A 1 0 = b := by simpa [b] using hA_symm.apply 0 1
  have htwo : (2 : K) ≠ 0 := Ring.two_ne_zero hchar
  have ht_ne : t ≠ 0 := by
    intro ht0
    apply hA_det
    simpa [ht0] using ht
  by_cases ha : a = 0
  · have hb : b ≠ 0 := by
      intro hb0
      apply hA_det
      simp [Matrix.det_fin_two, a, b, ha, hb0, hsymm]
    have hb' : A 0 1 ≠ 0 := by simpa [b] using hb
    let P0 : Matrix (Fin 2) (Fin 2) K :=
      !![1, -c / (2 * b * b); 0, 1 / b]
    have hP0det : P0.det ≠ 0 := by
      simp [P0, Matrix.det_fin_two, hb]
    let P : Matrix.GeneralLinearGroup (Fin 2) K :=
      Matrix.GeneralLinearGroup.mk'' P0 (isUnit_iff_ne_zero.mpr hP0det)
    refine ⟨P, ?_⟩
    change P0ᵀ * A * P0 = splitHyperbolicPlaneGramMatrix K
    ext i j
    fin_cases i <;> fin_cases j
    all_goals simp [P0, splitHyperbolicPlaneGramMatrix, Matrix.mul_apply,
      Fin.sum_univ_two, a, b, c, ha, hsymm]
    all_goals field_simp [hb', htwo]
    all_goals ring
  · have ha' : A 0 0 ≠ 0 := by simpa [a] using ha
    have hdet_formula : A.det = a * c - b * b := by
      simp [Matrix.det_fin_two, a, b, c, hsymm]
    rw [hdet_formula] at ht
    dsimp [a, b, c] at hdet_formula
    dsimp [a, b, c] at ht
    let P0 : Matrix (Fin 2) (Fin 2) K :=
      !![-b + t, (-b - t) / (2 * a * A.det); a, 1 / (2 * A.det)]
    have hP0det_eq : P0.det = t / A.det := by
      simp [P0, Matrix.det_fin_two]
      field_simp [ha, hA_det, htwo]
      ring
    have hP0det : P0.det ≠ 0 := by
      rw [hP0det_eq]
      exact div_ne_zero ht_ne hA_det
    let P : Matrix.GeneralLinearGroup (Fin 2) K :=
      Matrix.GeneralLinearGroup.mk'' P0 (isUnit_iff_ne_zero.mpr hP0det)
    refine ⟨P, ?_⟩
    change P0ᵀ * A * P0 = splitHyperbolicPlaneGramMatrix K
    ext i j
    fin_cases i <;> fin_cases j
    all_goals simp [P0, splitHyperbolicPlaneGramMatrix, Matrix.mul_apply,
      Fin.sum_univ_two, a, b, hsymm]
    · linear_combination A 0 0 * ht
    · field_simp [ha', hA_det, htwo]
      rw [hdet_formula]
      linear_combination -ht
    · field_simp [ha', hA_det, htwo]
      rw [hdet_formula]
      linear_combination -ht
    · field_simp [ha', hA_det, htwo]
      linear_combination ht

/-- A split nonsingular binary Gram matrix over a finite field has
orthogonal-group order `2 * (|K| - 1)`. -/
theorem natCard_binaryFiniteGramOrthogonalGroup_of_neg_det_eq_sq
    {K : Type*} [Field K] [Finite K]
    (A : Matrix (Fin 2) (Fin 2) K) (hA_symm : A.IsSymm)
    (hA_det : A.det ≠ 0) (hchar : ringChar K ≠ 2)
    (t : K) (ht : t * t = -A.det) :
    Nat.card (finiteGramOrthogonalGroup A) = 2 * (Nat.card K - 1) := by
  obtain ⟨P, hP⟩ :=
    exists_binaryGram_congr_splitHyperbolicPlane_of_neg_det_eq_sq
      A hA_symm hA_det hchar t ht
  exact natCard_finiteGramOrthogonalGroup_eq_splitHyperbolicPlane_of_congr
    A P hP hchar

private lemma quadraticAlgebra_algebraNorm_eq_norm
    {K : Type*} [Field K] (d : K)
    [Fact (∀ r : K, r ^ 2 ≠ d + 0 * r)]
    (z : QuadraticAlgebra K d 0) :
    Algebra.norm K z = QuadraticAlgebra.norm z := by
  rw [Algebra.norm_apply, ← QuadraticAlgebra.det_toLinearMap_eq_norm z]
  congr 1

private noncomputable def quadraticAlgebraUnitsNorm
    {K : Type*} [Field K] (d : K)
    [Fact (∀ r : K, r ^ 2 ≠ d + 0 * r)] :
    (QuadraticAlgebra K d 0)ˣ →* Kˣ :=
  Units.map (Algebra.norm K)

/-- The norm-one elements `x + yω` in the quadratic algebra with `ω² = d`.
Concretely, these are the pairs satisfying `x² - d y² = 1`. -/
def quadraticNormOne (K : Type*) [CommRing K] (d : K) :=
  {z : QuadraticAlgebra K d 0 // QuadraticAlgebra.norm z = 1}

private noncomputable def quadraticNormOneEquivUnitsNormKer
    {K : Type*} [Field K] (d : K)
    [Fact (∀ r : K, r ^ 2 ≠ d + 0 * r)] :
    quadraticNormOne K d ≃ (quadraticAlgebraUnitsNorm d).ker where
  toFun z :=
    ⟨Units.mk0 z.1 (by
      intro hz
      have h01 : (0 : K) = 1 := by simpa [hz] using z.2
      exact zero_ne_one h01), by
      apply Units.ext
      simpa [quadraticAlgebraUnitsNorm,
        quadraticAlgebra_algebraNorm_eq_norm] using z.2⟩
  invFun u :=
    ⟨(u.1 : QuadraticAlgebra K d 0), by
      have hu := congrArg Units.val u.2
      simpa [quadraticAlgebraUnitsNorm,
        quadraticAlgebra_algebraNorm_eq_norm] using hu⟩
  left_inv z := Subtype.ext rfl
  right_inv u := Subtype.ext (Units.ext rfl)

/-- For a nonsquare `d` over a finite field, the norm-one elements in the
quadratic extension `K(√d)` have cardinality `|K| + 1`. -/
theorem natCard_quadraticNormOne
    {K : Type*} [Field K] [Finite K]
    (d : K) (hd : ∀ r : K, r ^ 2 ≠ d) :
    Nat.card (quadraticNormOne K d) = Nat.card K + 1 := by
  letI : Fact (∀ r : K, r ^ 2 ≠ d + 0 * r) := ⟨by simpa using hd⟩
  letI : Finite (QuadraticAlgebra K d 0) :=
    Finite.of_injective (QuadraticAlgebra.equivProd d 0)
      (QuadraticAlgebra.equivProd d 0).injective
  let f := quadraticAlgebraUnitsNorm d
  let e : quadraticNormOne K d ≃ f.ker :=
    quadraticNormOneEquivUnitsNormKer d
  have hsurj : Function.Surjective f := FiniteField.unitsMap_norm_surjective K _
  have hcard := f.ker.card_mul_index
  rw [Subgroup.index_ker, f.range_eq_top_of_surjective hsurj] at hcard
  simp only [Nat.card_units] at hcard
  simp at hcard
  rw [Nat.card_units K] at hcard
  have hqa : Nat.card (QuadraticAlgebra K d 0) = Nat.card K * Nat.card K :=
    Nat.card_congr (QuadraticAlgebra.equivProd d 0) |>.trans (Nat.card_prod K K)
  rw [hqa] at hcard
  have hq : 1 < Nat.card K := Finite.one_lt_card
  have hfactor : Nat.card K * Nat.card K - 1 =
      (Nat.card K - 1) * (Nat.card K + 1) := by
    simpa [pow_two, mul_comm] using sq_tsub_sq (Nat.card K) 1
  rw [hfactor] at hcard
  have hker : Nat.card f.ker = Nat.card K + 1 := by
    apply Nat.eq_of_mul_eq_mul_left (n := Nat.card K - 1) (by omega)
    simpa [mul_comm] using hcard
  rw [Nat.card_congr e, hker]

/-- The fiber of the quadratic norm `x² - d y²` over `c`. -/
def quadraticNormFiber (K : Type*) [CommRing K] (d c : K) :=
  {z : QuadraticAlgebra K d 0 // QuadraticAlgebra.norm z = c}

/-- For a nonsquare `d` and nonzero `c`, translation between fibers of the
surjective finite-field norm identifies the norm-`c` fiber with the norm-one
fiber. -/
noncomputable def quadraticNormFiberEquivNormOne
    {K : Type*} [Field K] [Finite K]
    (d : K) (hd : ∀ r : K, r ^ 2 ≠ d) (c : K) (hc : c ≠ 0) :
    quadraticNormFiber K d c ≃ quadraticNormOne K d := by
  letI : Fact (∀ r : K, r ^ 2 ≠ d + 0 * r) := ⟨by simpa using hd⟩
  letI : Finite (QuadraticAlgebra K d 0) :=
    Finite.of_injective (QuadraticAlgebra.equivProd d 0)
      (QuadraticAlgebra.equivProd d 0).injective
  let f := quadraticAlgebraUnitsNorm d
  let cu : Kˣ := Units.mk0 c hc
  let eUnits : quadraticNormFiber K d c ≃ f ⁻¹' {cu} :=
    { toFun := fun z =>
        ⟨Units.mk0 z.1 (by
          intro hz
          have h0c : (0 : K) = c := by simpa [hz] using z.2
          exact hc h0c.symm), by
          change f (Units.mk0 z.1 _) = cu
          apply Units.ext
          simpa [f, cu, quadraticAlgebraUnitsNorm,
            quadraticAlgebra_algebraNorm_eq_norm] using z.2⟩
      invFun := fun u =>
        ⟨(u.1.1 : QuadraticAlgebra K d 0), by
          have hu := u.2
          change f u.1 = cu at hu
          have hu' := congrArg Units.val hu
          simpa [f, cu, quadraticAlgebraUnitsNorm,
            quadraticAlgebra_algebraNorm_eq_norm] using hu'⟩
      left_inv := fun z => Subtype.ext rfl
      right_inv := fun u => Subtype.ext (Units.ext rfl) }
  have hsurj : Function.Surjective f := FiniteField.unitsMap_norm_surjective K _
  exact eUnits.trans <|
    (f.fiberEquivKerOfSurjective hsurj cu).trans
      (quadraticNormOneEquivUnitsNormKer d).symm

/-- Every nonzero norm fiber of a nonsplit quadratic extension has
cardinality `|K| + 1`. -/
theorem natCard_quadraticNormFiber_of_ne_zero
    {K : Type*} [Field K] [Finite K]
    (d : K) (hd : ∀ r : K, r ^ 2 ≠ d) (c : K) (hc : c ≠ 0) :
    Nat.card (quadraticNormFiber K d c) = Nat.card K + 1 := by
  rw [Nat.card_congr (quadraticNormFiberEquivNormOne d hd c hc)]
  exact natCard_quadraticNormOne d hd

lemma quadraticNorm_eq_zero_iff_of_nonsquare
    {K : Type*} [Field K] (d : K) (hd : ∀ r : K, r ^ 2 ≠ d)
    (z : QuadraticAlgebra K d 0) :
    QuadraticAlgebra.norm z = 0 ↔ z = 0 := by
  letI : Fact (∀ r : K, r ^ 2 ≠ d + 0 * r) := ⟨by simpa using hd⟩
  constructor
  · intro hz
    by_contra hz0
    have hu := Units.ne_zero
      (quadraticAlgebraUnitsNorm d (Units.mk0 z hz0))
    apply hu
    simpa [quadraticAlgebraUnitsNorm,
      quadraticAlgebra_algebraNorm_eq_norm] using hz
  · rintro rfl
    simp [QuadraticAlgebra.norm_def]

/-- The zero norm fiber of an anisotropic binary norm is a singleton. -/
theorem natCard_quadraticNormFiber_zero
    {K : Type*} [Field K] [Finite K]
    (d : K) (hd : ∀ r : K, r ^ 2 ≠ d) :
    Nat.card (quadraticNormFiber K d 0) = 1 := by
  let e : quadraticNormFiber K d 0 ≃ Unit :=
    { toFun := fun _ => Unit.unit
      invFun := fun _ => ⟨0, by simp [QuadraticAlgebra.norm_def]⟩
      left_inv := fun z => Subtype.ext <|
        ((quadraticNorm_eq_zero_iff_of_nonsquare d hd z.1).mp z.2).symm
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e]
  simp

/-- The fiber of the binary sum-of-squares map `(x,y) ↦ x²+y²`. -/
def binarySumSquaresFiber (K : Type*) [CommRing K] (c : K) :=
  {z : K × K // z.1 ^ 2 + z.2 ^ 2 = c}

/-- Sum of two squares is the quadratic norm `x²-(-1)y²`. -/
noncomputable def binarySumSquaresFiberEquivQuadraticNormFiber
    {K : Type*} [CommRing K] (c : K) :
    binarySumSquaresFiber K c ≃ quadraticNormFiber K (-1) c where
  toFun z := ⟨⟨z.1.1, z.1.2⟩, by
    simpa [QuadraticAlgebra.norm_def, pow_two] using z.2⟩
  invFun z := ⟨(z.1.re, z.1.im), by
    simpa [QuadraticAlgebra.norm_def, pow_two] using z.2⟩
  left_inv z := Subtype.ext rfl
  right_inv z := Subtype.ext rfl

/-- When `-1` is nonsquare, every nonzero sum-of-squares fiber has
cardinality `|K|+1`. -/
theorem natCard_binarySumSquaresFiber_of_neg_one_nonsquare_ne_zero
    {K : Type*} [Field K] [Finite K]
    (hneg : ∀ r : K, r ^ 2 ≠ -1) (c : K) (hc : c ≠ 0) :
    Nat.card (binarySumSquaresFiber K c) = Nat.card K + 1 := by
  rw [Nat.card_congr (binarySumSquaresFiberEquivQuadraticNormFiber c)]
  exact natCard_quadraticNormFiber_of_ne_zero (-1) hneg c hc

/-- When `-1` is nonsquare, the zero sum-of-squares fiber is a singleton. -/
theorem natCard_binarySumSquaresFiber_zero_of_neg_one_nonsquare
    {K : Type*} [Field K] [Finite K]
    (hneg : ∀ r : K, r ^ 2 ≠ -1) :
    Nat.card (binarySumSquaresFiber K 0) = 1 := by
  rw [Nat.card_congr (binarySumSquaresFiberEquivQuadraticNormFiber 0)]
  exact natCard_quadraticNormFiber_zero (-1) hneg

/-- The fiber of the split binary product map `(u,v) ↦ u*v`. -/
def splitProductFiber (K : Type*) [CommRing K] (c : K) :=
  {z : K × K // z.1 * z.2 = c}

/-- A nonzero product fiber is parameterized by its first, necessarily
nonzero, coordinate. -/
noncomputable def splitProductFiberEquivUnits
    {K : Type*} [Field K] (c : K) (hc : c ≠ 0) :
    splitProductFiber K c ≃ Kˣ where
  toFun z := Units.mk0 z.1.1 (by
    intro hx
    apply hc
    simpa [hx] using z.2.symm)
  invFun u := ⟨((u : K), c / (u : K)), by field_simp⟩
  left_inv z := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · have hx : z.1.1 ≠ 0 := by
        intro hx
        apply hc
        simpa [hx] using z.2.symm
      dsimp
      field_simp [hx]
      exact z.2.symm
  right_inv u := Units.ext rfl

/-- Every nonzero fiber of the split product map has cardinality `|K|-1`. -/
theorem natCard_splitProductFiber_of_ne_zero
    {K : Type*} [Field K] [Finite K] (c : K) (hc : c ≠ 0) :
    Nat.card (splitProductFiber K c) = Nat.card K - 1 := by
  rw [Nat.card_congr (splitProductFiberEquivUnits c hc), Nat.card_units]

/-- The zero product fiber is the union of the two coordinate axes, encoded
as one full axis and the nonzero points of the other. -/
noncomputable def splitProductZeroFiberEquiv
    {K : Type*} [Field K] : splitProductFiber K 0 ≃ K ⊕ Kˣ := by
  classical
  exact
    { toFun := fun z => if hx : z.1.1 = 0 then Sum.inl z.1.2
        else Sum.inr (Units.mk0 z.1.1 hx)
      invFun := fun z => match z with
        | Sum.inl y => ⟨(0, y), zero_mul y⟩
        | Sum.inr u => ⟨((u : K), 0), mul_zero (u : K)⟩
      left_inv := fun z => by
        by_cases hx : z.1.1 = 0
        · apply Subtype.ext
          ext <;> simp [hx]
        · have hy : z.1.2 = 0 := (mul_eq_zero.mp z.2).resolve_left hx
          apply Subtype.ext
          ext <;> simp [hx, hy]
      right_inv := fun z => by
        cases z with
        | inl y => simp
        | inr u => simp [Units.ne_zero] }

/-- The zero fiber of the split product map has cardinality `2|K|-1`. -/
theorem natCard_splitProductFiber_zero
    {K : Type*} [Field K] [Finite K] :
    Nat.card (splitProductFiber K 0) = 2 * Nat.card K - 1 := by
  rw [Nat.card_congr (splitProductZeroFiberEquiv (K := K)), Nat.card_sum,
    Nat.card_units]
  have hq : 0 < Nat.card K := Nat.card_pos
  omega

/-- If `t²=-1`, the change of variables
`(x,y) ↦ (x+t*y, x-t*y)` turns a sum of two squares into a product. -/
noncomputable def binarySumSquaresFiberEquivSplitProduct
    {K : Type*} [Field K] (hchar : ringChar K ≠ 2)
    (t : K) (ht : t ^ 2 = -1) (c : K) :
    binarySumSquaresFiber K c ≃ splitProductFiber K c := by
  have htwo : (2 : K) ≠ 0 := Ring.two_ne_zero hchar
  have ht0 : t ≠ 0 := by
    intro ht0
    rw [ht0] at ht
    simp at ht
  exact
    { toFun := fun z => ⟨(z.1.1 + t * z.1.2, z.1.1 - t * z.1.2), by
        calc
          (z.1.1 + t * z.1.2) * (z.1.1 - t * z.1.2) =
              z.1.1 ^ 2 - t ^ 2 * z.1.2 ^ 2 := by ring
          _ = z.1.1 ^ 2 + z.1.2 ^ 2 := by rw [ht]; ring
          _ = c := z.2 ⟩
      invFun := fun z =>
        ⟨((z.1.1 + z.1.2) / 2, (z.1.1 - z.1.2) / (2 * t)), by
          calc
            ((z.1.1 + z.1.2) / 2) ^ 2 +
                ((z.1.1 - z.1.2) / (2 * t)) ^ 2 = z.1.1 * z.1.2 := by
              field_simp [htwo, ht0]
              rw [ht]
              ring
            _ = c := z.2 ⟩
      left_inv := fun z => by
        apply Subtype.ext
        apply Prod.ext
        · dsimp
          field_simp [htwo]
          ring
        · dsimp
          field_simp [htwo, ht0]
          ring
      right_inv := fun z => by
        apply Subtype.ext
        apply Prod.ext
        · dsimp
          field_simp [htwo, ht0]
          ring
        · dsimp
          field_simp [htwo, ht0]
          ring }

/-- When `-1` is square, every nonzero sum-of-squares fiber has
cardinality `|K|-1`. -/
theorem natCard_binarySumSquaresFiber_of_neg_one_square_ne_zero
    {K : Type*} [Field K] [Finite K] (hchar : ringChar K ≠ 2)
    (t : K) (ht : t ^ 2 = -1) (c : K) (hc : c ≠ 0) :
    Nat.card (binarySumSquaresFiber K c) = Nat.card K - 1 := by
  rw [Nat.card_congr (binarySumSquaresFiberEquivSplitProduct hchar t ht c)]
  exact natCard_splitProductFiber_of_ne_zero c hc

/-- When `-1` is square, the zero sum-of-squares fiber has cardinality
`2|K|-1`. -/
theorem natCard_binarySumSquaresFiber_zero_of_neg_one_square
    {K : Type*} [Field K] [Finite K] (hchar : ringChar K ≠ 2)
    (t : K) (ht : t ^ 2 = -1) :
    Nat.card (binarySumSquaresFiber K 0) = 2 * Nat.card K - 1 := by
  rw [Nat.card_congr (binarySumSquaresFiberEquivSplitProduct hchar t ht 0)]
  exact natCard_splitProductFiber_zero

/-- The diagonal binary Gram matrix for the norm form `x² - d y²`. -/
def nonsplitBinaryGramMatrix (K : Type*) [CommRing K] (d : K) :
    Matrix (Fin 2) (Fin 2) K :=
  !![1, 0; 0, -d]

/-- Multiplication by `x + yω`, for `ω² = d`, in the basis `(1, ω)`. -/
def quadraticNormMatrix {K : Type*} [CommRing K] (d : K)
    (z : QuadraticAlgebra K d 0) : Matrix (Fin 2) (Fin 2) K :=
  !![z.re, d * z.im; z.im, z.re]

lemma quadraticNormMatrix_det
    {K : Type*} [CommRing K] (d : K) (z : QuadraticAlgebra K d 0) :
    (quadraticNormMatrix d z).det = QuadraticAlgebra.norm z := by
  simp [quadraticNormMatrix, QuadraticAlgebra.norm_def, Matrix.det_fin_two]

lemma quadraticNormMatrix_gram
    {K : Type*} [CommRing K] (d : K) (z : QuadraticAlgebra K d 0) :
    (quadraticNormMatrix d z)ᵀ * nonsplitBinaryGramMatrix K d *
        quadraticNormMatrix d z =
      !![QuadraticAlgebra.norm z, 0; 0, -d * QuadraticAlgebra.norm z] := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp [quadraticNormMatrix, nonsplitBinaryGramMatrix,
    QuadraticAlgebra.norm_def, Matrix.mul_apply, Fin.sum_univ_two]
  all_goals ring

/-- Binary Gram-preserving matrices with determinant one. The determinant
condition makes invertibility automatic over a field, but this subtype is
defined over any commutative ring for the norm-matrix equivalence below. -/
def determinantOneGramPreserver {K : Type*} [CommRing K]
    (A : Matrix (Fin 2) (Fin 2) K) :=
  {X : Matrix (Fin 2) (Fin 2) K // Xᵀ * A * X = A ∧ X.det = 1}

/-- Multiplication matrices identify norm-one elements with determinant-one
isometries of the binary norm form. This calculation is characteristic-free. -/
noncomputable def quadraticNormOneEquivDeterminantOneGramPreserver
    {K : Type*} [CommRing K] (d : K) :
    quadraticNormOne K d ≃
      determinantOneGramPreserver (nonsplitBinaryGramMatrix K d) where
  toFun z := ⟨quadraticNormMatrix d z.1, by
    constructor
    · rw [quadraticNormMatrix_gram, z.2]
      simp [nonsplitBinaryGramMatrix]
    · rw [quadraticNormMatrix_det, z.2]⟩
  invFun X := ⟨⟨X.1 0 0, X.1 1 0⟩, by
    have h00 := congrFun (congrFun X.2.1 0) 0
    simp [nonsplitBinaryGramMatrix, Matrix.mul_apply, Fin.sum_univ_two] at h00
    simp [QuadraticAlgebra.norm_def]
    ring_nf at h00 ⊢
    exact h00⟩
  left_inv z := by
    apply Subtype.ext
    rfl
  right_inv X := by
    apply Subtype.ext
    let a := X.1 0 0
    let b := X.1 0 1
    let c := X.1 1 0
    let e := X.1 1 1
    have h00 := congrFun (congrFun X.2.1 0) 0
    have h01 := congrFun (congrFun X.2.1 0) 1
    have hdet := X.2.2
    have hnorm : a * a - d * c * c = 1 := by
      simp [nonsplitBinaryGramMatrix, Matrix.mul_apply, Fin.sum_univ_two] at h00
      ring_nf at h00 ⊢
      linear_combination h00
    have hcross : a * b - d * c * e = 0 := by
      simp [nonsplitBinaryGramMatrix, Matrix.mul_apply, Fin.sum_univ_two] at h01
      ring_nf at h01 ⊢
      linear_combination h01
    have hdet' : a * e - b * c = 1 := by
      simpa [Matrix.det_fin_two, a, b, c, e] using hdet
    ext i j
    fin_cases i <;> fin_cases j
    · rfl
    · change d * c = b
      linear_combination -d * c * hdet' - a * hcross + b * hnorm
    · rfl
    · change a = e
      linear_combination -a * hdet' - c * hcross + e * hnorm

/-- The determinant-one isometries of an anisotropic binary norm form over a
finite field have cardinality `|K| + 1`. -/
theorem natCard_nonsplitBinaryDeterminantOneGramPreserver
    {K : Type*} [Field K] [Finite K]
    (d : K) (hd : ∀ r : K, r ^ 2 ≠ d) :
    Nat.card (determinantOneGramPreserver (nonsplitBinaryGramMatrix K d)) =
      Nat.card K + 1 := by
  rw [← Nat.card_congr (quadraticNormOneEquivDeterminantOneGramPreserver d)]
  exact natCard_quadraticNormOne d hd

/-- Reflection in the second coordinate of a binary norm form. -/
def nonsplitBinaryReflection (K : Type*) [CommRing K] :
    Matrix (Fin 2) (Fin 2) K :=
  !![1, 0; 0, -1]

lemma nonsplitBinaryReflection_det
    {K : Type*} [CommRing K] :
    (nonsplitBinaryReflection K).det = -1 := by
  simp [nonsplitBinaryReflection, Matrix.det_fin_two]

lemma nonsplitBinaryReflection_sq
    {K : Type*} [CommRing K] :
    nonsplitBinaryReflection K * nonsplitBinaryReflection K = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [nonsplitBinaryReflection, Matrix.mul_apply, Fin.sum_univ_two]

lemma nonsplitBinaryReflection_gram
    {K : Type*} [CommRing K] (d : K) :
    (nonsplitBinaryReflection K)ᵀ * nonsplitBinaryGramMatrix K d *
        nonsplitBinaryReflection K = nonsplitBinaryGramMatrix K d := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [nonsplitBinaryReflection, nonsplitBinaryGramMatrix,
      Matrix.mul_apply, Fin.sum_univ_two]

lemma binaryGramPreserver_det_eq_one_or_neg_one
    {K : Type*} [Field K] (d : K) (hd : d ≠ 0)
    (X : {X : Matrix (Fin 2) (Fin 2) K //
      Xᵀ * nonsplitBinaryGramMatrix K d * X = nonsplitBinaryGramMatrix K d}) :
    X.1.det = 1 ∨ X.1.det = -1 := by
  have hdet := congrArg Matrix.det X.2
  simp only [Matrix.det_mul, Matrix.det_transpose] at hdet
  have hgram : (nonsplitBinaryGramMatrix K d).det = -d := by
    simp [nonsplitBinaryGramMatrix, Matrix.det_fin_two]
  rw [hgram] at hdet
  have hsq : X.1.det * X.1.det = 1 := by
    apply (mul_left_cancel₀ (neg_ne_zero.mpr hd))
    linear_combination hdet
  have hfactor : (X.1.det - 1) * (X.1.det + 1) = 0 := by
    linear_combination hsq
  rcases mul_eq_zero.mp hfactor with h | h
  · left
    linear_combination h
  · right
    linear_combination h

lemma binaryGramPreserver_mul_reflection
    {K : Type*} [Field K] (d : K)
    (X : Matrix (Fin 2) (Fin 2) K)
    (hX : Xᵀ * nonsplitBinaryGramMatrix K d * X = nonsplitBinaryGramMatrix K d) :
    (X * nonsplitBinaryReflection K)ᵀ * nonsplitBinaryGramMatrix K d *
        (X * nonsplitBinaryReflection K) = nonsplitBinaryGramMatrix K d := by
  calc
    (X * nonsplitBinaryReflection K)ᵀ * nonsplitBinaryGramMatrix K d *
        (X * nonsplitBinaryReflection K) =
      (nonsplitBinaryReflection K)ᵀ *
        (Xᵀ * nonsplitBinaryGramMatrix K d * X) *
          nonsplitBinaryReflection K := by
            simp only [Matrix.transpose_mul]
            simp [Matrix.mul_assoc]
    _ = (nonsplitBinaryReflection K)ᵀ * nonsplitBinaryGramMatrix K d *
          nonsplitBinaryReflection K := by rw [hX]
    _ = nonsplitBinaryGramMatrix K d := nonsplitBinaryReflection_gram d

/-- A determinant-one binary isometry, optionally followed by the standard
reflection, is an arbitrary isometry of the binary norm form. -/
def determinantOnePreserverBoolToBinaryGramPreserver
    {K : Type*} [Field K] (d : K) :
    determinantOneGramPreserver (nonsplitBinaryGramMatrix K d) × Bool →
      {X : Matrix (Fin 2) (Fin 2) K //
        Xᵀ * nonsplitBinaryGramMatrix K d * X = nonsplitBinaryGramMatrix K d}
  | (X, false) => ⟨X.1, X.2.1⟩
  | (X, true) => ⟨X.1 * nonsplitBinaryReflection K,
      binaryGramPreserver_mul_reflection d X.1 X.2.1⟩

/-- Over a field of odd characteristic, every isometry of a nonsingular
binary norm form is uniquely a determinant-one isometry, optionally followed
by the standard reflection. -/
noncomputable def determinantOnePreserverBoolEquivBinaryGramPreserver
    {K : Type*} [Field K] (d : K) (hd : d ≠ 0) (hchar : ringChar K ≠ 2) :
    determinantOneGramPreserver (nonsplitBinaryGramMatrix K d) × Bool ≃
      {X : Matrix (Fin 2) (Fin 2) K //
        Xᵀ * nonsplitBinaryGramMatrix K d * X = nonsplitBinaryGramMatrix K d} := by
  classical
  apply Equiv.ofBijective (determinantOnePreserverBoolToBinaryGramPreserver d)
  constructor
  · rintro ⟨X, b⟩ ⟨Y, c⟩ h
    cases b <;> cases c
    · apply Prod.ext
      · apply Subtype.ext
        have hval := congrArg Subtype.val h
        change X.1 = Y.1 at hval
        exact hval
      · rfl
    · have hdet := congrArg (fun Z => Z.1.det) h
      simp [determinantOnePreserverBoolToBinaryGramPreserver,
        Matrix.det_mul, nonsplitBinaryReflection_det, X.2.2, Y.2.2] at hdet
      exfalso
      apply Ring.two_ne_zero hchar
      linear_combination hdet
    · have hdet := congrArg (fun Z => Z.1.det) h
      simp [determinantOnePreserverBoolToBinaryGramPreserver,
        Matrix.det_mul, nonsplitBinaryReflection_det, X.2.2, Y.2.2] at hdet
      exfalso
      apply Ring.two_ne_zero hchar
      linear_combination -hdet
    · apply Prod.ext
      · apply Subtype.ext
        have hval := congrArg Subtype.val h
        change X.1 * nonsplitBinaryReflection K =
          Y.1 * nonsplitBinaryReflection K at hval
        have := congrArg (fun Z => Z * nonsplitBinaryReflection K) hval
        simpa [Matrix.mul_assoc, nonsplitBinaryReflection_sq] using this
      · rfl
  · intro X
    rcases binaryGramPreserver_det_eq_one_or_neg_one d hd X with hdet | hdet
    · refine ⟨(⟨X.1, X.2, hdet⟩, false), ?_⟩
      rfl
    · let Y : determinantOneGramPreserver (nonsplitBinaryGramMatrix K d) :=
        ⟨X.1 * nonsplitBinaryReflection K, by
          constructor
          · exact binaryGramPreserver_mul_reflection d X.1 X.2
          · rw [Matrix.det_mul, hdet, nonsplitBinaryReflection_det]
            ring⟩
      refine ⟨(Y, true), ?_⟩
      apply Subtype.ext
      simp [determinantOnePreserverBoolToBinaryGramPreserver, Y,
        Matrix.mul_assoc, nonsplitBinaryReflection_sq]

/-- The orthogonal group of an anisotropic binary norm form over an odd finite
field has cardinality `2 * (|K| + 1)`. -/
theorem natCard_nonsplitBinaryFiniteGramOrthogonalGroup
    {K : Type*} [Field K] [Finite K]
    (d : K) (hd : ∀ r : K, r ^ 2 ≠ d) (hchar : ringChar K ≠ 2) :
    Nat.card (finiteGramOrthogonalGroup (nonsplitBinaryGramMatrix K d)) =
      2 * (Nat.card K + 1) := by
  have hd0 : d ≠ 0 := by
    intro hd0
    subst d
    exact hd 0 (by simp)
  rw [← Nat.card_congr (matrixPreserverEquivFiniteGramOrthogonalGroup
    (nonsplitBinaryGramMatrix K d) (by
      simpa [nonsplitBinaryGramMatrix, Matrix.det_fin_two] using hd0))]
  rw [← Nat.card_congr
    (determinantOnePreserverBoolEquivBinaryGramPreserver d hd0 hchar)]
  rw [Nat.card_prod, natCard_nonsplitBinaryDeterminantOneGramPreserver d hd]
  simp [Nat.mul_comm]

/-- Multiplying a Gram matrix by a nonzero scalar does not change its
orthogonal subgroup. -/
lemma finiteGramOrthogonalGroup_smul_eq
    {K : Type*} [Field K] (a : K) (A : Matrix (Fin n) (Fin n) K)
    (ha : a ≠ 0) :
    finiteGramOrthogonalGroup (a • A) = finiteGramOrthogonalGroup A := by
  ext X
  change X.1ᵀ * (a • A) * X.1 = a • A ↔ X.1ᵀ * A * X.1 = A
  have hsmul : X.1ᵀ * (a • A) * X.1 = a • (X.1ᵀ * A * X.1) := by
    rw [Matrix.mul_smul, Matrix.smul_mul]
  rw [hsmul]
  exact (smul_right_injective (Matrix (Fin n) (Fin n) K) ha).eq_iff

/-- A symmetric binary form with nonsquare negative determinant is explicitly
congruent to a nonzero scalar multiple of a nonsplit diagonal norm form. -/
theorem exists_binaryGram_congr_smul_nonsplitBinaryGramMatrix
    {K : Type*} [Field K]
    (A : Matrix (Fin 2) (Fin 2) K) (hA_symm : A.IsSymm)
    (hnegdet : ∀ r : K, r ^ 2 ≠ -A.det) :
    ∃ (a d : K) (P : Matrix.GeneralLinearGroup (Fin 2) K),
      a ≠ 0 ∧ (∀ r : K, r ^ 2 ≠ d) ∧
        (↑P : Matrix (Fin 2) (Fin 2) K)ᵀ * A *
          (↑P : Matrix (Fin 2) (Fin 2) K) =
            a • nonsplitBinaryGramMatrix K d := by
  let a := A 0 0
  let b := A 0 1
  let c := A 1 1
  have hsymm : A 1 0 = b := by simpa [b] using hA_symm.apply 0 1
  have hdet_formula : A.det = a * c - b * b := by
    simp [Matrix.det_fin_two, a, b, c, hsymm]
  have ha : a ≠ 0 := by
    intro ha
    apply hnegdet b
    rw [hdet_formula, ha]
    ring
  have ha00 : A 0 0 ≠ 0 := by simpa [a] using ha
  let d := -A.det / (a * a)
  have hd : ∀ r : K, r ^ 2 ≠ d := by
    intro r hr
    apply hnegdet (a * r)
    calc
      (a * r) ^ 2 = a ^ 2 * r ^ 2 := by ring
      _ = a ^ 2 * d := by rw [hr]
      _ = -A.det := by
        simp [d]
        field_simp [ha]
  let P0 : Matrix (Fin 2) (Fin 2) K :=
    !![1, -b / a; 0, 1]
  have hP0det : P0.det = 1 := by
    simp [P0, Matrix.det_fin_two]
  let P : Matrix.GeneralLinearGroup (Fin 2) K :=
    Matrix.GeneralLinearGroup.mk'' P0 (isUnit_iff_ne_zero.mpr (by simp [hP0det]))
  refine ⟨a, d, P, ha, hd, ?_⟩
  change P0ᵀ * A * P0 = a • nonsplitBinaryGramMatrix K d
  ext i j
  fin_cases i <;> fin_cases j
  · simp [P0, nonsplitBinaryGramMatrix, Matrix.mul_apply,
      Fin.sum_univ_two, a]
  · simp [P0, nonsplitBinaryGramMatrix, Matrix.mul_apply,
      Fin.sum_univ_two, a, b]
    field_simp [ha00]
    ring
  · simp [P0, nonsplitBinaryGramMatrix, Matrix.mul_apply,
      Fin.sum_univ_two, a, b, hsymm]
    field_simp [ha00]
    ring
  · simp [P0, nonsplitBinaryGramMatrix, Matrix.mul_apply,
      Fin.sum_univ_two, a, b, hsymm, d]
    rw [hdet_formula]
    simp [a, b, c]
    field_simp [ha00]
    ring

/-- Every nonsplit nonsingular symmetric binary form over an odd finite field
has orthogonal-group order `2 * (|K| + 1)`. -/
theorem natCard_binaryFiniteGramOrthogonalGroup_of_neg_det_nonsquare
    {K : Type*} [Field K] [Finite K]
    (A : Matrix (Fin 2) (Fin 2) K) (hA_symm : A.IsSymm)
    (hnegdet : ∀ r : K, r ^ 2 ≠ -A.det) (hchar : ringChar K ≠ 2) :
    Nat.card (finiteGramOrthogonalGroup A) = 2 * (Nat.card K + 1) := by
  obtain ⟨a, d, P, ha, hd, hP⟩ :=
    exists_binaryGram_congr_smul_nonsplitBinaryGramMatrix A hA_symm hnegdet
  calc
    Nat.card (finiteGramOrthogonalGroup A) =
        Nat.card (finiteGramOrthogonalGroup (a • nonsplitBinaryGramMatrix K d)) :=
      natCard_finiteGramOrthogonalGroup_eq_of_congr A
        (a • nonsplitBinaryGramMatrix K d) P hP
    _ = Nat.card (finiteGramOrthogonalGroup (nonsplitBinaryGramMatrix K d)) := by
      rw [finiteGramOrthogonalGroup_smul_eq a
        (nonsplitBinaryGramMatrix K d) ha]
    _ = 2 * (Nat.card K + 1) :=
      natCard_nonsplitBinaryFiniteGramOrthogonalGroup d hd hchar

/-- Every nonsingular binary quadratic form over an odd finite field
represents every nonzero scalar. -/
theorem exists_binaryVector_gramQuadraticValue_eq
    {K : Type*} [Field K] [Finite K]
    (A : Matrix (Fin 2) (Fin 2) K) (hA_symm : A.IsSymm)
    (hA_det : A.det ≠ 0) (hchar : ringChar K ≠ 2)
    (c : K) (hc : c ≠ 0) :
    ∃ v : Fin 2 → K, gramQuadraticValue A v = c := by
  by_cases hsplit : ∃ t : K, t * t = -A.det
  · obtain ⟨t, ht⟩ := hsplit
    obtain ⟨P, hP⟩ :=
      exists_binaryGram_congr_splitHyperbolicPlane_of_neg_det_eq_sq
        A hA_symm hA_det hchar t ht
    let w : Fin 2 → K := ![1, c / 2]
    refine ⟨(↑P : Matrix (Fin 2) (Fin 2) K) *ᵥ w, ?_⟩
    rw [gramQuadraticValue_mulVec_of_congr A
      (splitHyperbolicPlaneGramMatrix K) P hP]
    simp [gramQuadraticValue, splitHyperbolicPlaneGramMatrix, w,
      Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    field_simp [Ring.two_ne_zero hchar]
    norm_num
  · have hneg : ∀ r : K, r ^ 2 ≠ -A.det := by
      intro r hr
      exact hsplit ⟨r, by simpa [pow_two] using hr⟩
    obtain ⟨a, d, P, ha, hd, hP⟩ :=
      exists_binaryGram_congr_smul_nonsplitBinaryGramMatrix A hA_symm hneg
    have hca : c / a ≠ 0 := div_ne_zero hc ha
    have hcard : Nat.card (quadraticNormFiber K d (c / a)) = Nat.card K + 1 :=
      natCard_quadraticNormFiber_of_ne_zero d hd (c / a) hca
    have hcard_pos : 0 < Nat.card (quadraticNormFiber K d (c / a)) := by
      rw [hcard]
      omega
    let z : quadraticNormFiber K d (c / a) :=
      Classical.choice (Nat.card_pos_iff.mp hcard_pos).1
    let w : Fin 2 → K := ![z.1.re, z.1.im]
    refine ⟨(↑P : Matrix (Fin 2) (Fin 2) K) *ᵥ w, ?_⟩
    rw [gramQuadraticValue_mulVec_of_congr A
      (a • nonsplitBinaryGramMatrix K d) P hP]
    have hz : z.1.re ^ 2 - d * z.1.im ^ 2 = c / a := by
      simpa [QuadraticAlgebra.norm_def, pow_two, mul_assoc] using z.2
    calc
      gramQuadraticValue (a • nonsplitBinaryGramMatrix K d) w =
          a * (z.1.re ^ 2 - d * z.1.im ^ 2) := by
        simp [gramQuadraticValue, nonsplitBinaryGramMatrix, w,
          Matrix.mulVec, dotProduct, Fin.sum_univ_two]
        ring
      _ = a * (c / a) := by rw [hz]
      _ = c := by field_simp [ha]

/-- If `d=t^2`, the quadratic norm `x^2-dy^2` splits as a product. -/
noncomputable def quadraticNormFiberEquivSplitProduct
    {K : Type*} [Field K] (hchar : ringChar K ≠ 2)
    (d : K) (hd : d ≠ 0) (t : K) (ht : t ^ 2 = d) (c : K) :
    quadraticNormFiber K d c ≃ splitProductFiber K c := by
  have htwo : (2 : K) ≠ 0 := Ring.two_ne_zero hchar
  have ht0 : t ≠ 0 := by
    intro ht0
    apply hd
    simpa [ht0] using ht.symm
  exact
    { toFun := fun z =>
        ⟨(z.1.re + t * z.1.im, z.1.re - t * z.1.im), by
          calc
            (z.1.re + t * z.1.im) * (z.1.re - t * z.1.im) =
                z.1.re ^ 2 - t ^ 2 * z.1.im ^ 2 := by ring
            _ = QuadraticAlgebra.norm z.1 := by
              rw [ht]
              simp [QuadraticAlgebra.norm_def, pow_two]
              ring
            _ = c := z.2 ⟩
      invFun := fun z =>
        ⟨⟨(z.1.1 + z.1.2) / 2, (z.1.1 - z.1.2) / (2 * t)⟩, by
          simp only [QuadraticAlgebra.norm_def, zero_mul, add_zero]
          calc
            ((z.1.1 + z.1.2) / 2) * ((z.1.1 + z.1.2) / 2) -
                d * ((z.1.1 - z.1.2) / (2 * t)) *
                  ((z.1.1 - z.1.2) / (2 * t)) =
                z.1.1 * z.1.2 := by
              field_simp [htwo, ht0]
              rw [← ht]
              ring
            _ = c := z.2 ⟩
      left_inv := fun z => by
        apply Subtype.ext
        apply QuadraticAlgebra.ext <;> dsimp
        · field_simp [htwo]
          ring
        · field_simp [htwo, ht0]
          ring
      right_inv := fun z => by
        apply Subtype.ext
        apply Prod.ext <;> dsimp
        · field_simp [htwo, ht0]
          ring
        · field_simp [htwo, ht0]
          ring }

theorem natCard_quadraticNormFiber_of_square_ne_zero
    {K : Type*} [Field K] [Finite K] (hchar : ringChar K ≠ 2)
    (d : K) (hd : d ≠ 0) (t : K) (ht : t ^ 2 = d)
    (c : K) (hc : c ≠ 0) :
    Nat.card (quadraticNormFiber K d c) = Nat.card K - 1 := by
  rw [Nat.card_congr
    (quadraticNormFiberEquivSplitProduct hchar d hd t ht c)]
  exact natCard_splitProductFiber_of_ne_zero c hc

theorem natCard_quadraticNormFiber_zero_of_square
    {K : Type*} [Field K] [Finite K] (hchar : ringChar K ≠ 2)
    (d : K) (hd : d ≠ 0) (t : K) (ht : t ^ 2 = d) :
    Nat.card (quadraticNormFiber K d 0) = 2 * Nat.card K - 1 := by
  rw [Nat.card_congr
    (quadraticNormFiberEquivSplitProduct hchar d hd t ht 0)]
  exact natCard_splitProductFiber_zero

/-- The fiber of the weighted binary sum `d*x^2+y^2`. -/
def weightedBinarySumSquaresFiber
    (K : Type*) [CommRing K] (d c : K) :=
  {z : K × K // d * z.1 ^ 2 + z.2 ^ 2 = c}

noncomputable def weightedBinarySumSquaresFiberEquivQuadraticNormFiber
    {K : Type*} [CommRing K] (d c : K) :
    weightedBinarySumSquaresFiber K d c ≃
      quadraticNormFiber K (-d) c where
  toFun z := ⟨⟨z.1.2, z.1.1⟩, by
    simp only [QuadraticAlgebra.norm_def, zero_mul, add_zero]
    linear_combination z.2⟩
  invFun z := ⟨(z.1.im, z.1.re), by
    have hz := z.2
    simp only [QuadraticAlgebra.norm_def, zero_mul, add_zero] at hz
    linear_combination hz⟩
  left_inv z := Subtype.ext rfl
  right_inv z := Subtype.ext rfl

theorem natCard_weightedBinarySumSquaresFiber_of_neg_d_nonsquare_ne_zero
    {K : Type*} [Field K] [Finite K] (d : K)
    (hneg : ∀ r : K, r ^ 2 ≠ -d) (c : K) (hc : c ≠ 0) :
    Nat.card (weightedBinarySumSquaresFiber K d c) = Nat.card K + 1 := by
  rw [Nat.card_congr
    (weightedBinarySumSquaresFiberEquivQuadraticNormFiber d c)]
  exact natCard_quadraticNormFiber_of_ne_zero (-d) hneg c hc

theorem natCard_weightedBinarySumSquaresFiber_zero_of_neg_d_nonsquare
    {K : Type*} [Field K] [Finite K] (d : K)
    (hneg : ∀ r : K, r ^ 2 ≠ -d) :
    Nat.card (weightedBinarySumSquaresFiber K d 0) = 1 := by
  rw [Nat.card_congr
    (weightedBinarySumSquaresFiberEquivQuadraticNormFiber d 0)]
  exact natCard_quadraticNormFiber_zero (-d) hneg

theorem natCard_weightedBinarySumSquaresFiber_of_neg_d_square_ne_zero
    {K : Type*} [Field K] [Finite K] (hchar : ringChar K ≠ 2)
    (d : K) (hd : d ≠ 0) (t : K) (ht : t ^ 2 = -d)
    (c : K) (hc : c ≠ 0) :
    Nat.card (weightedBinarySumSquaresFiber K d c) = Nat.card K - 1 := by
  rw [Nat.card_congr
    (weightedBinarySumSquaresFiberEquivQuadraticNormFiber d c)]
  exact natCard_quadraticNormFiber_of_square_ne_zero hchar (-d)
    (neg_ne_zero.mpr hd) t ht c hc

theorem natCard_weightedBinarySumSquaresFiber_zero_of_neg_d_square
    {K : Type*} [Field K] [Finite K] (hchar : ringChar K ≠ 2)
    (d : K) (hd : d ≠ 0) (t : K) (ht : t ^ 2 = -d) :
    Nat.card (weightedBinarySumSquaresFiber K d 0) =
      2 * Nat.card K - 1 := by
  rw [Nat.card_congr
    (weightedBinarySumSquaresFiberEquivQuadraticNormFiber d 0)]
  exact natCard_quadraticNormFiber_zero_of_square hchar (-d)
    (neg_ne_zero.mpr hd) t ht

lemma exists_sq_eq_neg_mul_of_neg_one_nonsquare_of_nonsquare
    {K : Type*} [Field K] [Finite K]
    (d : K) (hd0 : d ≠ 0) (hd : ∀ r : K, r ^ 2 ≠ d)
    (hneg : ∀ r : K, r ^ 2 ≠ -1) :
    ∃ t : K, t ^ 2 = -d := by
  classical
  letI : Fintype K := Fintype.ofFinite K
  have hnsq_neg_one : ¬ IsSquare (-1 : K) := by
    rintro ⟨r, hr⟩
    exact hneg r (by simpa [pow_two] using hr.symm)
  have hnsq_d : ¬ IsSquare d := by
    rintro ⟨r, hr⟩
    exact hd r (by simpa [pow_two] using hr.symm)
  have hchar_neg_one : quadraticChar K (-1) = -1 :=
    quadraticChar_neg_one_iff_not_isSquare.mpr hnsq_neg_one
  have hchar_d : quadraticChar K d = -1 :=
    quadraticChar_neg_one_iff_not_isSquare.mpr hnsq_d
  have hchar_neg_d : quadraticChar K (-d) = 1 := by
    rw [show -d = (-1 : K) * d by ring, map_mul, hchar_neg_one, hchar_d]
    norm_num
  have hsquare : IsSquare (-d) :=
    (quadraticChar_one_iff_isSquare (neg_ne_zero.mpr hd0)).mp hchar_neg_d
  rcases hsquare with ⟨t, ht⟩
  exact ⟨t, by simpa [pow_two] using ht.symm⟩

/-- The block diagonal matrix with two copies of the same binary block. -/
def binaryPairMatrixBlock
    {K : Type*} [Field K] (Y : Matrix (Fin 2) (Fin 2) K) :
    Matrix (Fin 4) (Fin 4) K :=
  !![Y 0 0, Y 0 1, 0, 0;
    Y 1 0, Y 1 1, 0, 0;
    0, 0, Y 0 0, Y 0 1;
    0, 0, Y 1 0, Y 1 1]

lemma binaryPairMatrixBlock_mul
    {K : Type*} [Field K]
    (Y Z : Matrix (Fin 2) (Fin 2) K) :
    binaryPairMatrixBlock Y * binaryPairMatrixBlock Z =
      binaryPairMatrixBlock (Y * Z) := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp [binaryPairMatrixBlock, Matrix.mul_apply,
    Fin.sum_univ_four, Fin.sum_univ_two]

lemma binaryPairMatrixBlock_one
    {K : Type*} [Field K] :
    binaryPairMatrixBlock (1 : Matrix (Fin 2) (Fin 2) K) =
      (1 : Matrix (Fin 4) (Fin 4) K) := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp [binaryPairMatrixBlock]

/-- The invertible paired binary block associated to an invertible binary
matrix. -/
noncomputable def binaryPairGeneralLinearBlock
    {K : Type*} [Field K] (Y : Matrix.GeneralLinearGroup (Fin 2) K) :
    Matrix.GeneralLinearGroup (Fin 4) K := by
  let M := binaryPairMatrixBlock (Y : Matrix (Fin 2) (Fin 2) K)
  let N := binaryPairMatrixBlock
    (↑(Y⁻¹) : Matrix (Fin 2) (Fin 2) K)
  refine ⟨M, N, ?_, ?_⟩
  · rw [show M * N = binaryPairMatrixBlock
        ((Y : Matrix (Fin 2) (Fin 2) K) *
          (↑(Y⁻¹) : Matrix (Fin 2) (Fin 2) K)) by
      exact binaryPairMatrixBlock_mul _ _]
    rw [← Matrix.GeneralLinearGroup.coe_mul]
    simp [binaryPairMatrixBlock_one]
  · rw [show N * M = binaryPairMatrixBlock
        ((↑(Y⁻¹) : Matrix (Fin 2) (Fin 2) K) *
          (Y : Matrix (Fin 2) (Fin 2) K)) by
      exact binaryPairMatrixBlock_mul _ _]
    rw [← Matrix.GeneralLinearGroup.coe_mul]
    simp [binaryPairMatrixBlock_one]

@[simp] lemma binaryPairGeneralLinearBlock_coe
    {K : Type*} [Field K] (Y : Matrix.GeneralLinearGroup (Fin 2) K) :
    (binaryPairGeneralLinearBlock Y : Matrix (Fin 4) (Fin 4) K) =
      binaryPairMatrixBlock (Y : Matrix (Fin 2) (Fin 2) K) := by
  simp [binaryPairGeneralLinearBlock]

/-- The block diagonal matrix with three copies of the same binary block. -/
def binaryTripleMatrixBlock
    {K : Type*} [Field K] (Y : Matrix (Fin 2) (Fin 2) K) :
    Matrix (Fin 6) (Fin 6) K :=
  !![Y 0 0, Y 0 1, 0, 0, 0, 0;
    Y 1 0, Y 1 1, 0, 0, 0, 0;
    0, 0, Y 0 0, Y 0 1, 0, 0;
    0, 0, Y 1 0, Y 1 1, 0, 0;
    0, 0, 0, 0, Y 0 0, Y 0 1;
    0, 0, 0, 0, Y 1 0, Y 1 1]

set_option maxHeartbeats 800000 in
lemma binaryTripleMatrixBlock_mul
    {K : Type*} [Field K]
    (Y Z : Matrix (Fin 2) (Fin 2) K) :
    binaryTripleMatrixBlock Y * binaryTripleMatrixBlock Z =
      binaryTripleMatrixBlock (Y * Z) := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp [binaryTripleMatrixBlock, Matrix.mul_apply,
    Fin.sum_univ_six, Fin.sum_univ_two]

lemma binaryTripleMatrixBlock_one
    {K : Type*} [Field K] :
    binaryTripleMatrixBlock (1 : Matrix (Fin 2) (Fin 2) K) =
      (1 : Matrix (Fin 6) (Fin 6) K) := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp [binaryTripleMatrixBlock]

/-- The invertible triple binary block associated to an invertible binary
matrix. -/
noncomputable def binaryTripleGeneralLinearBlock
    {K : Type*} [Field K] (Y : Matrix.GeneralLinearGroup (Fin 2) K) :
    Matrix.GeneralLinearGroup (Fin 6) K := by
  let M := binaryTripleMatrixBlock (Y : Matrix (Fin 2) (Fin 2) K)
  let N := binaryTripleMatrixBlock
    (↑(Y⁻¹) : Matrix (Fin 2) (Fin 2) K)
  refine ⟨M, N, ?_, ?_⟩
  · rw [show M * N = binaryTripleMatrixBlock
        ((Y : Matrix (Fin 2) (Fin 2) K) *
          (↑(Y⁻¹) : Matrix (Fin 2) (Fin 2) K)) by
      exact binaryTripleMatrixBlock_mul _ _]
    rw [← Matrix.GeneralLinearGroup.coe_mul]
    simp [binaryTripleMatrixBlock_one]
  · rw [show N * M = binaryTripleMatrixBlock
        ((↑(Y⁻¹) : Matrix (Fin 2) (Fin 2) K) *
          (Y : Matrix (Fin 2) (Fin 2) K)) by
      exact binaryTripleMatrixBlock_mul _ _]
    rw [← Matrix.GeneralLinearGroup.coe_mul]
    simp [binaryTripleMatrixBlock_one]

@[simp] lemma binaryTripleGeneralLinearBlock_coe
    {K : Type*} [Field K] (Y : Matrix.GeneralLinearGroup (Fin 2) K) :
    (binaryTripleGeneralLinearBlock Y : Matrix (Fin 6) (Fin 6) K) =
      binaryTripleMatrixBlock (Y : Matrix (Fin 2) (Fin 2) K) := by
  simp [binaryTripleGeneralLinearBlock]

/-- The block diagonal matrix with two copies of the same quaternary block. -/
def quaternaryPairMatrixBlock
    {K : Type*} [Field K] (Y : Matrix (Fin 4) (Fin 4) K) :
    Matrix (Fin 8) (Fin 8) K :=
  !![Y 0 0, Y 0 1, Y 0 2, Y 0 3, 0, 0, 0, 0;
    Y 1 0, Y 1 1, Y 1 2, Y 1 3, 0, 0, 0, 0;
    Y 2 0, Y 2 1, Y 2 2, Y 2 3, 0, 0, 0, 0;
    Y 3 0, Y 3 1, Y 3 2, Y 3 3, 0, 0, 0, 0;
    0, 0, 0, 0, Y 0 0, Y 0 1, Y 0 2, Y 0 3;
    0, 0, 0, 0, Y 1 0, Y 1 1, Y 1 2, Y 1 3;
    0, 0, 0, 0, Y 2 0, Y 2 1, Y 2 2, Y 2 3;
    0, 0, 0, 0, Y 3 0, Y 3 1, Y 3 2, Y 3 3]

set_option maxHeartbeats 4000000 in
lemma quaternaryPairMatrixBlock_mul
    {K : Type*} [Field K]
    (Y Z : Matrix (Fin 4) (Fin 4) K) :
    quaternaryPairMatrixBlock Y * quaternaryPairMatrixBlock Z =
      quaternaryPairMatrixBlock (Y * Z) := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp [quaternaryPairMatrixBlock, Matrix.mul_apply,
    Fin.sum_univ_eight, Fin.sum_univ_four]

set_option maxHeartbeats 800000 in
lemma quaternaryPairMatrixBlock_one
    {K : Type*} [Field K] :
    quaternaryPairMatrixBlock (1 : Matrix (Fin 4) (Fin 4) K) =
      (1 : Matrix (Fin 8) (Fin 8) K) := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp [quaternaryPairMatrixBlock]

/-- The invertible paired quaternary block associated to an invertible
quaternary matrix. -/
noncomputable def quaternaryPairGeneralLinearBlock
    {K : Type*} [Field K] (Y : Matrix.GeneralLinearGroup (Fin 4) K) :
    Matrix.GeneralLinearGroup (Fin 8) K := by
  let M := quaternaryPairMatrixBlock (Y : Matrix (Fin 4) (Fin 4) K)
  let N := quaternaryPairMatrixBlock
    (↑(Y⁻¹) : Matrix (Fin 4) (Fin 4) K)
  refine ⟨M, N, ?_, ?_⟩
  · rw [show M * N = quaternaryPairMatrixBlock
        ((Y : Matrix (Fin 4) (Fin 4) K) *
          (↑(Y⁻¹) : Matrix (Fin 4) (Fin 4) K)) by
      exact quaternaryPairMatrixBlock_mul _ _]
    rw [← Matrix.GeneralLinearGroup.coe_mul]
    simp [quaternaryPairMatrixBlock_one]
  · rw [show N * M = quaternaryPairMatrixBlock
        ((↑(Y⁻¹) : Matrix (Fin 4) (Fin 4) K) *
          (Y : Matrix (Fin 4) (Fin 4) K)) by
      exact quaternaryPairMatrixBlock_mul _ _]
    rw [← Matrix.GeneralLinearGroup.coe_mul]
    simp [quaternaryPairMatrixBlock_one]

@[simp] lemma quaternaryPairGeneralLinearBlock_coe
    {K : Type*} [Field K] (Y : Matrix.GeneralLinearGroup (Fin 4) K) :
    (quaternaryPairGeneralLinearBlock Y : Matrix (Fin 8) (Fin 8) K) =
      quaternaryPairMatrixBlock (Y : Matrix (Fin 4) (Fin 4) K) := by
  simp [quaternaryPairGeneralLinearBlock]

/-! ### The rank-six identity recurrence -/

/-- The fiber of the squaring map over `c`. -/
def squareRootFiber (K : Type*) [CommRing K] (c : K) :=
  {x : K // x ^ 2 = c}

/-- The zero square-root fiber over a field is a singleton. -/
noncomputable def squareRootFiberZeroEquivUnit
    {K : Type*} [Field K] : squareRootFiber K 0 ≃ Unit where
  toFun _ := Unit.unit
  invFun _ := ⟨0, by simp⟩
  left_inv x := by
    apply Subtype.ext
    exact (sq_eq_zero_iff.mp x.2).symm
  right_inv _ := rfl

theorem natCard_squareRootFiber_zero
    {K : Type*} [Field K] : Nat.card (squareRootFiber K 0) = 1 := by
  rw [Nat.card_congr (squareRootFiberZeroEquivUnit (K := K))]
  simp

/-- A nonzero square has exactly two square roots in odd characteristic. -/
noncomputable def squareRootFiberEquivBool
    {K : Type*} [Field K] (hchar : ringChar K ≠ 2)
    (c : K) (hc : c ≠ 0) (t : K) (ht : t ^ 2 = c) :
    squareRootFiber K c ≃ Bool := by
  classical
  have ht0 : t ≠ 0 := by
    intro h
    apply hc
    simpa [h] using ht.symm
  have htneg : t ≠ -t := by
    intro h
    have htwo : (2 : K) ≠ 0 := Ring.two_ne_zero hchar
    apply ht0
    apply (mul_eq_zero.mp ?_).resolve_left htwo
    linear_combination h
  have hneg_t : -t ≠ t := Ne.symm htneg
  exact
    { toFun := fun x => decide (x.1 ≠ t)
      invFun := fun b => if b then ⟨-t, by simp [ht]⟩ else ⟨t, ht⟩
      left_inv := by
        intro x
        apply Subtype.ext
        by_cases hx : x.1 = t
        · simp [hx]
        · have hxneg : x.1 = -t := by
            apply (sq_eq_sq_iff_eq_or_eq_neg.mp ?_).resolve_left hx
            rw [x.2, ht]
          simp [hxneg, hneg_t]
      right_inv := by
        intro b
        cases b
        · simp
        · simp [hneg_t] }

theorem natCard_squareRootFiber_of_sq
    {K : Type*} [Field K] (hchar : ringChar K ≠ 2)
    (c : K) (hc : c ≠ 0) (t : K) (ht : t ^ 2 = c) :
    Nat.card (squareRootFiber K c) = 2 := by
  rw [Nat.card_congr (squareRootFiberEquivBool hchar c hc t ht)]
  simp

theorem natCard_squareRootFiber_of_nonsquare
    {K : Type*} [Field K] (c : K) (hc : ∀ t : K, t ^ 2 ≠ c) :
    Nat.card (squareRootFiber K c) = 0 := by
  let e : squareRootFiber K c ≃ Empty :=
    { toFun := fun x => (hc x.1 x.2).elim
      invFun := fun x => x.elim
      left_inv := fun x => (hc x.1 x.2).elim
      right_inv := fun x => x.elim }
  rw [Nat.card_congr e]
  simp

end GoodPrimeFiniteOrthogonalGroup


lemma massLocalFactorAtPrime_eq_classicalSolutionCountLocalDensity_of_not_mem_bad
    (L : PositiveDefiniteIntegralLattice n) (p : {p : ℕ // Nat.Prime p})
    (hp : p ∉ massBadPrimeSet L) :
    massLocalFactorAtPrime L p =
      (((1 / 2 : ℚ) * classicalSolutionCountLocalDensityAtPrime L p : ℚ) : ℝ) := by
  letI : Fact (Nat.Prime p.1) := ⟨p.2⟩
  have hp_two : p.1 ≠ 2 :=
    not_mem_massBadPrimeSet_ne_two L hp
  have hval : padicValInt p.1 L.polarDeterminant = 0 :=
    padicValInt_polarDeterminant_eq_zero_of_not_mem_massBadPrimeSet L hp
  have halpha :=
    normalizedLocalDensity_eq_classicalSolutionCountLocalDensity_odd
      (n := n) L p.1 hp_two
  have hpow :
      (p.1 : ℝ) ^
          (-((padicValInt p.1 L.polarDeterminant : ℝ) * (((n : ℝ) + 1) / 2))) = 1 := by
    rw [hval]
    norm_num
  rw [hpow, mul_one] at halpha
  simpa [massLocalFactorAtPrime, massLocalFactor,
    classicalSolutionCountLocalDensityAtPrime]
    using halpha

lemma massLocalInverseFactorAtPrime_eq_classicalSolutionCountLocalDensity_inv_of_not_mem_bad
    (L : PositiveDefiniteIntegralLattice n) (p : {p : ℕ // Nat.Prime p})
    (hp : p ∉ massBadPrimeSet L) :
    massLocalInverseFactorAtPrime L p =
      ((((1 / 2 : ℚ) * classicalSolutionCountLocalDensityAtPrime L p : ℚ) : ℝ))⁻¹ := by
  letI : Fact (Nat.Prime p.1) := ⟨p.2⟩
  rw [massLocalInverseFactorAtPrime,
    massLocalFactorAtPrime_eq_classicalSolutionCountLocalDensity_of_not_mem_bad
      (n := n) L p hp]

/-- Good-prime comparison between the target Schulze--Pillot local factor and
Conway--Sloane's alpha-type local factor. -/
theorem massLocalFactorAtPrime_eq_halfClassicalLocalDensityAtPrime
    (L : PositiveDefiniteIntegralLattice n) (p : {p : ℕ // Nat.Prime p})
    (hp : p ∉ massBadPrimeSet L) :
    massLocalFactorAtPrime L p =
      halfClassicalLocalDensityAtPrime L p := by
  simpa [halfClassicalLocalDensityAtPrime] using
    massLocalFactorAtPrime_eq_classicalSolutionCountLocalDensity_of_not_mem_bad
      L p hp

/-- The universal finite Euler factor appearing at good primes in
Schulze--Pillot's local-density formula:
`∏_{j=1}^{s-1} (1 - p^{-2j})`. -/
noncomputable def goodPrimeEulerCore
    (p : {p : ℕ // Nat.Prime p}) (s : ℕ) : ℝ :=
  (Finset.Icc 1 (s - 1)).prod fun j =>
    1 - (p.1 : ℝ) ^ (-((2 : ℝ) * (j : ℝ)))

/-- The good-prime quadratic character value `χ_D(p)` in even rank, recorded
as the Jacobi symbol `J(((-1)^(n/2)) polarDeterminant(L) | p)`.

At the even-rank call sites `n = 2 * s`, this is the odd-prime component of
the Kronecker character attached to `D = (-1)^s polarDeterminant(L)`.  The later
Dirichlet-character step constructs the corresponding
modular character and prove agreement with this explicit symbol away from the
finite bad-prime set. -/
def goodPrimeQuadraticCharacter
    (L : PositiveDefiniteIntegralLattice n) (p : {p : ℕ // Nat.Prime p}) : ℤ :=
  jacobiSym (((-1 : ℤ) ^ (n / 2)) * L.polarDeterminant) p.1

/-- The good-prime Euler factor in odd rank `n = 2s - 1`. -/
noncomputable def goodPrimeOddEulerFactor
    (p : {p : ℕ // Nat.Prime p}) (s : ℕ) : ℝ :=
  goodPrimeEulerCore p s

/-- The good-prime Euler factor in even rank `n = 2s`. -/
noncomputable def goodPrimeEvenEulerFactor
    (L : PositiveDefiniteIntegralLattice n) (p : {p : ℕ // Nat.Prime p}) (s : ℕ) : ℝ :=
  goodPrimeEulerCore p s *
    (1 - (goodPrimeQuadraticCharacter L p : ℝ) *
      (p.1 : ℝ) ^ (-(s : ℝ)))

/-- The reduced good-prime Gram matrix remains symmetric. -/
lemma goodPrimeGramMatrix_isSymm
    (L : PositiveDefiniteIntegralLattice n) (p : {p : ℕ // Nat.Prime p}) :
    (goodPrimeGramMatrix L p).IsSymm := by
  ext i j
  simp [goodPrimeGramMatrix, polarGramMatrix, Matrix.transpose_apply,
    L.form_symm.apply]

/-- The determinant of the reduced good-prime Gram matrix is the reduced
integral discriminant. -/
lemma goodPrimeGramMatrix_det_eq_polarDeterminant
    (L : PositiveDefiniteIntegralLattice n) (p : {p : ℕ // Nat.Prime p}) :
    (goodPrimeGramMatrix L p).det = (L.polarDeterminant : ZMod p.1) := by
  rw [goodPrimeGramMatrix, PositiveDefiniteIntegralLattice.polarDeterminant, Int.cast_det]

/-- Rank-one specialization of the good-prime local-density computation.

This is the only general bad-prime finite-support case: the odd-rank Euler
core has no nontrivial good-prime factor when `n = 1`. The proof is through
the order-two one-dimensional finite orthogonal group. -/
lemma goodPrime_classicalSolutionCountLocalDensity_eq_one_of_rank_one
    (L : PositiveDefiniteIntegralLattice n) (hn : n = 1)
    (p : {p : ℕ // Nat.Prime p}) (hp : p ∉ massBadPrimeSet L) :
    (((1 / 2 : ℚ) * classicalSolutionCountLocalDensityAtPrime L p : ℚ) : ℝ) = 1 := by
  subst n
  rw [classicalSolutionCountLocalDensityAtPrime_eq_orthogonalGroup_normalizedCard_of_goodPrime
    L p hp, natCard_goodPrimeFiniteGramOrthogonalGroup_rank_one L p hp]
  norm_num

/-- For a fixed exponent index `j`, the finite prime product of inverse core
Euler factors `(1 - p^{-2j})⁻¹`.  These are the finite products that later
become zeta factors. -/
noncomputable def goodPrimeEulerCoreInverseProduct
    (S : Finset {p : ℕ // Nat.Prime p}) (j : ℕ) : ℝ :=
  S.prod fun p => (1 - (p.1 : ℝ) ^ (-((2 : ℝ) * (j : ℝ))))⁻¹

/-- The odd-rank finite good-prime tail reindexed as a product over the core
Euler-factor exponents `j = 1, ..., s - 1`. -/
noncomputable def goodPrimeOddEulerCoreInverseProduct
    (S : Finset {p : ℕ // Nat.Prime p}) (s : ℕ) : ℝ :=
  (Finset.Icc 1 (s - 1)).prod fun j =>
    goodPrimeEulerCoreInverseProduct S j

/-- The even-rank finite good-prime character tail
`∏_{p ∈ S} (1 - χ_D(p) p^{-s})⁻¹`, using the product-facing Jacobi-symbol
value `goodPrimeQuadraticCharacter`.  The future
Kronecker/Dirichlet-character formalization should prove the fixed-modulus
Dirichlet character agrees with this value without changing this product
shape. -/
noncomputable def goodPrimeEvenCharacterInverseProduct
    (L : PositiveDefiniteIntegralLattice n) (S : Finset {p : ℕ // Nat.Prime p}) (s : ℕ) : ℝ :=
  S.prod fun p =>
    (1 - (goodPrimeQuadraticCharacter L p : ℝ) *
      (p.1 : ℝ) ^ (-(s : ℝ)))⁻¹

lemma goodPrimeOddEulerProduct_eq_coreInverseProduct
    (S : Finset {p : ℕ // Nat.Prime p}) (s : ℕ) :
    (S.prod fun p => (goodPrimeOddEulerFactor p s)⁻¹) =
      goodPrimeOddEulerCoreInverseProduct S s := by
  calc
    (S.prod fun p => (goodPrimeOddEulerFactor p s)⁻¹) =
        S.prod fun p =>
          (Finset.Icc 1 (s - 1)).prod fun j =>
            (1 - (p.1 : ℝ) ^ (-((2 : ℝ) * (j : ℝ))))⁻¹ := by
          refine Finset.prod_congr rfl ?_
          intro p _hp
          rw [goodPrimeOddEulerFactor,
            goodPrimeEulerCore, Finset.prod_inv_distrib]
    _ = (Finset.Icc 1 (s - 1)).prod fun j =>
          S.prod fun p =>
            (1 - (p.1 : ℝ) ^ (-((2 : ℝ) * (j : ℝ))))⁻¹ := by
          rw [Finset.prod_comm]
    _ = goodPrimeOddEulerCoreInverseProduct S s := by
          rfl

lemma goodPrimeEvenEulerProduct_eq_core_mul_characterInverseProduct
    (L : PositiveDefiniteIntegralLattice n) (S : Finset {p : ℕ // Nat.Prime p}) (s : ℕ) :
    (S.prod fun p => (goodPrimeEvenEulerFactor L p s)⁻¹) =
      goodPrimeOddEulerCoreInverseProduct S s *
        goodPrimeEvenCharacterInverseProduct L S s := by
  calc
    (S.prod fun p => (goodPrimeEvenEulerFactor L p s)⁻¹) =
        S.prod fun p =>
          (goodPrimeOddEulerFactor p s)⁻¹ *
            (1 - (goodPrimeQuadraticCharacter L p : ℝ) *
              (p.1 : ℝ) ^ (-(s : ℝ)))⁻¹ := by
          refine Finset.prod_congr rfl ?_
          intro p _hp
          rw [goodPrimeEvenEulerFactor,
            goodPrimeOddEulerFactor, mul_inv_rev]
          ring
    _ = (S.prod fun p => (goodPrimeOddEulerFactor p s)⁻¹) *
          goodPrimeEvenCharacterInverseProduct L S s := by
          rw [Finset.prod_mul_distrib, goodPrimeEvenCharacterInverseProduct]
    _ = goodPrimeOddEulerCoreInverseProduct S s *
          goodPrimeEvenCharacterInverseProduct L S s := by
          rw [goodPrimeOddEulerProduct_eq_coreInverseProduct]

lemma massFinitePrimeInverseProduct_eq_goodPrimeClassicalInverseProduct_of_forall_not_mem_bad
    (L : PositiveDefiniteIntegralLattice n) (S : Finset {p : ℕ // Nat.Prime p})
    (hS : ∀ p ∈ S, p ∉ massBadPrimeSet L) :
    massFinitePrimeInverseProduct L S =
      massGoodPrimeClassicalInverseProduct L S := by
  refine Finset.prod_congr rfl ?_
  intro p hp
  exact
    massLocalInverseFactorAtPrime_eq_classicalSolutionCountLocalDensity_inv_of_not_mem_bad
      (n := n) L p (hS p hp)

/-- Any finite prime-set product splits into its bad-prime Schulze--Pillot
part and its good-prime classical solution-count part. -/
lemma massFinitePrimeInverseProduct_eq_badPrime_mul_goodPrimeClassical
    (L : PositiveDefiniteIntegralLattice n) (S : Finset {p : ℕ // Nat.Prime p}) :
    massFinitePrimeInverseProduct L S =
      massFinitePrimeInverseProduct L
          (S ∩ massBadPrimeSet L) *
        massGoodPrimeClassicalInverseProduct L
          (S \ massBadPrimeSet L) := by
  let B := massBadPrimeSet L
  have hdisj : Disjoint (S \ B) (S ∩ B) := by
    rw [Finset.disjoint_left]
    intro p hp hpb
    exact (Finset.mem_sdiff.mp hp).2 (Finset.mem_inter.mp hpb).2
  have hgood :
      massFinitePrimeInverseProduct L (S \ B) =
        massGoodPrimeClassicalInverseProduct L (S \ B) :=
    massFinitePrimeInverseProduct_eq_goodPrimeClassicalInverseProduct_of_forall_not_mem_bad
      (n := n) L (S \ B) (by
        intro p hp
        exact (Finset.mem_sdiff.mp hp).2)
  calc
    massFinitePrimeInverseProduct L S =
        massFinitePrimeInverseProduct L ((S \ B) ∪ (S ∩ B)) := by
          rw [Finset.sdiff_union_inter]
    _ = massFinitePrimeInverseProduct L (S \ B) *
          massFinitePrimeInverseProduct L (S ∩ B) := by
          simp [massFinitePrimeInverseProduct,
            Finset.prod_union hdisj]
    _ = massFinitePrimeInverseProduct L (S ∩ B) *
          massGoodPrimeClassicalInverseProduct L (S \ B) := by
          rw [hgood]
          ring

/-- If a finite prime set already contains every bad prime, its
Schulze--Pillot inverse product has a fixed bad-prime part and a good-prime
classical tail. -/
lemma massFinitePrimeInverseProduct_eq_badPrimeSet_mul_goodPrimeClassical
    (L : PositiveDefiniteIntegralLattice n) (S : Finset {p : ℕ // Nat.Prime p})
    (hB : massBadPrimeSet L ⊆ S) :
    massFinitePrimeInverseProduct L S =
      massBadPrimeInverseProduct L *
        massGoodPrimeClassicalInverseProduct L
          (S \ massBadPrimeSet L) := by
  let B := massBadPrimeSet L
  have hinter : S ∩ B = B := by
    ext p
    constructor
    · intro hp
      exact (Finset.mem_inter.mp hp).2
    · intro hp
      exact Finset.mem_inter.mpr ⟨hB hp, hp⟩
  rw [massFinitePrimeInverseProduct_eq_badPrime_mul_goodPrimeClassical]
  rw [hinter]
  rfl

/-- Adjoining a disjoint finite set of good primes multiplies the finite
Schulze--Pillot inverse product by the corresponding classical good-prime
tail. -/
lemma massFinitePrimeInverseProduct_union_goodPrimeClassical
    (L : PositiveDefiniteIntegralLattice n) (S T : Finset {p : ℕ // Nat.Prime p})
    (hdisj : Disjoint S T)
    (hT : ∀ p ∈ T, p ∉ massBadPrimeSet L) :
    massFinitePrimeInverseProduct L (S ∪ T) =
      massFinitePrimeInverseProduct L S *
        massGoodPrimeClassicalInverseProduct L T := by
  have hgood :
      massFinitePrimeInverseProduct L T =
        massGoodPrimeClassicalInverseProduct L T :=
    massFinitePrimeInverseProduct_eq_goodPrimeClassicalInverseProduct_of_forall_not_mem_bad
      (n := n) L T hT
  calc
    massFinitePrimeInverseProduct L (S ∪ T) =
        massFinitePrimeInverseProduct L S *
          massFinitePrimeInverseProduct L T := by
          simp [massFinitePrimeInverseProduct,
            Finset.prod_union hdisj]
    _ = massFinitePrimeInverseProduct L S *
          massGoodPrimeClassicalInverseProduct L T := by
          rw [hgood]


lemma rationalPrimesUpTo_subset_of_le {N M : ℕ} (hNM : N ≤ M) :
    rationalPrimesUpTo N ⊆ rationalPrimesUpTo M := by
  intro p hp
  rw [mem_rationalPrimesUpTo_iff] at hp ⊢
  exact le_trans hp hNM

/-- The coercion embedding from the rational-prime subtype to natural numbers,
used to compare the repository cutoff sets with Mathlib's `Nat.primesBelow`. -/
def rationalPrimeValEmbedding : {p : ℕ // Nat.Prime p} ↪ ℕ :=
  ⟨Subtype.val, by
    intro p q hpq
    exact Subtype.ext hpq⟩

lemma rationalPrimesUpTo_map_val_eq_primesBelow (N : ℕ) :
    (rationalPrimesUpTo N).map rationalPrimeValEmbedding =
      (N + 1).primesBelow := by
  ext q
  constructor
  · rw [Finset.mem_map]
    rintro ⟨p, hp, hpq⟩
    have hp_le : p.1 ≤ N := (mem_rationalPrimesUpTo_iff N p).mp hp
    rw [Nat.mem_primesBelow]
    exact ⟨by simpa [Nat.lt_succ_iff, hpq.symm] using hp_le,
      by simpa [hpq.symm] using p.2⟩
  · intro hq
    rw [Nat.mem_primesBelow] at hq
    rw [Finset.mem_map]
    refine ⟨⟨q, hq.2⟩, ?_, rfl⟩
    rw [mem_rationalPrimesUpTo_iff]
    exact Nat.lt_succ_iff.mp hq.1

lemma rationalPrimesUpTo_sdiff_map_val_eq_primesBelow_sdiff
    (N M : ℕ) :
    (rationalPrimesUpTo M \ rationalPrimesUpTo N).map rationalPrimeValEmbedding =
      (M + 1).primesBelow \ (N + 1).primesBelow := by
  rw [Finset.map_sdiff, rationalPrimesUpTo_map_val_eq_primesBelow,
    rationalPrimesUpTo_map_val_eq_primesBelow]

lemma goodPrimeEulerCoreInverseProduct_eq_primesBelow
    (N j : ℕ) :
    goodPrimeEulerCoreInverseProduct (rationalPrimesUpTo N) j =
      ((N + 1).primesBelow.prod fun p =>
        (1 - (p : ℝ) ^ (-((2 : ℝ) * (j : ℝ))))⁻¹) := by
  rw [← rationalPrimesUpTo_map_val_eq_primesBelow N]
  simp [goodPrimeEulerCoreInverseProduct, Finset.prod_map,
    rationalPrimeValEmbedding]

lemma goodPrimeEulerCoreInverseProduct_tail_eq_primesBelow_sdiff
    (N M j : ℕ) :
    goodPrimeEulerCoreInverseProduct
        (rationalPrimesUpTo M \ rationalPrimesUpTo N) j =
      (((M + 1).primesBelow \ (N + 1).primesBelow).prod fun p =>
        (1 - (p : ℝ) ^ (-((2 : ℝ) * (j : ℝ))))⁻¹) := by
  rw [← rationalPrimesUpTo_sdiff_map_val_eq_primesBelow_sdiff N M]
  simp [goodPrimeEulerCoreInverseProduct, Finset.prod_map,
    rationalPrimeValEmbedding]

/-- A source-facing convergence predicate for one fixed core Euler tail
`∏_{N < p ≤ M} (1 - p^{-2j})⁻¹`.  The later zeta Euler-product theorem should
provide this predicate with limit `ζ(2j)` after removing the finite cutoff. -/
def goodPrimeEulerCoreInverseProductTendsTo
    (N j : ℕ) (P : ℝ) : Prop :=
  Filter.Tendsto
    (fun M : ℕ =>
      goodPrimeEulerCoreInverseProduct
        (rationalPrimesUpTo M \ rationalPrimesUpTo N) j)
    Filter.atTop (nhds P)

/-- The zeta Euler-product value for the fixed core tail after removing the
finite cutoff `N`.  This is the real-valued target corresponding to
`ζ(2j) / ∏_{p ≤ N} (1 - p^{-2j})⁻¹`. -/
noncomputable def goodPrimeEulerCoreZetaTailFactor
    (N j : ℕ) : ℝ :=
  (riemannZeta (((2 * j : ℕ) : ℝ) : ℂ)).re *
    (goodPrimeEulerCoreInverseProduct
      (rationalPrimesUpTo N) j)⁻¹

/-- The real inverse core Euler factor, embedded in `ℂ`, is the corresponding
complex factor used by Mathlib's Riemann zeta Euler product. -/
lemma goodPrimeEulerCoreInverseFactor_ofReal
    (p j : ℕ) :
    (((1 - (p : ℝ) ^ (-((2 : ℝ) * (j : ℝ))))⁻¹ : ℝ) : ℂ) =
      (1 - (p : ℂ) ^ (-((2 * j : ℕ) : ℂ)))⁻¹ := by
  rw [Complex.ofReal_inv, Complex.ofReal_sub, Complex.ofReal_one]
  congr 2
  rw [Complex.ofReal_cpow]
  · congr 1
    norm_num
  · positivity

/-- The same real-to-complex bridge after rewriting the prime subtype cutoff
tail as Mathlib's `Nat.primesBelow` tail. -/
lemma goodPrimeEulerCoreInverseProduct_tail_eq_complex_re_primesBelow_sdiff
    (N M j : ℕ) :
    goodPrimeEulerCoreInverseProduct
        (rationalPrimesUpTo M \ rationalPrimesUpTo N) j =
      (((M + 1).primesBelow \ (N + 1).primesBelow).prod fun p =>
        (1 - (p : ℂ) ^ (-((2 * j : ℕ) : ℂ)))⁻¹).re := by
  rw [goodPrimeEulerCoreInverseProduct_tail_eq_primesBelow_sdiff]
  rw [Finset.prod_inv_distrib]
  let S := (M + 1).primesBelow \ (N + 1).primesBelow
  have hcast :
      (((S.prod fun p =>
        (1 - (p : ℝ) ^ (-((2 : ℝ) * (j : ℝ)))))⁻¹ : ℝ) : ℂ) =
        (S.prod fun p => (1 - (p : ℂ) ^ (-((2 * j : ℕ) : ℂ))))⁻¹ := by
    rw [Complex.ofReal_inv, Complex.ofReal_prod]
    congr 1
    refine Finset.prod_congr rfl ?_
    intro p _hp
    rw [Complex.ofReal_sub, Complex.ofReal_one]
    congr 1
    rw [Complex.ofReal_cpow]
    · congr 1
      norm_num
    · positivity
  conv_rhs => rw [Finset.prod_inv_distrib]
  change (S.prod fun p =>
      (1 - (p : ℝ) ^ (-((2 : ℝ) * (j : ℝ)))))⁻¹ =
    ((S.prod fun p => (1 - (p : ℂ) ^ (-((2 * j : ℕ) : ℂ))))⁻¹).re
  have hre := congrArg Complex.re hcast
  rw [Complex.ofReal_re] at hre
  exact hre

/-- Complex convergence of the fixed core Euler tail, directly from
Mathlib's Riemann zeta Euler product and finite cutoff cancellation. -/
lemma riemann_zeta_goodPrimeEulerCoreComplexTail_tendsto
    (N j : ℕ) (hj : 1 ≤ j) :
    Filter.Tendsto
      (fun M : ℕ => ((M + 1).primesBelow \ (N + 1).primesBelow).prod fun p =>
        (1 - (p : ℂ) ^ (-((2 * j : ℕ) : ℂ)))⁻¹)
      Filter.atTop
      (nhds (riemannZeta ((2 * j : ℕ) : ℂ) /
        ((N + 1).primesBelow.prod fun p =>
          (1 - (p : ℂ) ^ (-((2 * j : ℕ) : ℂ)))⁻¹))) := by
  let s : ℂ := ((2 * j : ℕ) : ℂ)
  have hs : 1 < s.re := by
    dsimp [s]
    norm_num
    have hjr : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
    nlinarith
  have hzN :
      ((N + 1).primesBelow.prod fun p =>
        (1 - (p : ℂ) ^ (-s))⁻¹) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr ?_
    intro p hp
    exact inv_ne_zero
      (Complex.one_sub_prime_cpow_ne_zero
        (Nat.prime_of_mem_primesBelow hp) hs)
  have hzeta :=
    (riemannZeta_eulerProduct (s := s) hs).comp
      (Filter.tendsto_add_atTop_nat 1)
  have hdiv := hzeta.div_const
    ((N + 1).primesBelow.prod fun p =>
      (1 - (p : ℂ) ^ (-s))⁻¹)
  refine Filter.Tendsto.congr' ?_ hdiv
  filter_upwards [Filter.eventually_ge_atTop N] with M hNM
  have hsubset :
      (N + 1).primesBelow ⊆ (M + 1).primesBelow := by
    intro p hp
    rw [Nat.mem_primesBelow] at hp ⊢
    exact ⟨lt_of_lt_of_le hp.1 (Nat.succ_le_succ hNM), hp.2⟩
  rw [Function.comp_def]
  simp only [s]
  rw [← Finset.prod_sdiff hsubset]
  exact mul_div_cancel_right₀ _ hzN

/-- The Riemann zeta Euler product in the repository's real-valued
prime-subtype/cutoff notation.  This is proved by
translating Mathlib's complex `riemannZeta_eulerProduct` through the finite
cutoff and real-part bridge above. -/
theorem riemann_zeta_goodPrimeEulerCoreInverseProductTendsTo
    (N j : ℕ) (hj : 1 ≤ j) :
    goodPrimeEulerCoreInverseProductTendsTo N j
      (goodPrimeEulerCoreZetaTailFactor N j) := by
  unfold goodPrimeEulerCoreInverseProductTendsTo
  have hcomplex :=
    riemann_zeta_goodPrimeEulerCoreComplexTail_tendsto N j hj
  have hreal :
      Filter.Tendsto
        (fun M : ℕ =>
          (((M + 1).primesBelow \ (N + 1).primesBelow).prod fun p =>
            (1 - (p : ℂ) ^ (-((2 * j : ℕ) : ℂ)))⁻¹).re)
        Filter.atTop
        (nhds ((riemannZeta ((2 * j : ℕ) : ℂ) /
          ((N + 1).primesBelow.prod fun p =>
            (1 - (p : ℂ) ^ (-((2 * j : ℕ) : ℂ)))⁻¹)).re)) :=
    Complex.continuous_re.tendsto _ |>.comp hcomplex
  have htail :
      Filter.Tendsto
        (fun M : ℕ =>
          goodPrimeEulerCoreInverseProduct
            (rationalPrimesUpTo M \ rationalPrimesUpTo N) j)
        Filter.atTop
        (nhds ((riemannZeta ((2 * j : ℕ) : ℂ) /
          ((N + 1).primesBelow.prod fun p =>
            (1 - (p : ℂ) ^ (-((2 * j : ℕ) : ℂ)))⁻¹)).re)) := by
    refine Filter.Tendsto.congr' ?_ hreal
    filter_upwards with M
    exact (goodPrimeEulerCoreInverseProduct_tail_eq_complex_re_primesBelow_sdiff
      N M j).symm
  have hlim :
      goodPrimeEulerCoreZetaTailFactor N j =
        (riemannZeta ((2 * j : ℕ) : ℂ) /
          ((N + 1).primesBelow.prod fun p =>
            (1 - (p : ℂ) ^ (-((2 * j : ℕ) : ℂ)))⁻¹)).re := by
    rw [goodPrimeEulerCoreZetaTailFactor,
      goodPrimeEulerCoreInverseProduct_eq_primesBelow]
    let R : ℝ := ((N + 1).primesBelow.prod fun p =>
      (1 - (p : ℝ) ^ (-((2 : ℝ) * (j : ℝ))))⁻¹)
    have hden :
        ((R : ℝ) : ℂ) =
          ((N + 1).primesBelow.prod fun p =>
            (1 - (p : ℂ) ^ (-((2 * j : ℕ) : ℂ)))⁻¹) := by
      dsimp [R]
      rw [Complex.ofReal_prod]
      refine Finset.prod_congr rfl ?_
      intro p _hp
      exact goodPrimeEulerCoreInverseFactor_ofReal p j
    rw [← hden]
    change (riemannZeta ((2 * j : ℕ) : ℂ)).re * R⁻¹ =
      (riemannZeta ((2 * j : ℕ) : ℂ) / ((R : ℝ) : ℂ)).re
    rw [div_eq_mul_inv, Complex.mul_re]
    simp
  simpa [hlim] using htail

/-- Convergence of the odd-rank core tail, after the finite product over
`j = 1, ..., s - 1` has been reassembled. -/
def goodPrimeOddEulerCoreInverseProductTendsTo
    (N s : ℕ) (P : ℝ) : Prop :=
  Filter.Tendsto
    (fun M : ℕ =>
      goodPrimeOddEulerCoreInverseProduct
        (rationalPrimesUpTo M \ rationalPrimesUpTo N) s)
    Filter.atTop (nhds P)

/-- Convergence predicate for the even-rank quadratic-character tail
`∏_{N < p ≤ M} (1 - χ_D(p)p^{-s})⁻¹`.  This is intentionally separate from
the zeta core products; its convergence for a Dirichlet/Kronecker character is
not proved in this declaration. -/
def goodPrimeEvenCharacterInverseProductTendsTo
    (L : PositiveDefiniteIntegralLattice n) (N s : ℕ) (P : ℝ) : Prop :=
  Filter.Tendsto
    (fun M : ℕ =>
      goodPrimeEvenCharacterInverseProduct L
        (rationalPrimesUpTo M \ rationalPrimesUpTo N) s)
    Filter.atTop (nhds P)

/-- The discriminant convention expected in the even-rank good-prime
quadratic character, namely `D = (-1)^s * polarDeterminant(L)`. -/
def goodPrimeEvenCharacterDiscriminant
    (L : PositiveDefiniteIntegralLattice n) (s : ℕ) : ℤ :=
  (-1 : ℤ) ^ s * L.polarDeterminant

/-- In the active even-rank branch, the product-facing Jacobi-symbol character
uses the same discriminant convention as the Dirichlet-character package. -/
lemma goodPrimeQuadraticCharacter_eq_jacobiSym_even
    (L : PositiveDefiniteIntegralLattice n) (p : {p : ℕ // Nat.Prime p}) (s : ℕ)
    (hn : n = 2 * s) :
    goodPrimeQuadraticCharacter L p =
      jacobiSym (goodPrimeEvenCharacterDiscriminant L s) p.1 := by
  have hhalf : n / 2 = s := by omega
  simp [goodPrimeQuadraticCharacter,
    goodPrimeEvenCharacterDiscriminant, hhalf]

/-- The even-rank Dirichlet discriminant has the same absolute value as the
bilinear Gram determinant. -/
lemma goodPrimeEvenCharacterDiscriminant_natAbs
    (L : PositiveDefiniteIntegralLattice n) (s : ℕ) :
    (goodPrimeEvenCharacterDiscriminant L s).natAbs =
      L.polarDeterminant.natAbs := by
  rw [goodPrimeEvenCharacterDiscriminant, Int.natAbs_mul,
    Int.natAbs_pow]
  norm_num

/-- At good primes, the even-rank Dirichlet discriminant is prime to the
denominator of the Jacobi symbol. -/
lemma goodPrimeEvenCharacterDiscriminant_gcd_prime_eq_one_of_not_mem_bad
    (L : PositiveDefiniteIntegralLattice n) (s : ℕ) {p : {p : ℕ // Nat.Prime p}}
    (hp : p ∉ massBadPrimeSet L) :
    (goodPrimeEvenCharacterDiscriminant L s).gcd p.1 = 1 := by
  have hnot_dvd_disc :
      ¬ p.1 ∣ L.polarDeterminant.natAbs :=
    not_mem_massBadPrimeSet_not_dvd_polarDeterminant_natAbs L hp
  have hnot_dvd_D :
      ¬ p.1 ∣ (goodPrimeEvenCharacterDiscriminant L s).natAbs := by
    simpa [goodPrimeEvenCharacterDiscriminant_natAbs] using
      hnot_dvd_disc
  have hcop :
      Nat.Coprime p.1
        (goodPrimeEvenCharacterDiscriminant L s).natAbs :=
    p.2.coprime_iff_not_dvd.mpr hnot_dvd_D
  simpa [Int.gcd, Nat.gcd_comm] using hcop.gcd_eq_one

/-- At good primes, the explicit Jacobi value used in the even-rank Euler
factor is quadratic. -/
lemma goodPrimeEvenCharacterJacobi_sq_of_not_mem_bad
    (L : PositiveDefiniteIntegralLattice n) (s : ℕ) {p : {p : ℕ // Nat.Prime p}}
    (hp : p ∉ massBadPrimeSet L) :
    jacobiSym (goodPrimeEvenCharacterDiscriminant L s) p.1 ^ 2 =
      1 := by
  exact jacobiSym.sq_one
    (goodPrimeEvenCharacterDiscriminant_gcd_prime_eq_one_of_not_mem_bad
      L s hp)

/-- In the active even-rank branch, the product-facing good-prime character
value is itself quadratic outside the bad-prime set. -/
lemma goodPrimeQuadraticCharacter_sq_of_not_mem_bad_even
    (L : PositiveDefiniteIntegralLattice n) (s : ℕ) {p : {p : ℕ // Nat.Prime p}}
    (hp : p ∉ massBadPrimeSet L) (hn : n = 2 * s) :
    goodPrimeQuadraticCharacter L p ^ 2 = 1 := by
  rw [goodPrimeQuadraticCharacter_eq_jacobiSym_even L p s hn]
  exact goodPrimeEvenCharacterJacobi_sq_of_not_mem_bad L s hp

/-- The fixed Dirichlet modulus for the even-rank character package.  This is
the standard modulus large enough for the Kronecker character attached to
`(-1)^s * polarDeterminant(L)`. -/
def goodPrimeEvenDirichletModulus
    (L : PositiveDefiniteIntegralLattice n) (s : ℕ) : ℕ :=
  4 * (goodPrimeEvenCharacterDiscriminant L s).natAbs

/-- The fixed Kronecker modulus is positive. -/
lemma goodPrimeEvenDirichletModulus_pos
    (L : PositiveDefiniteIntegralLattice n) (s : ℕ) :
    0 < goodPrimeEvenDirichletModulus L s := by
  have hD :
      0 < (goodPrimeEvenCharacterDiscriminant L s).natAbs :=
    Int.natAbs_pos.mpr (by
      rw [goodPrimeEvenCharacterDiscriminant]
      exact mul_ne_zero (by simp) (ne_of_gt L.polarDeterminant_pos))
  exact mul_pos (by norm_num) hD

/-- The fixed Kronecker modulus is strictly larger than one. -/
lemma one_lt_goodPrimeEvenDirichletModulus
    (L : PositiveDefiniteIntegralLattice n) (s : ℕ) :
    1 < goodPrimeEvenDirichletModulus L s := by
  rw [goodPrimeEvenDirichletModulus]
  have hD :
      0 < (goodPrimeEvenCharacterDiscriminant L s).natAbs :=
    Int.natAbs_pos.mpr (by
      rw [goodPrimeEvenCharacterDiscriminant]
      exact mul_ne_zero (by simp) (ne_of_gt L.polarDeterminant_pos))
  omega

/-- A number coprime to the fixed Kronecker modulus is odd. -/
lemma odd_of_coprime_goodPrimeEvenDirichletModulus
    (L : PositiveDefiniteIntegralLattice n) (s a : ℕ)
    (ha : Nat.Coprime a (goodPrimeEvenDirichletModulus L s)) :
    Odd a := by
  rw [← Nat.not_even_iff_odd]
  intro ha_even
  have htwo_dvd_mod :
      2 ∣ goodPrimeEvenDirichletModulus L s := by
    rw [goodPrimeEvenDirichletModulus]
    exact dvd_mul_of_dvd_left (by norm_num : 2 ∣ 4)
      (goodPrimeEvenCharacterDiscriminant L s).natAbs
  have htwo_dvd_gcd :
      2 ∣ Nat.gcd a (goodPrimeEvenDirichletModulus L s) :=
    Nat.dvd_gcd (even_iff_two_dvd.mp ha_even) htwo_dvd_mod
  rw [ha.gcd_eq_one] at htwo_dvd_gcd
  norm_num at htwo_dvd_gcd

/-- A number coprime to the fixed Kronecker modulus is nonzero. -/
lemma ne_zero_of_coprime_goodPrimeEvenDirichletModulus
    (L : PositiveDefiniteIntegralLattice n) (s a : ℕ)
    (ha : Nat.Coprime a (goodPrimeEvenDirichletModulus L s)) :
    a ≠ 0 := by
  intro ha_zero
  have hmod_one :
      goodPrimeEvenDirichletModulus L s = 1 := by
    simpa [ha_zero, Nat.gcd_comm] using ha.gcd_eq_one
  have hmod_pos := goodPrimeEvenDirichletModulus_pos L s
  have hmod_four :
      4 ≤ goodPrimeEvenDirichletModulus L s := by
    rw [goodPrimeEvenDirichletModulus]
    have hD :
        0 < (goodPrimeEvenCharacterDiscriminant L s).natAbs :=
      Int.natAbs_pos.mpr (by
        rw [goodPrimeEvenCharacterDiscriminant]
        exact mul_ne_zero (by simp) (ne_of_gt L.polarDeterminant_pos))
    omega
  omega

/-- Multiplicativity of the explicit Jacobi value after reducing the
denominator modulo the fixed Kronecker modulus.  This is the arithmetic
unit-multiplicativity step needed for the future Dirichlet/Kronecker character
construction. -/
lemma goodPrimeEvenCharacterJacobi_mul_mod
    (L : PositiveDefiniteIntegralLattice n) (s a b : ℕ)
    (ha : Nat.Coprime a (goodPrimeEvenDirichletModulus L s))
    (hb : Nat.Coprime b (goodPrimeEvenDirichletModulus L s)) :
    jacobiSym (goodPrimeEvenCharacterDiscriminant L s)
        ((a * b) % goodPrimeEvenDirichletModulus L s) =
      jacobiSym (goodPrimeEvenCharacterDiscriminant L s) a *
      jacobiSym (goodPrimeEvenCharacterDiscriminant L s) b := by
  let D := goodPrimeEvenCharacterDiscriminant L s
  let m := goodPrimeEvenDirichletModulus L s
  have ha_odd : Odd a :=
    odd_of_coprime_goodPrimeEvenDirichletModulus L s a ha
  have hb_odd : Odd b :=
    odd_of_coprime_goodPrimeEvenDirichletModulus L s b hb
  have hab_odd : Odd (a * b) := ha_odd.mul hb_odd
  have ha_ne : a ≠ 0 :=
    ne_zero_of_coprime_goodPrimeEvenDirichletModulus L s a ha
  have hb_ne : b ≠ 0 :=
    ne_zero_of_coprime_goodPrimeEvenDirichletModulus L s b hb
  have hmod :
      jacobiSym D (a * b) =
        jacobiSym D ((a * b) % m) := by
    simpa [D, m, goodPrimeEvenDirichletModulus]
      using (jacobiSym.mod_right D hab_odd)
  have hmul : jacobiSym D (a * b) = jacobiSym D a * jacobiSym D b := by
    haveI : NeZero a := ⟨ha_ne⟩
    haveI : NeZero b := ⟨hb_ne⟩
    exact jacobiSym.mul_right D a b
  exact hmod.symm.trans hmul

/-- A denominator coprime to the fixed Kronecker modulus is coprime to the
Jacobi discriminant. -/
lemma goodPrimeEvenCharacterDiscriminant_gcd_eq_one_of_coprime_modulus
    (L : PositiveDefiniteIntegralLattice n) (s a : ℕ)
    (ha : Nat.Coprime a (goodPrimeEvenDirichletModulus L s)) :
    (goodPrimeEvenCharacterDiscriminant L s).gcd a = 1 := by
  let D := goodPrimeEvenCharacterDiscriminant L s
  have hD_dvd_m :
      D.natAbs ∣ goodPrimeEvenDirichletModulus L s := by
    rw [goodPrimeEvenDirichletModulus]
    exact dvd_mul_left D.natAbs 4
  have hcop : Nat.Coprime a D.natAbs :=
    Nat.Coprime.of_dvd_right hD_dvd_m ha
  simpa [D, Int.gcd, Nat.gcd_comm] using hcop.gcd_eq_one

/-- On units modulo the fixed Kronecker modulus, the explicit Jacobi value is
quadratic. -/
lemma goodPrimeEvenCharacterJacobi_sq_of_coprime_modulus
    (L : PositiveDefiniteIntegralLattice n) (s a : ℕ)
    (ha : Nat.Coprime a (goodPrimeEvenDirichletModulus L s)) :
    jacobiSym (goodPrimeEvenCharacterDiscriminant L s) a ^ 2 =
      1 := by
  exact jacobiSym.sq_one
    (goodPrimeEvenCharacterDiscriminant_gcd_eq_one_of_coprime_modulus
      L s a ha)

/-- The explicit Jacobi value is nonzero on units modulo the fixed Kronecker
modulus. -/
lemma goodPrimeEvenCharacterJacobi_ne_zero_of_coprime_modulus
    (L : PositiveDefiniteIntegralLattice n) (s a : ℕ)
    (ha : Nat.Coprime a (goodPrimeEvenDirichletModulus L s)) :
    ((jacobiSym (goodPrimeEvenCharacterDiscriminant L s) a : ℝ) :
      ℂ) ≠ 0 := by
  intro hzero
  have hsq :=
    goodPrimeEvenCharacterJacobi_sq_of_coprime_modulus L s a ha
  have hsqC :
      (((jacobiSym (goodPrimeEvenCharacterDiscriminant L s) a : ℝ) :
        ℂ) ^ 2) = 1 := by
    exact_mod_cast hsq
  rw [hzero] at hsqC
  norm_num at hsqC

/-- The explicit fixed-modulus Jacobi symbol packaged as a homomorphism on the
unit group of `ZMod (4 * |(-1)^s polarDeterminant(L)|)`. -/
noncomputable def goodPrimeEvenCharacterJacobiUnitHom
    (L : PositiveDefiniteIntegralLattice n) (s : ℕ) :
    (ZMod (goodPrimeEvenDirichletModulus L s))ˣ →* ℂˣ where
  toFun u :=
    Units.mk0
      (((jacobiSym (goodPrimeEvenCharacterDiscriminant L s)
        (u : ZMod (goodPrimeEvenDirichletModulus L s)).val : ℝ) : ℂ))
      (goodPrimeEvenCharacterJacobi_ne_zero_of_coprime_modulus
        L s (u : ZMod (goodPrimeEvenDirichletModulus L s)).val
        (ZMod.val_coe_unit_coprime u))
  map_one' := by
    let m := goodPrimeEvenDirichletModulus L s
    haveI : Fact (1 < m) :=
      ⟨by
        dsimp [m]
        exact one_lt_goodPrimeEvenDirichletModulus L s⟩
    have hval : ((1 : (ZMod m)ˣ) : ZMod m).val = 1 := by
      change (1 : ZMod m).val = 1
      exact ZMod.val_one m
    ext
    simp only [Units.val_mk0]
    rw [hval]
    norm_num
  map_mul' u v := by
    ext
    simp only [Units.val_mk0, Units.val_mul]
    let m := goodPrimeEvenDirichletModulus L s
    let a := (u : ZMod m).val
    let b := (v : ZMod m).val
    have ha : Nat.Coprime a m := by
      simpa [a, m] using ZMod.val_coe_unit_coprime u
    have hb : Nat.Coprime b m := by
      simpa [b, m] using ZMod.val_coe_unit_coprime v
    have hmul :=
      goodPrimeEvenCharacterJacobi_mul_mod L s a b ha hb
    have hval : ((u : ZMod m) * (v : ZMod m)).val = (a * b) % m := by
      simpa [a, b] using ZMod.val_mul (u : ZMod m) (v : ZMod m)
    rw [hval]
    exact_mod_cast hmul

/-- The explicit fixed-modulus Jacobi symbol as an actual Dirichlet character.
This packages the unit-group homomorphism above with Mathlib's standard
`MulChar.ofUnitHom` extension, so non-units are sent to zero. -/
noncomputable def goodPrimeEvenJacobiDirichletCharacter
    (L : PositiveDefiniteIntegralLattice n) (s : ℕ) :
    DirichletCharacter ℂ (goodPrimeEvenDirichletModulus L s) :=
  MulChar.ofUnitHom (goodPrimeEvenCharacterJacobiUnitHom L s)

/-- On units, the concrete fixed-modulus Dirichlet character evaluates to the
explicit Jacobi value of the chosen representative. -/
lemma goodPrimeEvenJacobiDirichletCharacter_apply_unit
    (L : PositiveDefiniteIntegralLattice n) (s : ℕ)
    (u : (ZMod (goodPrimeEvenDirichletModulus L s))ˣ) :
    goodPrimeEvenJacobiDirichletCharacter L s
        (u : ZMod (goodPrimeEvenDirichletModulus L s)) =
      ((jacobiSym (goodPrimeEvenCharacterDiscriminant L s)
        (u : ZMod (goodPrimeEvenDirichletModulus L s)).val : ℝ) :
          ℂ) := by
  rw [goodPrimeEvenJacobiDirichletCharacter,
    MulChar.ofUnitHom_coe]
  simp [goodPrimeEvenCharacterJacobiUnitHom]

/-- A good prime is a unit modulo the fixed Kronecker modulus
`4 * |(-1)^s polarDeterminant(L)|`. -/
lemma goodPrimeEvenDirichletModulus_coprime_prime_of_not_mem_bad
    (L : PositiveDefiniteIntegralLattice n) (s : ℕ) {p : {p : ℕ // Nat.Prime p}}
    (hp : p ∉ massBadPrimeSet L) :
    Nat.Coprime p.1 (goodPrimeEvenDirichletModulus L s) := by
  have hp_ne_two : p.1 ≠ 2 :=
    not_mem_massBadPrimeSet_ne_two L hp
  have hp_coprime_four : Nat.Coprime p.1 4 := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num]
    exact Nat.Coprime.pow_right 2 <|
      (p.2.coprime_iff_not_dvd).mpr (by
        intro hp_dvd_two
        rcases (Nat.dvd_prime Nat.prime_two).mp hp_dvd_two with hp_one | hp_two
        · exact p.2.ne_one hp_one
        · exact hp_ne_two hp_two)
  have hnot_dvd_D :
      ¬ p.1 ∣ (goodPrimeEvenCharacterDiscriminant L s).natAbs := by
    simpa [goodPrimeEvenCharacterDiscriminant_natAbs] using
      not_mem_massBadPrimeSet_not_dvd_polarDeterminant_natAbs L hp
  have hp_coprime_D :
      Nat.Coprime p.1
        (goodPrimeEvenCharacterDiscriminant L s).natAbs :=
    p.2.coprime_iff_not_dvd.mpr hnot_dvd_D
  rw [goodPrimeEvenDirichletModulus]
  exact Nat.Coprime.mul_right hp_coprime_four hp_coprime_D

/-- The concrete fixed-modulus Jacobi `DirichletCharacter` agrees with the
product-facing good-prime quadratic value in the active even-rank branch. -/
lemma goodPrimeQuadraticCharacter_eq_jacobiDirichletCharacter
    (L : PositiveDefiniteIntegralLattice n) (s : ℕ) (p : {p : ℕ // Nat.Prime p})
    (hp : p ∉ massBadPrimeSet L) (hn : n = 2 * s) :
    (((goodPrimeQuadraticCharacter L p : ℝ) : ℂ)) =
      goodPrimeEvenJacobiDirichletCharacter L s p.1 := by
  let m := goodPrimeEvenDirichletModulus L s
  let D := goodPrimeEvenCharacterDiscriminant L s
  have hp_coprime : Nat.Coprime p.1 m := by
    simpa [m] using
      goodPrimeEvenDirichletModulus_coprime_prime_of_not_mem_bad
        L s hp
  let u : (ZMod m)ˣ := ZMod.unitOfCoprime p.1 hp_coprime
  rw [goodPrimeQuadraticCharacter_eq_jacobiSym_even L p s hn]
  change (((jacobiSym D p.1 : ℝ) : ℂ)) =
    goodPrimeEvenJacobiDirichletCharacter L s (p.1 : ZMod m)
  rw [show (p.1 : ZMod m) = (u : ZMod m) by rfl,
    goodPrimeEvenJacobiDirichletCharacter_apply_unit]
  have hp_odd : Odd p.1 :=
    p.2.odd_of_ne_two (not_mem_massBadPrimeSet_ne_two L hp)
  have hu_val : (u : ZMod m).val = p.1 % m := by
    rw [show (u : ZMod m) = (p.1 : ZMod m) by rfl]
    exact ZMod.val_natCast m p.1
  rw [hu_val]
  exact_mod_cast (jacobiSym.mod_right D hp_odd)

/-- The concrete fixed-modulus Jacobi `DirichletCharacter` is quadratic. -/
theorem goodPrimeEvenJacobiDirichletCharacter_sq
    (L : PositiveDefiniteIntegralLattice n) (s : ℕ) :
    goodPrimeEvenJacobiDirichletCharacter L s ^ 2 = 1 := by
  apply MulChar.ext
  intro u
  rw [MulChar.pow_apply_coe, MulChar.one_apply_coe]
  rw [goodPrimeEvenJacobiDirichletCharacter_apply_unit]
  have hsq :=
    goodPrimeEvenCharacterJacobi_sq_of_coprime_modulus
      L s (u : ZMod (goodPrimeEvenDirichletModulus L s)).val
      (ZMod.val_coe_unit_coprime u)
  exact_mod_cast hsq

/-- Odd numerator case for the elementary Jacobi-symbol witness:
`J(c | 4tc - 1) = 1`. -/
private lemma jacobiSym_nat_four_mul_sub_one_eq_one_of_odd
    (c t : ℕ) (hc : 0 < c) (ht : 0 < t) (hcodd : Odd c) :
    jacobiSym (c : ℤ) (4 * t * c - 1) = 1 := by
  let b := 4 * t * c - 1
  have htc_pos : 0 < t * c := Nat.mul_pos ht hc
  have hprod_pos : 0 < 4 * t * c := by nlinarith [htc_pos]
  have hprod_ge_one : 1 ≤ 4 * t * c := Nat.succ_le_of_lt hprod_pos
  have hb_succ : b + 1 = 4 * t * c := by
    dsimp [b]
    exact Nat.sub_add_cancel hprod_ge_one
  have hb_odd : Odd b := by
    refine ⟨2 * t * c - 1, ?_⟩
    apply Nat.succ.inj
    rw [Nat.succ_eq_add_one, hb_succ]
    have htwo_ge_one : 1 ≤ 2 * t * c := by nlinarith [htc_pos]
    zify [htwo_ge_one]
    ring
  have hb_mod4 : b % 4 = 3 := by
    have hb_eq : b = 4 * (t * c - 1) + 3 := by
      apply Nat.succ.inj
      rw [Nat.succ_eq_add_one, hb_succ]
      have htc_ge_one : 1 ≤ t * c := Nat.succ_le_of_lt htc_pos
      zify [htc_ge_one]
      ring
    rw [hb_eq]
    simp
  have hb_mod_c : ((b : ℤ) % (c : ℤ)) = ((-1 : ℤ) % (c : ℤ)) := by
    apply Int.ModEq.eq
    rw [Int.modEq_iff_dvd]
    refine ⟨-(4 * (t : ℤ)), ?_⟩
    have hb_succ_int : (b : ℤ) + 1 = (4 * t * c : ℕ) := by
      exact_mod_cast hb_succ
    have hb_succ_int' : (b : ℤ) + 1 = 4 * (t : ℤ) * (c : ℤ) := by
      simpa using hb_succ_int
    calc
      (-1 : ℤ) - (b : ℤ) = -((b : ℤ) + 1) := by ring
      _ = -(4 * (t : ℤ) * (c : ℤ)) := by rw [hb_succ_int']
      _ = (c : ℤ) * -(4 * (t : ℤ)) := by ring
  have hbc : jacobiSym (b : ℤ) c = jacobiSym (-1) c := by
    exact jacobiSym.mod_left' hb_mod_c
  have hqr := jacobiSym.quadratic_reciprocity_if
    (a := c) (b := b) (Nat.odd_iff.mp hcodd) (Nat.odd_iff.mp hb_odd)
  rw [← hqr]
  rw [hbc]
  rcases Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp hcodd) with hc1 | hc3
  · have hif : ¬ (c % 4 = 3 ∧ b % 4 = 3) := by omega
    simp [hif, jacobiSym.at_neg_one hcodd, ZMod.χ₄_nat_one_mod_four hc1]
  · have hif : c % 4 = 3 ∧ b % 4 = 3 := ⟨hc3, hb_mod4⟩
    simp [hif, jacobiSym.at_neg_one hcodd, ZMod.χ₄_nat_three_mod_four hc3]

/-- Elementary Jacobi-symbol witness used in the rank-two endpoint:
`J(c | 4tc - 1) = 1` for positive `c,t`.  The even step removes a factor of
`2`, since `4tc - 1 ≡ 7 (mod 8)` when `c` is even. -/
private lemma jacobiSym_nat_four_mul_sub_one_eq_one
    (c t : ℕ) (hc : 0 < c) (ht : 0 < t) :
    jacobiSym (c : ℤ) (4 * t * c - 1) = 1 := by
  induction c using Nat.strongRecOn generalizing t with
  | ind c ih =>
    by_cases hcodd : Odd c
    · exact jacobiSym_nat_four_mul_sub_one_eq_one_of_odd c t hc ht hcodd
    · have hceven : Even c := Nat.not_odd_iff_even.mp hcodd
      let d := c / 2
      have hc_eq : c = 2 * d := by
        dsimp [d]
        exact (Nat.two_mul_div_two_of_even hceven).symm
      have hd_pos : 0 < d := by nlinarith
      have hd_lt : d < c := by nlinarith
      let b := 4 * t * c - 1
      have htc_pos : 0 < t * c := Nat.mul_pos ht hc
      have hprod_pos : 0 < 4 * t * c := by nlinarith [htc_pos]
      have hprod_ge_one : 1 ≤ 4 * t * c := Nat.succ_le_of_lt hprod_pos
      have hb_succ : b + 1 = 4 * t * c := by
        dsimp [b]
        exact Nat.sub_add_cancel hprod_ge_one
      have hb_odd : Odd b := by
        refine ⟨2 * t * c - 1, ?_⟩
        apply Nat.succ.inj
        rw [Nat.succ_eq_add_one, hb_succ]
        have htwo_ge_one : 1 ≤ 2 * t * c := by nlinarith [htc_pos]
        zify [htwo_ge_one]
        ring
      have hb_mod8 : b % 8 = 7 := by
        have htd_pos : 0 < t * d := Nat.mul_pos ht hd_pos
        have hb_eq : b = 8 * (t * d - 1) + 7 := by
          apply Nat.succ.inj
          rw [Nat.succ_eq_add_one, hb_succ]
          have htd_ge_one : 1 ≤ t * d := Nat.succ_le_of_lt htd_pos
          rw [hc_eq]
          zify [htd_ge_one]
          ring
        rw [hb_eq]
        simp
      have hc_even_int : ((c : ℤ) % 2 = 0) := by
        exact_mod_cast (Nat.even_iff.mp hceven)
      have hb_odd_mod : b % 2 = 1 := Nat.odd_iff.mp hb_odd
      have hstep := jacobiSym.even_odd (a := (c : ℤ)) (b := b)
        hc_even_int hb_odd_mod
      have hnot : ¬ (b % 8 = 3 ∨ b % 8 = 5) := by omega
      simp [hnot] at hstep
      have hc_div : (c : ℤ) / 2 = (d : ℤ) := by
        rw [hc_eq]
        norm_num
      rw [hc_div] at hstep
      rw [← hstep]
      have hb_eq_ih : b = 4 * (2 * t) * d - 1 := by
        dsimp [b]
        rw [hc_eq]
        ring_nf
      rw [hb_eq_ih]
      exact ih d hd_lt (2 * t) hd_pos (by nlinarith [ht])

/-- The elementary Jacobi-symbol calculation left after using
`polarDeterminant(L) = 4 * pairingDeterminant(L)` in rank two. -/
theorem jacobiSym_neg_four_mul_modulus_pred_eq_neg_one
    (c : ℕ) (hc : 0 < c) :
    jacobiSym (-(4 * (c : ℤ))) (16 * c - 1) = -1 := by
  let b := 16 * c - 1
  have hc_pos_prod : 0 < 16 * c := by nlinarith [hc]
  have hb_odd : Odd b := by
    refine ⟨8 * c - 1, ?_⟩
    apply Nat.succ.inj
    dsimp [b]
    have hge : 1 ≤ 16 * c := Nat.succ_le_of_lt hc_pos_prod
    rw [Nat.sub_add_cancel hge]
    have h8ge : 1 ≤ 8 * c := by nlinarith [hc]
    zify [h8ge]
    ring
  have hb_mod4 : b % 4 = 3 := by
    have hb_eq : b = 4 * (4 * c - 1) + 3 := by
      apply Nat.succ.inj
      dsimp [b]
      have hge : 1 ≤ 16 * c := Nat.succ_le_of_lt hc_pos_prod
      rw [Nat.sub_add_cancel hge]
      have h4ge : 1 ≤ 4 * c := by nlinarith [hc]
      zify [h4ge]
      ring
    rw [hb_eq]
    simp
  have hneg := jacobiSym.neg (4 * (c : ℤ)) hb_odd
  rw [hneg]
  have hchi : ZMod.χ₄ b = -1 := ZMod.χ₄_nat_three_mod_four hb_mod4
  rw [hchi]
  have hb_odd_mod : b % 2 = 1 := Nat.odd_iff.mp hb_odd
  have hdiv := jacobiSym.div_four_left (a := 4 * (c : ℤ)) (b := b)
    (by norm_num) hb_odd_mod
  have hfour : jacobiSym (4 * (c : ℤ)) b = jacobiSym (c : ℤ) b := by
    rw [← hdiv]
    congr
    norm_num
  rw [hfour]
  have hb_eq : b = 4 * 4 * c - 1 := by
    dsimp [b]
  rw [hb_eq, jacobiSym_nat_four_mul_sub_one_eq_one c 4 hc (by norm_num)]
  norm_num

/-- The lattice-specific rank-two endpoint witness, derived from the narrower
integer Jacobi-symbol step above.  At the unit `m - 1` modulo
`m = 4 * |-polarDeterminant(L)|`, the concrete numerator `D = -polarDeterminant(L)` has Jacobi value
`-1`.  Lean below turns this single witness into nontriviality of the
concrete fixed-modulus Jacobi Dirichlet character. -/
theorem goodPrimeEvenCharacterJacobi_modulus_pred_eq_neg_one
    (L : PositiveDefiniteIntegralLattice n) (hn : n = 2 * 1) :
    jacobiSym (goodPrimeEvenCharacterDiscriminant L 1)
      (goodPrimeEvenDirichletModulus L 1 - 1) = -1 := by
  have hn2 : n = 2 := by omega
  subst n
  have hform_pos : 0 < L.pairingDeterminant := by
    have hdisc := L.polarDeterminant_pos
    rw [L.polarDeterminant_eq_two_pow_mul_pairingDeterminant] at hdisc
    norm_num at hdisc
    exact hdisc
  let c : ℕ := L.pairingDeterminant.natAbs
  have hc : 0 < c := Int.natAbs_pos.mpr (ne_of_gt hform_pos)
  have hc_cast : (c : ℤ) = L.pairingDeterminant := by
    dsimp [c]
    exact Int.natAbs_of_nonneg (le_of_lt hform_pos)
  have hdisc_eq : L.polarDeterminant = 4 * (c : ℤ) := by
    rw [L.polarDeterminant_eq_two_pow_mul_pairingDeterminant]
    norm_num
    rw [hc_cast]
  have hD :
      goodPrimeEvenCharacterDiscriminant L 1 =
        -(4 * (c : ℤ)) := by
    rw [goodPrimeEvenCharacterDiscriminant, hdisc_eq]
    norm_num
  have hmod :
      goodPrimeEvenDirichletModulus L 1 = 16 * c := by
    rw [goodPrimeEvenDirichletModulus, hD, Int.natAbs_neg,
      Int.natAbs_mul, Int.natAbs_natCast]
    norm_num
    ring
  rw [hD, hmod]
  exact jacobiSym_neg_four_mul_modulus_pred_eq_neg_one c hc

/-- The concrete fixed-modulus Jacobi Dirichlet character is nontrivial at the
rank-two endpoint.  The only remaining source input is the explicit Jacobi
value at the unit `m - 1`; all character packaging and evaluation at that unit
is formal. -/
theorem goodPrimeEvenJacobiDirichletCharacter_ne_one
    (L : PositiveDefiniteIntegralLattice n) (hn : n = 2 * 1) :
    goodPrimeEvenJacobiDirichletCharacter L 1 ≠ 1 := by
  let m := goodPrimeEvenDirichletModulus L 1
  let D := goodPrimeEvenCharacterDiscriminant L 1
  have hm_pos : 0 < m := by
    dsimp [m]
    exact goodPrimeEvenDirichletModulus_pos L 1
  have hm_one : 1 ≤ m := Nat.succ_le_of_lt hm_pos
  have hcop : Nat.Coprime (m - 1) m := by
    exact (Nat.coprime_self_sub_left (m := 1) (n := m) hm_one).mpr
      (Nat.coprime_one_left m)
  let u : (ZMod m)ˣ := ZMod.unitOfCoprime (m - 1) hcop
  have hu_val : (u : ZMod m).val = m - 1 := by
    rw [show (u : ZMod m) = ((m - 1 : ℕ) : ZMod m) by rfl]
    rw [ZMod.val_natCast]
    exact Nat.mod_eq_of_lt (Nat.sub_lt hm_pos zero_lt_one)
  intro hχ
  have h_eval_jacobi :
      goodPrimeEvenJacobiDirichletCharacter L 1 (u : ZMod m) =
        ((jacobiSym D (m - 1) : ℝ) : ℂ) := by
    simpa [m, D, hu_val] using
      goodPrimeEvenJacobiDirichletCharacter_apply_unit L 1 u
  have h_eval_one :
      goodPrimeEvenJacobiDirichletCharacter L 1 (u : ZMod m) =
        1 := by
    rw [hχ]
    exact MulChar.one_apply_coe u
  have hvalue : ((jacobiSym D (m - 1) : ℝ) : ℂ) = 1 :=
    h_eval_jacobi.symm.trans h_eval_one
  have hsource :=
    goodPrimeEvenCharacterJacobi_modulus_pred_eq_neg_one
      L hn
  rw [show D = goodPrimeEvenCharacterDiscriminant L 1 by rfl,
    show m = goodPrimeEvenDirichletModulus L 1 by rfl,
    hsource] at hvalue
  norm_num at hvalue

/-- The Dirichlet character used by the even-rank Euler-product package.  In
the active even-rank branch this is the concrete fixed-modulus Jacobi
Dirichlet character; outside that branch it is the principal character. -/
noncomputable def goodPrimeEvenDirichletCharacter
    (L : PositiveDefiniteIntegralLattice n) (s : ℕ) :
    DirichletCharacter ℂ (goodPrimeEvenDirichletModulus L s) :=
  if _hn : n = 2 * s then
    goodPrimeEvenJacobiDirichletCharacter L s
  else
    1

/-- The chosen Dirichlet character agrees with the good-prime Jacobi-symbol
quadratic value away from the bad primes. -/
theorem goodPrimeQuadraticCharacter_eq_dirichletCharacter
    (L : PositiveDefiniteIntegralLattice n) (s : ℕ) (p : {p : ℕ // Nat.Prime p})
    (hp : p ∉ massBadPrimeSet L) (hn : n = 2 * s) :
    (((goodPrimeQuadraticCharacter L p : ℝ) : ℂ)) =
      goodPrimeEvenDirichletCharacter L s p.1 :=
by
  rw [goodPrimeEvenDirichletCharacter, dif_pos hn]
  exact goodPrimeQuadraticCharacter_eq_jacobiDirichletCharacter
    L s p hp hn

/-- The remaining fixed-modulus source supplies only the rank-two endpoint
nontriviality of the concrete Jacobi Dirichlet character. -/
theorem goodPrimeEvenDirichletCharacter_ne_one
    (L : PositiveDefiniteIntegralLattice n) (hn : n = 2 * 1) :
    goodPrimeEvenDirichletCharacter L 1 ≠ 1 := by
  rw [goodPrimeEvenDirichletCharacter, dif_pos hn]
  exact goodPrimeEvenJacobiDirichletCharacter_ne_one L hn

/-- The chosen fixed-modulus character is quadratic in the even-rank branch. -/
theorem goodPrimeEvenDirichletCharacter_sq
    (L : PositiveDefiniteIntegralLattice n) (s : ℕ) (hn : n = 2 * s) :
    goodPrimeEvenDirichletCharacter L s ^ 2 = 1 := by
  rw [goodPrimeEvenDirichletCharacter, dif_pos hn]
  exact goodPrimeEvenJacobiDirichletCharacter_sq L s

/-- The cutoff-removed complex Dirichlet `L`-tail attached to the narrowed
even-rank character interface. -/
noncomputable def goodPrimeEvenDirichletComplexTailFactor
    (L : PositiveDefiniteIntegralLattice n) (N s : ℕ) : ℂ :=
  let χ := goodPrimeEvenDirichletCharacter L s
  LSeries (fun m : ℕ => (χ m : ℂ)) ((s : ℕ) : ℂ) /
    ((N + 1).primesBelow.prod fun p =>
      (1 - χ p * (p : ℂ) ^ (-((s : ℕ) : ℂ)))⁻¹)

/-- The real-valued cutoff-removed Dirichlet `L`-tail used by the real
Schulze--Pillot product side. -/
noncomputable def goodPrimeEvenDirichletTailFactorOfCharacter
    (L : PositiveDefiniteIntegralLattice n) (N s : ℕ) : ℝ :=
  (goodPrimeEvenDirichletComplexTailFactor L N s).re

/-- The endpoint value for the cutoff-removed Dirichlet `L`-tail at `s = 1`,
defined from the analytic-continuation `LFunction` rather than Mathlib's
plain `LSeries` value, which is only the absolute-convergence/tsum value at
the endpoint. The endpoint theorem proves
convergence to this standard value. -/
noncomputable def goodPrimeEvenCharacterDirichletEndpointComplexTailFactor
    (L : PositiveDefiniteIntegralLattice n) (N : ℕ) : ℂ :=
  let χ := goodPrimeEvenDirichletCharacter L 1
  letI : NeZero (goodPrimeEvenDirichletModulus L 1) :=
    ⟨ne_of_gt (goodPrimeEvenDirichletModulus_pos L 1)⟩
  DirichletCharacter.LFunction χ 1 /
    ((N + 1).primesBelow.prod fun p =>
      (1 - χ p * (p : ℂ) ^ (-((1 : ℕ) : ℂ)))⁻¹)

/-- The real endpoint value for the cutoff-removed Dirichlet `L`-tail at
`s = 1`. -/
noncomputable def goodPrimeEvenCharacterDirichletEndpointTailFactor
    (L : PositiveDefiniteIntegralLattice n) (N : ℕ) : ℝ :=
  (goodPrimeEvenCharacterDirichletEndpointComplexTailFactor L N).re

/-- Cutoff-removed real Dirichlet tail value for the compatibility theorem
targeting all positive `s`: at the endpoint `s = 1` this is the isolated
source-facing endpoint value, while for `1 < s` it is the value constructed
from the chosen Dirichlet character and Mathlib's `L`-series. -/
noncomputable def goodPrimeEvenCharacterDirichletTailFactor
    (L : PositiveDefiniteIntegralLattice n) (N s : ℕ) : ℝ :=
  if s = 1 then
    goodPrimeEvenCharacterDirichletEndpointTailFactor L N
  else
    goodPrimeEvenDirichletTailFactorOfCharacter L N s

/-- One real Euler factor in the Jacobi-symbol character product, embedded in
`ℂ`, agrees with the Euler factor of the chosen Dirichlet character away from
the bad-prime set. -/
lemma goodPrimeEvenCharacterInverseFactor_ofReal_of_not_mem_bad
    (L : PositiveDefiniteIntegralLattice n) (s : ℕ) (p : {p : ℕ // Nat.Prime p})
    (hp : p ∉ massBadPrimeSet L) (hn : n = 2 * s) :
    (((1 - (goodPrimeQuadraticCharacter L p : ℝ) *
        (p.1 : ℝ) ^ (-(s : ℝ)))⁻¹ : ℝ) : ℂ) =
      (1 - goodPrimeEvenDirichletCharacter L s p.1 *
        (p.1 : ℂ) ^ (-((s : ℕ) : ℂ)))⁻¹ := by
  rw [Complex.ofReal_inv, Complex.ofReal_sub, Complex.ofReal_one,
    Complex.ofReal_mul,
    goodPrimeQuadraticCharacter_eq_dirichletCharacter L s p hp hn]
  congr 2
  rw [Complex.ofReal_cpow]
  · congr 1
    norm_num
  · positivity

/-- Finite products of the real Jacobi-symbol character factors embed as the
Dirichlet-character finite products, provided the finite set avoids the bad
primes. -/
lemma goodPrimeEvenCharacterInverseProduct_ofReal_of_forall_not_mem_bad
    (L : PositiveDefiniteIntegralLattice n) (S : Finset {p : ℕ // Nat.Prime p}) (s : ℕ)
    (hS : ∀ p ∈ S, p ∉ massBadPrimeSet L) (hn : n = 2 * s) :
    ((goodPrimeEvenCharacterInverseProduct L S s : ℝ) : ℂ) =
      S.prod fun p =>
        (1 - goodPrimeEvenDirichletCharacter L s p.1 *
          (p.1 : ℂ) ^ (-((s : ℕ) : ℂ)))⁻¹ := by
  rw [goodPrimeEvenCharacterInverseProduct, Complex.ofReal_prod]
  refine Finset.prod_congr rfl ?_
  intro p hp
  exact goodPrimeEvenCharacterInverseFactor_ofReal_of_not_mem_bad
    L s p (hS p hp) hn

/-- The Dirichlet-character Euler factors are nonzero in the half-plane
`Re(s) > 1`. -/
lemma goodPrimeEvenDirichletEulerFactor_ne_zero
    (L : PositiveDefiniteIntegralLattice n) {s : ℕ} (hs : 1 < s) (p : ℕ) (hp : p.Prime) :
    (1 - goodPrimeEvenDirichletCharacter L s p *
        (p : ℂ) ^ (-((s : ℕ) : ℂ)))⁻¹ ≠ 0 := by
  refine inv_ne_zero ?_
  rw [sub_ne_zero]
  intro h
  have hnorm : ‖goodPrimeEvenDirichletCharacter L s p *
      (p : ℂ) ^ (-((s : ℕ) : ℂ))‖ < 1 := by
    have hχ : ‖goodPrimeEvenDirichletCharacter L s p‖ ≤ 1 :=
      (goodPrimeEvenDirichletCharacter L s).norm_le_one p
    have hpHalf : ‖(p : ℂ) ^ (-((s : ℕ) : ℂ))‖ ≤ (1 / 2 : ℝ) :=
      Complex.norm_prime_cpow_le_one_half ⟨p, hp⟩ (by
        norm_num
        exact_mod_cast hs)
    calc
      ‖goodPrimeEvenDirichletCharacter L s p *
          (p : ℂ) ^ (-((s : ℕ) : ℂ))‖
          = ‖goodPrimeEvenDirichletCharacter L s p‖ *
              ‖(p : ℂ) ^ (-((s : ℕ) : ℂ))‖ := norm_mul _ _
      _ ≤ 1 * (1 / 2 : ℝ) :=
          mul_le_mul hχ hpHalf (norm_nonneg _) zero_le_one
      _ < 1 := by norm_num
  have hnorm_eq : ‖goodPrimeEvenDirichletCharacter L s p *
      (p : ℂ) ^ (-((s : ℕ) : ℂ))‖ = 1 := by
    rw [← h, norm_one]
  nlinarith

/-- Complex convergence of the even-rank character tail in the range
`1 < s`, directly from Mathlib's Dirichlet `L`-series Euler product and finite
cutoff cancellation. -/
lemma dirichlet_L_goodPrimeEvenCharacterComplexTail_tendsto_of_one_lt
    (L : PositiveDefiniteIntegralLattice n) (N s : ℕ) (hs : 1 < s) :
    Filter.Tendsto
      (fun M : ℕ => ((M + 1).primesBelow \ (N + 1).primesBelow).prod fun p =>
        (1 - goodPrimeEvenDirichletCharacter L s p *
          (p : ℂ) ^ (-((s : ℕ) : ℂ)))⁻¹)
      Filter.atTop
      (nhds (goodPrimeEvenDirichletComplexTailFactor L N s)) := by
  let χ := goodPrimeEvenDirichletCharacter L s
  let z : ℂ := ((s : ℕ) : ℂ)
  have hz : 1 < z.re := by
    dsimp [z]
    norm_num
    exact_mod_cast hs
  have hzN :
      ((N + 1).primesBelow.prod fun p =>
        (1 - χ p * (p : ℂ) ^ (-z))⁻¹) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr ?_
    intro p hp
    exact goodPrimeEvenDirichletEulerFactor_ne_zero
      (n := n) L hs p (Nat.prime_of_mem_primesBelow hp)
  have hχ := (DirichletCharacter.LSeries_eulerProduct (χ := χ) hz).comp
    (Filter.tendsto_add_atTop_nat 1)
  have hdiv := hχ.div_const
    ((N + 1).primesBelow.prod fun p =>
      (1 - χ p * (p : ℂ) ^ (-z))⁻¹)
  refine Filter.Tendsto.congr' ?_ hdiv
  filter_upwards [Filter.eventually_ge_atTop N] with M hNM
  have hsubset :
      (N + 1).primesBelow ⊆ (M + 1).primesBelow := by
    intro p hp
    rw [Nat.mem_primesBelow] at hp ⊢
    exact ⟨lt_of_lt_of_le hp.1 (Nat.succ_le_succ hNM), hp.2⟩
  rw [Function.comp_def]
  simp only [z, χ]
  rw [← Finset.prod_sdiff hsubset]
  exact mul_div_cancel_right₀ _ hzN

/-- In ranks with `1 < s`, the repository's real-valued even character tail
converges by Mathlib's Dirichlet `L`-series Euler product, once the
Jacobi-symbol quadratic value has been identified with a Dirichlet character away from
the bad primes. -/
theorem dirichlet_L_goodPrimeEvenCharacterInverseProductTendsTo_of_one_lt
    (L : PositiveDefiniteIntegralLattice n) (N s : ℕ)
    (hB : massBadPrimeSet L ⊆ rationalPrimesUpTo N) (hs : 1 < s)
    (hn : n = 2 * s) :
    goodPrimeEvenCharacterInverseProductTendsTo L N s
      (goodPrimeEvenDirichletTailFactorOfCharacter L N s) := by
  unfold goodPrimeEvenCharacterInverseProductTendsTo
  have hcomplex :=
    dirichlet_L_goodPrimeEvenCharacterComplexTail_tendsto_of_one_lt
      (n := n) L N s hs
  have hreal :
      Filter.Tendsto
        (fun M : ℕ =>
          (((M + 1).primesBelow \ (N + 1).primesBelow).prod fun p =>
            (1 - goodPrimeEvenDirichletCharacter L s p *
              (p : ℂ) ^ (-((s : ℕ) : ℂ)))⁻¹).re)
        Filter.atTop
        (nhds (goodPrimeEvenDirichletTailFactorOfCharacter L N s)) := by
    exact Complex.continuous_re.tendsto _ |>.comp hcomplex
  have htail :
      Filter.Tendsto
        (fun M : ℕ =>
          goodPrimeEvenCharacterInverseProduct L
            (rationalPrimesUpTo M \ rationalPrimesUpTo N) s)
        Filter.atTop
        (nhds (goodPrimeEvenDirichletTailFactorOfCharacter L N s)) := by
    refine Filter.Tendsto.congr' ?_ hreal
    filter_upwards with M
    have hnotBad :
        ∀ p ∈ rationalPrimesUpTo M \ rationalPrimesUpTo N,
          p ∉ massBadPrimeSet L := by
      intro p hp
      exact fun hpB => (Finset.mem_sdiff.mp hp).2 (hB hpB)
    have hcast :=
      goodPrimeEvenCharacterInverseProduct_ofReal_of_forall_not_mem_bad
        (n := n) L (rationalPrimesUpTo M \ rationalPrimesUpTo N) s hnotBad hn
    have hmap :
        ((rationalPrimesUpTo M \ rationalPrimesUpTo N).prod fun p =>
          (1 - goodPrimeEvenDirichletCharacter L s p.1 *
            (p.1 : ℂ) ^ (-((s : ℕ) : ℂ)))⁻¹) =
          (((M + 1).primesBelow \ (N + 1).primesBelow).prod fun p =>
            (1 - goodPrimeEvenDirichletCharacter L s p *
              (p : ℂ) ^ (-((s : ℕ) : ℂ)))⁻¹) := by
      rw [← rationalPrimesUpTo_sdiff_map_val_eq_primesBelow_sdiff N M]
      simp [Finset.prod_map, rationalPrimeValEmbedding]
    have hre := congrArg Complex.re hcast
    rw [Complex.ofReal_re] at hre
    exact (hre.trans (congrArg Complex.re hmap)).symm
  exact htail

/-- On and to the right of the endpoint `x = 1`, each Dirichlet Euler-product
multiplier has norm strictly less than one.  This is the elementary factor
estimate needed before proving the remaining locally uniform Euler-product
tail near the endpoint. -/
lemma dirichlet_L_character_endpointRegion_eulerMultiplier_norm_lt_one
    {m : ℕ} (χ : DirichletCharacter ℂ m) {x : ℝ} (hx : 1 ≤ x)
    (p : ℕ) (hp : p.Prime) :
    ‖χ p * (p : ℂ) ^ (-(x : ℂ))‖ < 1 := by
  have hχ : ‖χ p‖ ≤ 1 := χ.norm_le_one p
  have hpHalf : ‖(p : ℂ) ^ (-(x : ℂ))‖ ≤ (1 / 2 : ℝ) := by
    have hmono :
        ‖(p : ℂ) ^ (-(x : ℂ))‖ ≤
          ‖(p : ℂ) ^ (-((1 : ℕ) : ℂ))‖ := by
      refine Complex.norm_natCast_cpow_le_norm_natCast_cpow_of_pos hp.pos ?_
      simpa using (neg_le_neg hx : -x ≤ -(1 : ℝ))
    have hendpoint : ‖(p : ℂ) ^ (-((1 : ℕ) : ℂ))‖ ≤ (1 / 2 : ℝ) := by
      rw [Complex.norm_natCast_cpow_of_pos hp.pos]
      simp only [Complex.neg_re, Nat.cast_one]
      rw [Real.rpow_neg (Nat.cast_nonneg p)]
      norm_num
      simpa [one_div] using
        (inv_le_inv₀
          (by exact_mod_cast hp.pos : (0 : ℝ) < (p : ℝ))
          (by norm_num : (0 : ℝ) < 2)).mpr
          (by exact_mod_cast hp.two_le : (2 : ℝ) ≤ (p : ℝ))
    exact hmono.trans hendpoint
  calc
    ‖χ p * (p : ℂ) ^ (-(x : ℂ))‖
        = ‖χ p‖ * ‖(p : ℂ) ^ (-(x : ℂ))‖ := norm_mul _ _
    _ ≤ 1 * (1 / 2 : ℝ) :=
        mul_le_mul hχ hpHalf (norm_nonneg _) zero_le_one
    _ < 1 := by norm_num

/-- The Dirichlet-character Euler denominators on and to the right of the
endpoint `x = 1` are nonzero. -/
lemma dirichlet_L_character_endpointRegion_eulerDenominator_ne_zero
    {m : ℕ} (χ : DirichletCharacter ℂ m) {x : ℝ} (hx : 1 ≤ x)
    (p : ℕ) (hp : p.Prime) :
    1 - χ p * (p : ℂ) ^ (-(x : ℂ)) ≠ 0 := by
  rw [sub_ne_zero]
  intro h
  have hnorm := dirichlet_L_character_endpointRegion_eulerMultiplier_norm_lt_one
    χ hx p hp
  have hnorm_eq : ‖χ p * (p : ℂ) ^ (-(x : ℂ))‖ = 1 := by
    rw [← h, norm_one]
  linarith

/-- The Dirichlet-character Euler factors at the endpoint `s = 1` are nonzero.
This elementary estimate is the finite-cutoff bookkeeping needed after the
standard endpoint Euler-product theorem is supplied. -/
lemma dirichlet_L_nontrivial_character_endpoint_eulerFactor_ne_zero
    {m : ℕ} (χ : DirichletCharacter ℂ m) (p : ℕ) (hp : p.Prime) :
    (1 - χ p * (p : ℂ) ^ (-((1 : ℕ) : ℂ)))⁻¹ ≠ 0 := by
  simpa using
    inv_ne_zero
      (dirichlet_L_character_endpointRegion_eulerDenominator_ne_zero χ le_rfl p hp)

/-- Each fixed finite Dirichlet Euler product has the expected right-endpoint
limit as the real exponent tends to `1` from the half-plane `1 < x`.  This is
the finite-cutoff continuity input needed for the eventual Abel/uniform
convergence passage from Mathlib's half-plane Euler product to the endpoint
Euler product. -/
lemma dirichlet_L_character_finiteEulerProduct_tendsto_endpoint
    {m : ℕ} (χ : DirichletCharacter ℂ m) (M : ℕ) :
    Filter.Tendsto
      (fun x : ℝ => (M + 1).primesBelow.prod fun p =>
        (1 - χ p * (p : ℂ) ^ (-(x : ℂ)))⁻¹)
      (nhdsWithin (1 : ℝ) (Set.Ioi 1))
      (nhds ((M + 1).primesBelow.prod fun p =>
        (1 - χ p * (p : ℂ) ^ (-((1 : ℕ) : ℂ)))⁻¹)) := by
  refine tendsto_finset_prod ((M + 1).primesBelow) ?_
  intro p hp
  have hpPrime : p.Prime := Nat.prime_of_mem_primesBelow hp
  have hp_ne : (p : ℂ) ≠ 0 := by
    exact_mod_cast hpPrime.ne_zero
  have hpow :
      Filter.Tendsto (fun x : ℝ => (p : ℂ) ^ (-(x : ℂ)))
        (nhdsWithin (1 : ℝ) (Set.Ioi 1))
        (nhds ((p : ℂ) ^ (-((1 : ℕ) : ℂ)))) := by
    have hneg :
        Filter.Tendsto (fun x : ℝ => -(x : ℂ))
          (nhdsWithin (1 : ℝ) (Set.Ioi 1))
          (nhds (-((1 : ℕ) : ℂ))) := by
      simpa using
        (Complex.continuous_ofReal.continuousAt.tendsto.mono_left inf_le_left).neg
    exact hneg.const_cpow (Or.inl hp_ne)
  have hden :
      Filter.Tendsto (fun x : ℝ => 1 - χ p * (p : ℂ) ^ (-(x : ℂ)))
        (nhdsWithin (1 : ℝ) (Set.Ioi 1))
        (nhds (1 - χ p * (p : ℂ) ^ (-((1 : ℕ) : ℂ)))) := by
    exact tendsto_const_nhds.sub (tendsto_const_nhds.mul hpow)
  have hden_ne :
      1 - χ p * (p : ℂ) ^ (-((1 : ℕ) : ℂ)) ≠ 0 := by
    intro hzero
    have hfactor :=
      dirichlet_L_nontrivial_character_endpoint_eulerFactor_ne_zero χ p hpPrime
    rw [hzero, inv_zero] at hfactor
    exact hfactor rfl
  exact hden.inv₀ hden_ne

/-- Mathlib's Dirichlet Euler product, restated for real exponents `x > 1` in
the repository's `(M + 1).primesBelow` cutoff notation.  This is the
half-plane finite-product input for the endpoint Abel/uniform
interchange. -/
lemma dirichlet_L_character_halfplane_complexEulerProduct_tendsto_LSeries
    {m : ℕ} (χ : DirichletCharacter ℂ m) {x : ℝ} (hx : 1 < x) :
    Filter.Tendsto
      (fun M : ℕ => (M + 1).primesBelow.prod fun p =>
        (1 - χ p * (p : ℂ) ^ (-(x : ℂ)))⁻¹)
      Filter.atTop
      (nhds (LSeries (fun n => χ n) (x : ℂ))) := by
  have hxre : 1 < (x : ℂ).re := by
    simpa using hx
  simpa [Function.comp_def] using
    (DirichletCharacter.LSeries_eulerProduct (χ := χ) hxre).comp
      (Filter.tendsto_add_atTop_nat 1)

/-- Mathlib's half-plane Dirichlet Euler product, restated with the infinite
product as the target.  This separates the pointwise `tprod` convergence from
the endpoint-uniformity argument. -/
lemma dirichlet_L_character_halfplane_complexEulerProduct_tendsto_tprod
    {m : ℕ} (χ : DirichletCharacter ℂ m) {x : ℝ} (hx : 1 < x) :
    Filter.Tendsto
      (fun M : ℕ => (M + 1).primesBelow.prod fun p =>
        (1 - χ p * (p : ℂ) ^ (-(x : ℂ)))⁻¹)
      Filter.atTop
      (nhds (∏' p : Nat.Primes,
        (1 - χ p * (p : ℂ) ^ (-(x : ℂ)))⁻¹)) := by
  have hxre : 1 < (x : ℂ).re := by
    simpa using hx
  have htprod :
      (∏' p : Nat.Primes,
          (1 - χ p * (p : ℂ) ^ (-(x : ℂ)))⁻¹) =
        LSeries (fun n => χ n) (x : ℂ) :=
    DirichletCharacter.LSeries_eulerProduct_tprod χ hxre
  simpa [htprod] using
    dirichlet_L_character_halfplane_complexEulerProduct_tendsto_LSeries χ hx

/-- The ordinary Dirichlet-series values in the half-plane tend to Mathlib's
analytic-continuation endpoint value for a nontrivial character.  This is the
boundary-value side needed to upgrade the `1 < s` Euler product to
the endpoint Euler-product theorem. -/
lemma dirichlet_L_nontrivial_character_LSeries_tendsto_LFunction_one
    {m : ℕ} [NeZero m] (χ : DirichletCharacter ℂ m) (hχ : χ ≠ 1) :
    Filter.Tendsto
      (fun x : ℝ => LSeries (fun n => χ n) (x : ℂ))
      (nhdsWithin (1 : ℝ) (Set.Ioi 1))
      (nhds (DirichletCharacter.LFunction χ 1)) := by
  have hcont : ContinuousAt (DirichletCharacter.LFunction χ) (1 : ℂ) :=
    (DirichletCharacter.differentiableAt_LFunction χ (1 : ℂ) (Or.inr hχ)).continuousAt
  have hcast : Filter.Tendsto (fun x : ℝ => (x : ℂ))
      (nhdsWithin (1 : ℝ) (Set.Ioi 1)) (nhds (1 : ℂ)) := by
    exact Complex.continuous_ofReal.continuousAt.tendsto.mono_left inf_le_left
  refine (hcont.tendsto.comp hcast).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hxre : 1 < (x : ℂ).re := by simpa using hx
  simpa using DirichletCharacter.LFunction_eq_LSeries χ hxre

private lemma sum_range_eq_sum_range_mod_of_periodic_of_sum_period_eq_zero
    {A : Type*} [AddCommMonoid A] (f : ℕ → A) {m : ℕ}
    (hperiod : Function.Periodic f m)
    (hzero : (∑ i ∈ Finset.range m, f i) = 0) (N : ℕ) :
    (∑ i ∈ Finset.range N, f i) = ∑ i ∈ Finset.range (N % m), f i := by
  have hblocks (q : ℕ) : (∑ i ∈ Finset.range (q * m), f i) = 0 := by
    induction q with
    | zero => simp
    | succ q ih =>
        rw [Nat.succ_mul, Finset.sum_range_add, ih, zero_add]
        convert hzero using 1
        refine Finset.sum_congr rfl ?_
        intro i hi
        simpa [Nat.add_comm] using (hperiod.nat_mul q) i
  calc
    (∑ i ∈ Finset.range N, f i) =
        ∑ i ∈ Finset.range (N / m * m + N % m), f i := by
      have hdecomp : N / m * m + N % m = N := by
        rw [Nat.mul_comm]
        exact Nat.div_add_mod N m
      rw [hdecomp]
    _ = (∑ i ∈ Finset.range (N / m * m), f i) +
        ∑ i ∈ Finset.range (N % m), f (N / m * m + i) := by
      rw [Finset.sum_range_add]
    _ = ∑ i ∈ Finset.range (N % m), f i := by
      rw [hblocks, zero_add]
      refine Finset.sum_congr rfl ?_
      intro i hi
      simpa [Nat.add_comm] using (hperiod.nat_mul (N / m)) i

/-- A nontrivial Dirichlet character has zero sum on one natural residue
block. This is the natural-indexed form of `MulChar.sum_eq_zero_of_ne_one`. -/
lemma dirichlet_L_nontrivial_character_sum_modulus_eq_zero
    {m : ℕ} [NeZero m] (χ : DirichletCharacter ℂ m) (hχ : χ ≠ 1) :
    (∑ i ∈ Finset.range m, χ i) = 0 := by
  cases m with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ m =>
      rw [← Fin.sum_univ_eq_sum_range]
      calc
        (∑ i : Fin (m + 1), χ (i : ℕ)) = ∑ i : Fin (m + 1), χ i := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          change χ ((i.val : ℕ) : ZMod (m + 1)) = χ (i : ZMod (m + 1))
          apply congrArg χ
          apply ZMod.val_injective (m + 1)
          rw [ZMod.val_natCast_of_lt i.isLt]
          change i.val = i.val
          rfl
        _ = 0 := MulChar.sum_eq_zero_of_ne_one hχ

/-- Every natural ordered prefix of a nontrivial Dirichlet character reduces
exactly to its final incomplete residue block. -/
lemma dirichlet_L_nontrivial_character_naturalPrefix_eq_modulus_remainder
    {m : ℕ} [NeZero m] (χ : DirichletCharacter ℂ m) (hχ : χ ≠ 1)
    (N : ℕ) :
    (∑ i ∈ Finset.range N, χ i) =
      ∑ i ∈ Finset.range (N % m), χ i := by
  apply sum_range_eq_sum_range_mod_of_periodic_of_sum_period_eq_zero
  · intro i
    change χ ((i + m : ℕ) : ZMod m) = χ (i : ZMod m)
    rw [Nat.cast_add, ZMod.natCast_self, add_zero]
  · exact dirichlet_L_nontrivial_character_sum_modulus_eq_zero χ hχ

/-- Natural ordered character prefixes are uniformly bounded by the modulus.
This is the periodic cancellation input for endpoint Dirichlet tests. -/
lemma dirichlet_L_nontrivial_character_naturalPrefix_norm_le_modulus
    {m : ℕ} [NeZero m] (χ : DirichletCharacter ℂ m) (hχ : χ ≠ 1)
    (N : ℕ) :
    ‖∑ i ∈ Finset.range N, χ i‖ ≤ m := by
  rw [dirichlet_L_nontrivial_character_naturalPrefix_eq_modulus_remainder χ hχ]
  calc
    ‖∑ i ∈ Finset.range (N % m), χ i‖ ≤
        ∑ i ∈ Finset.range (N % m), ‖χ i‖ := norm_sum_le _ _
    _ ≤ (Finset.range (N % m)).card • (1 : ℝ) := by
      exact Finset.sum_le_card_nsmul _ _ _ fun i hi => χ.norm_le_one i
    _ = ((N % m : ℕ) : ℝ) := by simp
    _ ≤ (m : ℝ) := by
      exact_mod_cast (Nat.le_of_lt (Nat.mod_lt N (NeZero.pos m)))

/-- A metric endpoint-passage lemma.  If finite products `P M x` converge to
their endpoint values `E M` as `x → 1+`, the limiting half-plane values `F x`
converge to `y`, and the tails `P M x - F x` are uniformly small near the
endpoint for large `M`, then the endpoint products `E M` converge to `y`. -/
lemma tendsto_endpoint_of_eventually_uniform_halfplane_tail
    (P : ℕ → ℝ → ℂ) (E : ℕ → ℂ) (F : ℝ → ℂ) (y : ℂ)
    (hfinite : ∀ M,
      Filter.Tendsto (P M) (nhdsWithin (1 : ℝ) (Set.Ioi (1 : ℝ))) (nhds (E M)))
    (hF : Filter.Tendsto F (nhdsWithin (1 : ℝ) (Set.Ioi (1 : ℝ))) (nhds y))
    (hunif : ∀ ε : ℝ, ε > 0 → ∃ M₀ : ℕ, ∀ M : ℕ, M ≥ M₀ →
      ∀ᶠ (x : ℝ) in nhdsWithin (1 : ℝ) (Set.Ioi (1 : ℝ)),
        dist (P M x) (F x) < ε) :
    Filter.Tendsto E Filter.atTop (nhds y) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hthird : 0 < ε / 3 := by positivity
  rcases hunif (ε / 3) hthird with ⟨M₀, hM₀⟩
  refine ⟨M₀, ?_⟩
  intro M hM
  have hP : ∀ᶠ (x : ℝ) in nhdsWithin (1 : ℝ) (Set.Ioi (1 : ℝ)),
      dist (P M x) (E M) < ε / 3 :=
    (Metric.tendsto_nhds.mp (hfinite M)) (ε / 3) hthird
  have hU : ∀ᶠ (x : ℝ) in nhdsWithin (1 : ℝ) (Set.Ioi (1 : ℝ)),
      dist (P M x) (F x) < ε / 3 :=
    hM₀ M hM
  have hY : ∀ᶠ (x : ℝ) in nhdsWithin (1 : ℝ) (Set.Ioi (1 : ℝ)),
      dist (F x) y < ε / 3 :=
    (Metric.tendsto_nhds.mp hF) (ε / 3) hthird
  rcases (hP.and (hU.and hY)).exists with ⟨x, hxP, hxU, hxY⟩
  calc
    dist (E M) y ≤ dist (E M) (P M x) + dist (P M x) y := by
      exact dist_triangle (E M) (P M x) y
    _ ≤ dist (E M) (P M x) + (dist (P M x) (F x) + dist (F x) y) := by
      gcongr
      exact dist_triangle (P M x) (F x) y
    _ = dist (E M) (P M x) + dist (P M x) (F x) + dist (F x) y := by
      ring
    _ < ε / 3 + ε / 3 + ε / 3 := by
      gcongr
      simpa [dist_comm] using hxP
    _ = ε := by ring

/-- The logarithmic Euler factor differs from its first-order term by the
standard complex-log Taylor remainder.  This is the local estimate
used to reduce the endpoint logarithmic tail to the
first-order prime-character tail plus an absolutely summable quadratic
remainder. -/
lemma dirichlet_L_character_endpointRegion_eulerLog_sub_linear_norm_le
    {m : ℕ} (χ : DirichletCharacter ℂ m) {x : ℝ} (hx : 1 ≤ x)
    (p : ℕ) (hp : p.Prime) :
    ‖(-Complex.log (1 - χ p * (p : ℂ) ^ (-(x : ℂ))) -
        χ p * (p : ℂ) ^ (-(x : ℂ)))‖ ≤
      ‖χ p * (p : ℂ) ^ (-(x : ℂ))‖ ^ 2 *
        (1 - ‖χ p * (p : ℂ) ^ (-(x : ℂ))‖)⁻¹ / 2 := by
  let z : ℂ := χ p * (p : ℂ) ^ (-(x : ℂ))
  have hz : ‖z‖ < 1 := by
    simpa [z] using
      dirichlet_L_character_endpointRegion_eulerMultiplier_norm_lt_one χ hx p hp
  have hlog := Complex.norm_log_one_add_sub_self_le (z := -z) (by simpa [z] using hz)
  calc
    ‖(-Complex.log (1 - χ p * (p : ℂ) ^ (-(x : ℂ))) -
        χ p * (p : ℂ) ^ (-(x : ℂ)))‖ =
        ‖Complex.log (1 + -z) - (-z)‖ := by
      rw [← norm_neg]
      simp [z, sub_eq_add_neg, add_comm]
    _ ≤ ‖z‖ ^ 2 * (1 - ‖z‖)⁻¹ / 2 := by
      simpa [norm_neg] using hlog
    _ =
        ‖χ p * (p : ℂ) ^ (-(x : ℂ))‖ ^ 2 *
          (1 - ‖χ p * (p : ℂ) ^ (-(x : ℂ))‖)⁻¹ / 2 := by
      simp [z]

/-- Uniform `p^{-2}` majorant for the endpoint-region Dirichlet logarithmic
Euler remainder.  This is the comparison estimate needed to turn the
quadratic-remainder endpoint argument into the absolute summability of
`∑ p^{-2}` over rational primes. -/
lemma dirichlet_L_character_endpointRegion_eulerLog_sub_linear_norm_le_inv_sq
    {m : ℕ} (χ : DirichletCharacter ℂ m) {x : ℝ} (hx : 1 ≤ x)
    (p : ℕ) (hp : p.Prime) :
    ‖(-Complex.log (1 - χ p * (p : ℂ) ^ (-(x : ℂ))) -
        χ p * (p : ℂ) ^ (-(x : ℂ)))‖ ≤
      (p : ℝ) ^ (-2 : ℝ) := by
  let z : ℂ := χ p * (p : ℂ) ^ (-(x : ℂ))
  have hmain :=
    dirichlet_L_character_endpointRegion_eulerLog_sub_linear_norm_le χ hx p hp
  have hzHalf : ‖z‖ ≤ (1 / 2 : ℝ) := by
    have hχ : ‖χ p‖ ≤ 1 := χ.norm_le_one p
    have hpHalf : ‖(p : ℂ) ^ (-(x : ℂ))‖ ≤ (1 / 2 : ℝ) := by
      have hmono :
          ‖(p : ℂ) ^ (-(x : ℂ))‖ ≤
            ‖(p : ℂ) ^ (-((1 : ℕ) : ℂ))‖ := by
        refine Complex.norm_natCast_cpow_le_norm_natCast_cpow_of_pos hp.pos ?_
        simpa using (neg_le_neg hx : -x ≤ -(1 : ℝ))
      have hendpoint : ‖(p : ℂ) ^ (-((1 : ℕ) : ℂ))‖ ≤ (1 / 2 : ℝ) := by
        rw [Complex.norm_natCast_cpow_of_pos hp.pos]
        simp only [Complex.neg_re, Nat.cast_one]
        rw [Real.rpow_neg (Nat.cast_nonneg p)]
        norm_num
        simpa [one_div] using
          (inv_le_inv₀
            (by exact_mod_cast hp.pos : (0 : ℝ) < (p : ℝ))
            (by norm_num : (0 : ℝ) < 2)).mpr
            (by exact_mod_cast hp.two_le : (2 : ℝ) ≤ (p : ℝ))
      exact hmono.trans hendpoint
    calc
      ‖z‖ = ‖χ p‖ * ‖(p : ℂ) ^ (-(x : ℂ))‖ := by simp [z]
      _ ≤ 1 * (1 / 2 : ℝ) := by
        exact mul_le_mul hχ hpHalf (norm_nonneg _) zero_le_one
      _ = 1 / 2 := by ring
  have hden_le : (1 - ‖z‖)⁻¹ ≤ (2 : ℝ) := by
    have hpos : 0 < 1 - ‖z‖ := by linarith
    have hhalf_pos : (0 : ℝ) < 1 / 2 := by norm_num
    have hhalf_le : (1 / 2 : ℝ) ≤ 1 - ‖z‖ := by linarith
    have hle : (1 - ‖z‖)⁻¹ ≤ (1 / 2 : ℝ)⁻¹ :=
      (inv_le_inv₀ hpos hhalf_pos).mpr hhalf_le
    simpa using hle
  have hzsq_bound : ‖z‖ ^ 2 * (1 - ‖z‖)⁻¹ / 2 ≤ ‖z‖ ^ 2 := by
    have hzsq_nonneg : 0 ≤ ‖z‖ ^ 2 := sq_nonneg _
    nlinarith [mul_le_mul_of_nonneg_left hden_le hzsq_nonneg]
  have hz_norm_le : ‖z‖ ≤ (p : ℝ) ^ (-x : ℝ) := by
    have hχ : ‖χ p‖ ≤ 1 := χ.norm_le_one p
    have hpow : ‖(p : ℂ) ^ (-(x : ℂ))‖ = (p : ℝ) ^ (-x : ℝ) := by
      rw [Complex.norm_natCast_cpow_of_pos hp.pos]
      simp
    calc
      ‖z‖ = ‖χ p‖ * ‖(p : ℂ) ^ (-(x : ℂ))‖ := by simp [z]
      _ ≤ 1 * ‖(p : ℂ) ^ (-(x : ℂ))‖ := by
        exact mul_le_mul hχ le_rfl (norm_nonneg _) zero_le_one
      _ = (p : ℝ) ^ (-x : ℝ) := by simp [hpow]
  have hzsq_le : ‖z‖ ^ 2 ≤ ((p : ℝ) ^ (-x : ℝ)) ^ 2 := by
    have hpow_nonneg : 0 ≤ (p : ℝ) ^ (-x : ℝ) :=
      Real.rpow_nonneg (Nat.cast_nonneg p) _
    nlinarith [hz_norm_le, norm_nonneg z]
  have hxpow : ((p : ℝ) ^ (-x : ℝ)) ^ 2 ≤ (p : ℝ) ^ (-2 : ℝ) := by
    rw [← Real.rpow_mul_natCast (Nat.cast_nonneg p)]
    have hp_real : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.pos
    have hexp : (-x : ℝ) * (2 : ℝ) ≤ (-2 : ℝ) := by nlinarith
    exact Real.rpow_le_rpow_of_exponent_le hp_real hexp
  calc
    ‖(-Complex.log (1 - χ p * (p : ℂ) ^ (-(x : ℂ))) -
        χ p * (p : ℂ) ^ (-(x : ℂ)))‖
        ≤ ‖z‖ ^ 2 * (1 - ‖z‖)⁻¹ / 2 := by simpa [z] using hmain
    _ ≤ ‖z‖ ^ 2 := hzsq_bound
    _ ≤ ((p : ℝ) ^ (-x : ℝ)) ^ 2 := hzsq_le
    _ ≤ (p : ℝ) ^ (-2 : ℝ) := hxpow

/-- Finite tails in the repository's prime-cutoff notation are differences of
the corresponding cutoff prefixes. -/
lemma primesBelow_tail_sum_eq_prefix_sub {A : Type*} [AddCommGroup A]
    (f : ℕ → A) {M K : ℕ} (hMK : M ≤ K) :
    (((K + 1).primesBelow \ (M + 1).primesBelow).sum f) =
      ((K + 1).primesBelow.sum f) - ((M + 1).primesBelow.sum f) := by
  have hsubset : (M + 1).primesBelow ⊆ (K + 1).primesBelow := by
    intro p hp
    rw [Nat.mem_primesBelow] at hp ⊢
    exact ⟨lt_of_lt_of_le hp.1 (Nat.succ_le_succ hMK), hp.2⟩
  have hsplit :
      ((K + 1).primesBelow.sum f) =
        (((K + 1).primesBelow \ (M + 1).primesBelow).sum f) +
          ((M + 1).primesBelow.sum f) := by
    simpa using
      (Finset.sum_sdiff
        (s₁ := (M + 1).primesBelow) (s₂ := (K + 1).primesBelow)
        (f := f) hsubset).symm
  rw [hsplit]
  abel

/-- The endpoint first-order prime-character tail is exactly the difference of
the two endpoint prime-character cutoff prefixes.  Thus the remaining
endpoint Cauchy-tail source only has to control the prefix sequence, not the
finite-set subtraction bookkeeping. -/
lemma dirichlet_L_character_endpoint_firstOrder_tail_eq_prefix_sub
    {m : ℕ} (χ : DirichletCharacter ℂ m) {M K : ℕ} (hMK : M ≤ K) :
    (((K + 1).primesBelow \ (M + 1).primesBelow).sum fun p =>
      χ p * (p : ℂ) ^ (-((1 : ℕ) : ℂ))) =
      ((K + 1).primesBelow.sum fun p =>
        χ p * (p : ℂ) ^ (-((1 : ℕ) : ℂ))) -
        ((M + 1).primesBelow.sum fun p =>
          χ p * (p : ℂ) ^ (-((1 : ℕ) : ℂ))) := by
  exact primesBelow_tail_sum_eq_prefix_sub
    (fun p => χ p * (p : ℂ) ^ (-((1 : ℕ) : ℂ))) hMK

/-- The Abel-continuity first-order variation tail is the difference between
the half-plane prefix difference and the endpoint prefix difference.  This is
the finite-cutoff identity needed before applying a genuine Abel/Dirichlet
estimate to the remaining variation source. -/
lemma dirichlet_L_character_endpoint_halfplane_firstOrder_variation_tail_eq_prefix_sub
    {m : ℕ} (χ : DirichletCharacter ℂ m) {M K : ℕ} (hMK : M ≤ K) (x : ℝ) :
    (((K + 1).primesBelow \ (M + 1).primesBelow).sum fun p =>
      χ p * ((p : ℂ) ^ (-(x : ℂ)) - (p : ℂ) ^ (-((1 : ℕ) : ℂ)))) =
      (((K + 1).primesBelow.sum fun p =>
        χ p * (p : ℂ) ^ (-(x : ℂ))) -
        ((M + 1).primesBelow.sum fun p =>
          χ p * (p : ℂ) ^ (-(x : ℂ)))) -
        (((K + 1).primesBelow.sum fun p =>
          χ p * (p : ℂ) ^ (-((1 : ℕ) : ℂ))) -
          ((M + 1).primesBelow.sum fun p =>
            χ p * (p : ℂ) ^ (-((1 : ℕ) : ℂ)))) := by
  let S : Finset ℕ := (K + 1).primesBelow \ (M + 1).primesBelow
  let half : ℕ → ℂ := fun p => χ p * (p : ℂ) ^ (-(x : ℂ))
  let endpoint : ℕ → ℂ := fun p => χ p * (p : ℂ) ^ (-((1 : ℕ) : ℂ))
  have htail :
      S.sum (fun p => half p - endpoint p) =
        S.sum half - S.sum endpoint := by
    rw [Finset.sum_sub_distrib]
  have hhalf :
      S.sum half =
        ((K + 1).primesBelow.sum half) -
          ((M + 1).primesBelow.sum half) := by
    simpa [S, half] using primesBelow_tail_sum_eq_prefix_sub half hMK
  have hendpoint :
      S.sum endpoint =
        ((K + 1).primesBelow.sum endpoint) -
          ((M + 1).primesBelow.sum endpoint) := by
    simpa [S, endpoint] using primesBelow_tail_sum_eq_prefix_sub endpoint hMK
  calc
    (((K + 1).primesBelow \ (M + 1).primesBelow).sum fun p =>
        χ p * ((p : ℂ) ^ (-(x : ℂ)) - (p : ℂ) ^ (-((1 : ℕ) : ℂ)))) =
        S.sum (fun p => half p - endpoint p) := by
          refine Finset.sum_congr rfl ?_
          intro p _hp
          simp [half, endpoint, mul_sub]
    _ = S.sum half - S.sum endpoint := htail
    _ = (((K + 1).primesBelow.sum half) -
          ((M + 1).primesBelow.sum half)) -
        (((K + 1).primesBelow.sum endpoint) -
          ((M + 1).primesBelow.sum endpoint)) := by
          rw [hhalf, hendpoint]
    _ = (((K + 1).primesBelow.sum fun p =>
        χ p * (p : ℂ) ^ (-(x : ℂ))) -
        ((M + 1).primesBelow.sum fun p =>
          χ p * (p : ℂ) ^ (-(x : ℂ)))) -
        (((K + 1).primesBelow.sum fun p =>
          χ p * (p : ℂ) ^ (-((1 : ℕ) : ℂ))) -
        ((M + 1).primesBelow.sum fun p =>
            χ p * (p : ℂ) ^ (-((1 : ℕ) : ℂ)))) := rfl

/-- Pointwise factorization of the endpoint-subtracted first-order
half-plane term.  This is the algebraic input for the remaining Abel
summation step: the variable half-plane part is an endpoint first-order term
multiplied by the scalar weight `p^(1-x)-1`. -/
lemma dirichlet_L_character_endpoint_halfplane_firstOrder_variation_factor
    {m : ℕ} (χ : DirichletCharacter ℂ m) {p : ℕ} (hp : p.Prime) (x : ℝ) :
    χ p * ((p : ℂ) ^ (-(x : ℂ)) - (p : ℂ) ^ (-((1 : ℕ) : ℂ))) =
      (χ p * (p : ℂ) ^ (-((1 : ℕ) : ℂ))) *
        ((p : ℂ) ^ ((1 : ℂ) - (x : ℂ)) - 1) := by
  have hp_ne : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hpow : (p : ℂ) ^ (-(x : ℂ)) =
      (p : ℂ) ^ (-((1 : ℕ) : ℂ)) * (p : ℂ) ^ ((1 : ℂ) - (x : ℂ)) := by
    have hexp : -(x : ℂ) = -((1 : ℕ) : ℂ) + ((1 : ℂ) - (x : ℂ)) := by
      ring
    rw [hexp, Complex.cpow_add _ _ hp_ne]
  rw [hpow]
  ring

/-- Tail form of the first-order variation as a weighted endpoint tail. -/
lemma dirichlet_L_character_endpoint_halfplane_firstOrder_variation_tail_eq_weighted_endpoint_tail
    {m : ℕ} (χ : DirichletCharacter ℂ m) {M K : ℕ} (x : ℝ) :
    (((K + 1).primesBelow \ (M + 1).primesBelow).sum fun p =>
      χ p * ((p : ℂ) ^ (-(x : ℂ)) - (p : ℂ) ^ (-((1 : ℕ) : ℂ)))) =
      (((K + 1).primesBelow \ (M + 1).primesBelow).sum fun p =>
        (χ p * (p : ℂ) ^ (-((1 : ℕ) : ℂ))) *
          ((p : ℂ) ^ ((1 : ℂ) - (x : ℂ)) - 1)) := by
  refine Finset.sum_congr rfl ?_
  intro p hp
  have hpPrime : p.Prime :=
    Nat.prime_of_mem_primesBelow (Finset.mem_sdiff.mp hp).1
  exact dirichlet_L_character_endpoint_halfplane_firstOrder_variation_factor χ hpPrime x

/-- Prefix-difference form of the first-order variation as a weighted endpoint
tail.  This is the finite algebraic shape needed for the subsequent Abel
partial-summation inequality. -/
lemma dirichlet_L_character_endpoint_halfplane_firstOrder_variation_prefix_eq_weighted_endpoint_tail
    {m : ℕ} (χ : DirichletCharacter ℂ m) {M K : ℕ} (hMK : M ≤ K) (x : ℝ) :
    ((((K + 1).primesBelow.sum fun p =>
        χ p * (p : ℂ) ^ (-(x : ℂ))) -
      ((M + 1).primesBelow.sum fun p =>
        χ p * (p : ℂ) ^ (-(x : ℂ)))) -
      (((K + 1).primesBelow.sum fun p =>
        χ p * (p : ℂ) ^ (-((1 : ℕ) : ℂ))) -
      ((M + 1).primesBelow.sum fun p =>
        χ p * (p : ℂ) ^ (-((1 : ℕ) : ℂ))))) =
      (((K + 1).primesBelow \ (M + 1).primesBelow).sum fun p =>
        (χ p * (p : ℂ) ^ (-((1 : ℕ) : ℂ))) *
          ((p : ℂ) ^ ((1 : ℂ) - (x : ℂ)) - 1)) := by
  rw [← dirichlet_L_character_endpoint_halfplane_firstOrder_variation_tail_eq_prefix_sub
    χ hMK x]
  exact
    dirichlet_L_character_endpoint_halfplane_firstOrder_variation_tail_eq_weighted_endpoint_tail
      χ x

/-- A finite prime tail in `Nat.primesBelow` notation is the same as a
range-sum with the prime and lower-cutoff conditions inserted into the
summand.  This is the bookkeeping form used by Abel summation over ordinary
integer intervals. -/
lemma primesBelow_tail_sum_eq_indicator_range_sum {A : Type*} [AddCommMonoid A]
    (f : ℕ → A) (M J : ℕ) :
    (Finset.range (J + 1)).sum
        (fun i => if M < i ∧ i.Prime then f i else 0) =
      (((J + 1).primesBelow \ (M + 1).primesBelow).sum f) := by
  have hset :
      (Finset.range (J + 1)).filter (fun i => M < i ∧ i.Prime) =
        (J + 1).primesBelow \ (M + 1).primesBelow := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_sdiff,
      Nat.mem_primesBelow]
    constructor
    · intro hp
      exact ⟨⟨hp.1, hp.2.2⟩, fun h => (not_lt.mpr
        (Nat.succ_le_of_lt hp.2.1)) h.1⟩
    · intro hp
      have hMp : M < p := by
        by_contra hnot
        exact hp.2 ⟨Nat.lt_succ_iff.mpr (Nat.le_of_not_gt hnot), hp.1.2⟩
      exact ⟨hp.1.1, hMp, hp.1.2⟩
  rw [← Finset.sum_filter]
  rw [hset]

/-- Exact Abel summation identity for the weighted endpoint first-order prime
tail.  The partial sums on the right are endpoint tails from the fixed lower
cutoff `M`; this lemma does not bound these partial sums or the
monotone scalar weight variation. -/
lemma dirichlet_L_character_endpoint_weighted_endpoint_tail_eq_sum_Ioc_by_parts
    {m : ℕ} (χ : DirichletCharacter ℂ m) {M K : ℕ} (hMK : M < K) (x : ℝ) :
    (((K + 1).primesBelow \ (M + 1).primesBelow).sum fun p =>
        (χ p * (p : ℂ) ^ (-((1 : ℕ) : ℂ))) *
          ((p : ℂ) ^ ((1 : ℂ) - (x : ℂ)) - 1)) =
      let endpointTail : ℕ → ℂ := fun i =>
        if M < i ∧ i.Prime then χ i * (i : ℂ) ^ (-((1 : ℕ) : ℂ)) else 0
      let weight : ℕ → ℂ := fun i => (i : ℂ) ^ ((1 : ℂ) - (x : ℂ)) - 1
      weight K • ((Finset.range (K + 1)).sum endpointTail) -
        weight (M + 1) • ((Finset.range (M + 1)).sum endpointTail) -
        (Finset.Ioc M (K - 1)).sum fun i =>
          (weight (i + 1) - weight i) •
            ((Finset.range (i + 1)).sum endpointTail) := by
  let endpointTail : ℕ → ℂ := fun i =>
    if M < i ∧ i.Prime then χ i * (i : ℂ) ^ (-((1 : ℕ) : ℂ)) else 0
  let weight : ℕ → ℂ := fun i => (i : ℂ) ^ ((1 : ℂ) - (x : ℂ)) - 1
  have hleft :
      (Finset.Ioc M K).sum (fun i => weight i • endpointTail i) =
        (((K + 1).primesBelow \ (M + 1).primesBelow).sum fun p =>
          (χ p * (p : ℂ) ^ (-((1 : ℕ) : ℂ))) *
            ((p : ℂ) ^ ((1 : ℂ) - (x : ℂ)) - 1)) := by
    have hfilter :
        (Finset.Ioc M K).filter Nat.Prime =
          (K + 1).primesBelow \ (M + 1).primesBelow := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_sdiff,
        Nat.mem_primesBelow]
      constructor
      · intro hp
        exact ⟨⟨Nat.lt_succ_iff.mpr hp.1.2, hp.2⟩,
          fun h => (not_lt.mpr (Nat.succ_le_of_lt hp.1.1)) h.1⟩
      · intro hp
        have hMp : M < p := by
          by_contra hnot
          exact hp.2 ⟨Nat.lt_succ_iff.mpr (Nat.le_of_not_gt hnot), hp.1.2⟩
        exact ⟨⟨hMp, Nat.lt_succ_iff.mp hp.1.1⟩, hp.1.2⟩
    calc
      (Finset.Ioc M K).sum (fun i => weight i • endpointTail i) =
          (Finset.Ioc M K).sum (fun i =>
            if i.Prime then
              (χ i * (i : ℂ) ^ (-((1 : ℕ) : ℂ))) *
                ((i : ℂ) ^ ((1 : ℂ) - (x : ℂ)) - 1)
            else 0) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            have hMi : M < i := (Finset.mem_Ioc.mp hi).1
            by_cases hiPrime : i.Prime
            · simp [endpointTail, weight, hMi, hiPrime, mul_comm]
            · simp [endpointTail, weight, hiPrime]
      _ = ((Finset.Ioc M K).filter Nat.Prime).sum (fun i =>
            (χ i * (i : ℂ) ^ (-((1 : ℕ) : ℂ))) *
              ((i : ℂ) ^ ((1 : ℂ) - (x : ℂ)) - 1)) := by
            rw [Finset.sum_filter]
      _ = (((K + 1).primesBelow \ (M + 1).primesBelow).sum fun p =>
            (χ p * (p : ℂ) ^ (-((1 : ℕ) : ℂ))) *
              ((p : ℂ) ^ ((1 : ℂ) - (x : ℂ)) - 1)) := by
            rw [hfilter]
  have hparts := Finset.sum_Ioc_by_parts weight endpointTail hMK
  rw [← hleft]
  simpa [endpointTail, weight] using hparts

/-- Finite Abel norm estimate for the weighted endpoint first-order prime
tail.  Once the endpoint tail partial sums are bounded by `B`, the weighted
tail is controlled by `B` times the two endpoint weights and the total
variation of the scalar Abel weights. -/
lemma dirichlet_L_character_endpoint_weighted_endpoint_tail_norm_le
    {m : ℕ} (χ : DirichletCharacter ℂ m) {M K : ℕ} (hMK : M < K) (x : ℝ)
    {B : ℝ}
    (hTail : ∀ J : ℕ, M ≤ J → J ≤ K →
      ‖(Finset.range (J + 1)).sum fun i =>
        if M < i ∧ i.Prime then χ i * (i : ℂ) ^ (-((1 : ℕ) : ℂ)) else 0‖ ≤ B) :
    ‖(((K + 1).primesBelow \ (M + 1).primesBelow).sum fun p =>
        (χ p * (p : ℂ) ^ (-((1 : ℕ) : ℂ))) *
          ((p : ℂ) ^ ((1 : ℂ) - (x : ℂ)) - 1))‖ ≤
      B *
        (‖(K : ℂ) ^ ((1 : ℂ) - (x : ℂ)) - 1‖ +
          ‖((M + 1 : ℕ) : ℂ) ^ ((1 : ℂ) - (x : ℂ)) - 1‖ +
          (Finset.Ioc M (K - 1)).sum fun i =>
            ‖((i + 1 : ℕ) : ℂ) ^ ((1 : ℂ) - (x : ℂ)) -
              (i : ℂ) ^ ((1 : ℂ) - (x : ℂ))‖) := by
  let endpointTail : ℕ → ℂ := fun i =>
    if M < i ∧ i.Prime then χ i * (i : ℂ) ^ (-((1 : ℕ) : ℂ)) else 0
  let weight : ℕ → ℂ := fun i => (i : ℂ) ^ ((1 : ℂ) - (x : ℂ)) - 1
  have hidentity :=
    dirichlet_L_character_endpoint_weighted_endpoint_tail_eq_sum_Ioc_by_parts
      χ hMK x
  let a : ℂ := weight K • ((Finset.range (K + 1)).sum endpointTail)
  let b : ℂ := weight (M + 1) • ((Finset.range (M + 1)).sum endpointTail)
  let c : ℂ := (Finset.Ioc M (K - 1)).sum fun i =>
    (weight (i + 1) - weight i) • ((Finset.range (i + 1)).sum endpointTail)
  have hleft :
      (((K + 1).primesBelow \ (M + 1).primesBelow).sum fun p =>
          (χ p * (p : ℂ) ^ (-((1 : ℕ) : ℂ))) *
            ((p : ℂ) ^ ((1 : ℂ) - (x : ℂ)) - 1)) = a - b - c := by
    simpa [endpointTail, weight, a, b, c, add_assoc] using hidentity
  have hnorm_split : ‖a - b - c‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ := by
    have h₁ : ‖a - b - c‖ ≤ ‖a - b‖ + ‖c‖ := norm_sub_le (a - b) c
    have h₂ : ‖a - b‖ ≤ ‖a‖ + ‖b‖ := norm_sub_le a b
    linarith
  have hKtail : ‖(Finset.range (K + 1)).sum endpointTail‖ ≤ B := by
    simpa [endpointTail] using hTail K hMK.le le_rfl
  have hMtail : ‖(Finset.range (M + 1)).sum endpointTail‖ ≤ B := by
    simpa [endpointTail] using hTail M le_rfl hMK.le
  have ha : ‖a‖ ≤ ‖weight K‖ * B := by
    calc
      ‖a‖ = ‖weight K‖ * ‖(Finset.range (K + 1)).sum endpointTail‖ := by
        simp [a]
      _ ≤ ‖weight K‖ * B := by
        exact mul_le_mul_of_nonneg_left hKtail (norm_nonneg _)
  have hb : ‖b‖ ≤ ‖weight (M + 1)‖ * B := by
    calc
      ‖b‖ = ‖weight (M + 1)‖ *
          ‖(Finset.range (M + 1)).sum endpointTail‖ := by
        simp [b]
      _ ≤ ‖weight (M + 1)‖ * B := by
        exact mul_le_mul_of_nonneg_left hMtail (norm_nonneg _)
  have hc : ‖c‖ ≤
      ((Finset.Ioc M (K - 1)).sum fun i => ‖weight (i + 1) - weight i‖) * B := by
    calc
      ‖c‖ ≤ (Finset.Ioc M (K - 1)).sum fun i =>
          ‖(weight (i + 1) - weight i) •
            ((Finset.range (i + 1)).sum endpointTail)‖ := by
        exact norm_sum_le _ _
      _ ≤ (Finset.Ioc M (K - 1)).sum fun i =>
          ‖weight (i + 1) - weight i‖ * B := by
        refine Finset.sum_le_sum ?_
        intro i hi
        have hi' := Finset.mem_Ioc.mp hi
        have hMle : M ≤ i := by omega
        have hiK : i ≤ K := by omega
        have htail_i : ‖(Finset.range (i + 1)).sum endpointTail‖ ≤ B := by
          simpa [endpointTail] using hTail i hMle hiK
        calc
          ‖(weight (i + 1) - weight i) •
              ((Finset.range (i + 1)).sum endpointTail)‖ =
              ‖weight (i + 1) - weight i‖ *
                ‖(Finset.range (i + 1)).sum endpointTail‖ := by
            simp
          _ ≤ ‖weight (i + 1) - weight i‖ * B := by
            exact mul_le_mul_of_nonneg_left htail_i (norm_nonneg _)
      _ = ((Finset.Ioc M (K - 1)).sum fun i =>
          ‖weight (i + 1) - weight i‖) * B := by
        rw [Finset.sum_mul]
  calc
    ‖(((K + 1).primesBelow \ (M + 1).primesBelow).sum fun p =>
        (χ p * (p : ℂ) ^ (-((1 : ℕ) : ℂ))) *
          ((p : ℂ) ^ ((1 : ℂ) - (x : ℂ)) - 1))‖ =
        ‖a - b - c‖ := by rw [hleft]
    _ ≤ ‖a‖ + ‖b‖ + ‖c‖ := hnorm_split
    _ ≤ ‖weight K‖ * B + ‖weight (M + 1)‖ * B +
        ((Finset.Ioc M (K - 1)).sum fun i =>
          ‖weight (i + 1) - weight i‖) * B := by
        linarith
    _ = B *
        (‖(K : ℂ) ^ ((1 : ℂ) - (x : ℂ)) - 1‖ +
          ‖((M + 1 : ℕ) : ℂ) ^ ((1 : ℂ) - (x : ℂ)) - 1‖ +
          (Finset.Ioc M (K - 1)).sum fun i =>
            ‖((i + 1 : ℕ) : ℂ) ^ ((1 : ℂ) - (x : ℂ)) -
              (i : ℂ) ^ ((1 : ℂ) - (x : ℂ))‖) := by
        simp [weight, mul_add, mul_comm]

/-- For positive integer bases, the endpoint Abel scalar weight has the real
form `1 - i^(1-x)` when `x > 1`. -/
lemma complex_nat_cpow_one_sub_norm_eq
    (i : ℕ) (hi : 0 < i) (x : ℝ) (hx : 1 < x) :
    ‖(i : ℂ) ^ ((1 : ℂ) - (x : ℂ)) - 1‖ =
      1 - (i : ℝ) ^ (1 - x) := by
  rw [show (i : ℂ) ^ ((1 : ℂ) - (x : ℂ)) =
      (((i : ℝ) ^ (1 - x) : ℝ) : ℂ) by
    rw [Complex.ofReal_cpow]
    · norm_num
    · exact_mod_cast hi.le]
  rw [← Complex.ofReal_one, ← Complex.ofReal_sub]
  rw [show ‖(((i : ℝ) ^ (1 - x) - 1 : ℝ) : ℂ)‖ =
      |(i : ℝ) ^ (1 - x) - 1| by
    exact RCLike.norm_ofReal _]
  rw [abs_of_nonpos]
  · ring
  · exact sub_nonpos.mpr (Real.rpow_le_one_of_one_le_of_nonpos
      (by exact_mod_cast (Nat.succ_le_of_lt hi)) (by linarith))

/-- Consecutive endpoint Abel scalar weights telescope for `x > 1`. -/
lemma complex_nat_cpow_one_sub_consecutive_norm_eq
    (i : ℕ) (hi : 0 < i) (x : ℝ) (hx : 1 < x) :
    ‖((i + 1 : ℕ) : ℂ) ^ ((1 : ℂ) - (x : ℂ)) -
      (i : ℂ) ^ ((1 : ℂ) - (x : ℂ))‖ =
        (i : ℝ) ^ (1 - x) - ((i + 1 : ℕ) : ℝ) ^ (1 - x) := by
  rw [show ((i + 1 : ℕ) : ℂ) ^ ((1 : ℂ) - (x : ℂ)) =
      ((((i + 1 : ℕ) : ℝ) ^ (1 - x) : ℝ) : ℂ) by
    rw [Complex.ofReal_cpow]
    · norm_num
    · exact_mod_cast (Nat.succ_pos i).le]
  rw [show (i : ℂ) ^ ((1 : ℂ) - (x : ℂ)) =
      (((i : ℝ) ^ (1 - x) : ℝ) : ℂ) by
    rw [Complex.ofReal_cpow]
    · norm_num
    · exact_mod_cast hi.le]
  rw [← Complex.ofReal_sub]
  rw [show ‖((((i + 1 : ℕ) : ℝ) ^ (1 - x) -
      (i : ℝ) ^ (1 - x) : ℝ) : ℂ)‖ =
      |((i + 1 : ℕ) : ℝ) ^ (1 - x) - (i : ℝ) ^ (1 - x)| by
    exact RCLike.norm_ofReal _]
  rw [abs_of_nonpos]
  · ring
  · exact sub_nonpos.mpr (Real.rpow_le_rpow_of_nonpos
      (by exact_mod_cast hi) (by exact_mod_cast (Nat.le_succ i)) (by linarith))

/-- A finite telescoping identity over the interval used by the Abel
summation estimate. -/
lemma sum_Ioc_consecutive_sub (f : ℕ → ℝ) {M K : ℕ} (hMK : M < K) :
    (Finset.Ioc M (K - 1)).sum (fun i => f i - f (i + 1)) =
      f (M + 1) - f K := by
  induction K with
  | zero => omega
  | succ K ih =>
      by_cases hMK_eq : M = K
      · subst M
        rw [show K + 1 - 1 = K by omega]
        simp
      · have hMleK : M ≤ K := Nat.lt_succ_iff.mp hMK
        have hMKlt : M < K := lt_of_le_of_ne hMleK hMK_eq
        have hMleKpred : M ≤ K - 1 := Nat.le_sub_one_of_lt hMKlt
        have hKpos : 1 ≤ K := Nat.one_le_of_lt hMKlt
        rw [show K + 1 - 1 = K by omega]
        conv_lhs => rw [← Nat.sub_add_cancel hKpos]
        rw [Finset.sum_Ioc_succ_top hMleKpred]
        rw [ih hMKlt]
        have h1 : K - 1 + 1 = K := by omega
        rw [h1]
        ring

/-- The scalar Abel weights `i^(1-x)-1` have uniformly bounded total variation
on every finite tail when `x > 1`. -/
lemma dirichlet_L_character_endpoint_abel_weight_total_variation_le_two
    {M K : ℕ} (hMK : M < K) {x : ℝ} (hx : 1 < x) :
    ‖(K : ℂ) ^ ((1 : ℂ) - (x : ℂ)) - 1‖ +
      ‖((M + 1 : ℕ) : ℂ) ^ ((1 : ℂ) - (x : ℂ)) - 1‖ +
      ((Finset.Ioc M (K - 1)).sum fun i =>
        ‖((i + 1 : ℕ) : ℂ) ^ ((1 : ℂ) - (x : ℂ)) -
          (i : ℂ) ^ ((1 : ℂ) - (x : ℂ))‖) ≤ 2 := by
  have hKpos : 0 < K := Nat.pos_of_ne_zero (by omega)
  have hM1pos : 0 < M + 1 := Nat.succ_pos M
  have hsum :
      (Finset.Ioc M (K - 1)).sum (fun i =>
        ‖((i + 1 : ℕ) : ℂ) ^ ((1 : ℂ) - (x : ℂ)) -
          (i : ℂ) ^ ((1 : ℂ) - (x : ℂ))‖) =
      (M + 1 : ℝ) ^ (1 - x) - (K : ℝ) ^ (1 - x) := by
    calc
      (Finset.Ioc M (K - 1)).sum (fun i =>
        ‖((i + 1 : ℕ) : ℂ) ^ ((1 : ℂ) - (x : ℂ)) -
          (i : ℂ) ^ ((1 : ℂ) - (x : ℂ))‖) =
          (Finset.Ioc M (K - 1)).sum (fun i =>
            (i : ℝ) ^ (1 - x) - ((i + 1 : ℕ) : ℝ) ^ (1 - x)) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            have hi_pos : 0 < i := by
              have hMi : M < i := (Finset.mem_Ioc.mp hi).1
              omega
            exact complex_nat_cpow_one_sub_consecutive_norm_eq i hi_pos x hx
      _ = (M + 1 : ℝ) ^ (1 - x) - (K : ℝ) ^ (1 - x) := by
            simpa using
              sum_Ioc_consecutive_sub (fun i => (i : ℝ) ^ (1 - x))
                (hMK := hMK)
  rw [complex_nat_cpow_one_sub_norm_eq K hKpos x hx,
    complex_nat_cpow_one_sub_norm_eq (M + 1) hM1pos x hx, hsum]
  have hKnonneg : 0 ≤ (K : ℝ) ^ (1 - x) := Real.rpow_nonneg (by positivity) _
  norm_num [Nat.cast_add, Nat.cast_one]
  linarith

/-- The finite Abel norm estimate collapses to `2 * B` once the endpoint tail
partial sums are uniformly bounded by `B`. -/
lemma dirichlet_L_character_endpoint_weighted_endpoint_tail_norm_le_two_mul
    {m : ℕ} (χ : DirichletCharacter ℂ m) {M K : ℕ} (hMK : M < K) {x : ℝ}
    (hx : 1 < x) {B : ℝ}
    (hTail : ∀ J : ℕ, M ≤ J → J ≤ K →
      ‖(Finset.range (J + 1)).sum fun i =>
        if M < i ∧ i.Prime then χ i * (i : ℂ) ^ (-((1 : ℕ) : ℂ)) else 0‖ ≤ B) :
    ‖(((K + 1).primesBelow \ (M + 1).primesBelow).sum fun p =>
        (χ p * (p : ℂ) ^ (-((1 : ℕ) : ℂ))) *
          ((p : ℂ) ^ ((1 : ℂ) - (x : ℂ)) - 1))‖ ≤ B * 2 := by
  have hBnonneg : 0 ≤ B := by
    exact (norm_nonneg _).trans (hTail M le_rfl hMK.le)
  exact
    (dirichlet_L_character_endpoint_weighted_endpoint_tail_norm_le
      χ hMK x hTail).trans
      (mul_le_mul_of_nonneg_left
        (dirichlet_L_character_endpoint_abel_weight_total_variation_le_two hMK hx)
        hBnonneg)

private lemma sum_Ioc_sub_succ_eq {w : ℕ → ℝ} {M K : ℕ} (hMK : M < K) :
    (∑ i ∈ Finset.Ioc M (K - 1), (w i - w (i + 1))) = w (M + 1) - w K := by
  induction K with
  | zero => omega
  | succ K ih =>
      simp only [Nat.add_sub_cancel]
      by_cases hM : M < K
      · have hK : 0 < K := lt_of_le_of_lt (Nat.zero_le M) hM
        have hsplit := Finset.sum_Ioc_succ_top (Nat.le_sub_one_of_lt hM)
          (fun i => w i - w (i + 1))
        rw [Nat.sub_add_cancel hK] at hsplit
        rw [hsplit]
        rw [ih hM]
        ring
      · have hMK' : M = K := by omega
        subst K
        simp

/-- Finite Dirichlet-test estimate for natural ordered character tails. The
bound is uniform on the full endpoint region `1 ≤ sigma`, hence in particular
on the strip `1 ≤ sigma ≤ 2`. -/
lemma dirichlet_L_nontrivial_character_naturalCpow_tail_norm_le
    {m : ℕ} [NeZero m] (chi : DirichletCharacter ℂ m) (hchi : chi ≠ 1)
    {M K : ℕ} (hMK : M ≤ K) {sigma : ℝ} (hsigma : 1 ≤ sigma) :
    ‖∑ i ∈ Finset.Ioc M K, chi i * (i : ℂ) ^ (-(sigma : ℂ))‖ ≤
      2 * m / (M + 1) := by
  by_cases hKM : K = M
  · subst K
    simp
    positivity
  have hMKlt : M < K := lt_of_le_of_ne hMK (Ne.symm hKM)
  let weight : ℕ → ℂ := fun i => (i : ℂ) ^ (-(sigma : ℂ))
  have hleft :
      (∑ i ∈ Finset.Ioc M K, weight i • chi i) =
        ∑ i ∈ Finset.Ioc M K, chi i * (i : ℂ) ^ (-(sigma : ℂ)) := by
    refine Finset.sum_congr rfl ?_
    intro i hi
    simp [weight, mul_comm]
  have hparts := Finset.sum_Ioc_by_parts weight (fun i => chi i) hMKlt
  have hidentity :
      (∑ i ∈ Finset.Ioc M K, chi i * (i : ℂ) ^ (-(sigma : ℂ))) =
        weight K • ((Finset.range (K + 1)).sum fun i => chi i) -
          weight (M + 1) • ((Finset.range (M + 1)).sum fun i => chi i) -
          (∑ i ∈ Finset.Ioc M (K - 1),
            (weight (i + 1) - weight i) •
              ((Finset.range (i + 1)).sum fun j => chi j)) := by
    rw [← hleft]
    exact hparts
  have hweight_real (i : ℕ) (hi : 0 < i) :
      weight i = (((i : ℝ) ^ (-sigma : ℝ) : ℝ) : ℂ) := by
    simp only [weight]
    rw [Complex.ofReal_cpow]
    · simp
    · exact_mod_cast hi.le
  have hweight_antitone {i j : ℕ} (hi : 0 < i) (hij : i ≤ j) :
      (j : ℝ) ^ (-sigma : ℝ) ≤ (i : ℝ) ^ (-sigma : ℝ) := by
    exact Real.rpow_le_rpow_of_nonpos
      (by exact_mod_cast hi) (by exact_mod_cast hij) (by linarith)
  have hvariation (i : ℕ) (hi : i ∈ Finset.Ioc M (K - 1)) :
      ‖weight (i + 1) - weight i‖ =
        (i : ℝ) ^ (-sigma : ℝ) - ((i + 1 : ℕ) : ℝ) ^ (-sigma : ℝ) := by
    have hMi : M < i := (Finset.mem_Ioc.mp hi).1
    have hi_pos : 0 < i := lt_of_le_of_lt (Nat.zero_le M) hMi
    rw [hweight_real (i + 1) (Nat.succ_pos i), hweight_real i hi_pos,
      ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonpos (sub_nonpos.mpr (hweight_antitone hi_pos (Nat.le_succ i)))]
    ring
  have hvariation_sum :
      (∑ i ∈ Finset.Ioc M (K - 1), ‖weight (i + 1) - weight i‖) =
        ((M + 1 : ℕ) : ℝ) ^ (-sigma : ℝ) - (K : ℝ) ^ (-sigma : ℝ) := by
    rw [Finset.sum_congr rfl hvariation]
    exact sum_Ioc_sub_succ_eq hMKlt
  have hweight_norm (i : ℕ) (hi : 0 < i) :
      ‖weight i‖ = (i : ℝ) ^ (-sigma : ℝ) := by
    rw [hweight_real i hi, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg i) _)]
  have hprefix (J : ℕ) :
      ‖(Finset.range (J + 1)).sum fun i => chi i‖ ≤ (m : ℝ) := by
    exact dirichlet_L_nontrivial_character_naturalPrefix_norm_le_modulus
      chi hchi (J + 1)
  rw [hidentity]
  calc
    ‖weight K • ((Finset.range (K + 1)).sum fun i => chi i) -
          weight (M + 1) • ((Finset.range (M + 1)).sum fun i => chi i) -
          (∑ i ∈ Finset.Ioc M (K - 1),
            (weight (i + 1) - weight i) •
              ((Finset.range (i + 1)).sum fun j => chi j))‖
        ≤ ‖weight K‖ * m + ‖weight (M + 1)‖ * m +
            (∑ i ∈ Finset.Ioc M (K - 1), ‖weight (i + 1) - weight i‖ * m) := by
      calc
        _ ≤ ‖weight K • ((Finset.range (K + 1)).sum fun i => chi i)‖ +
              ‖weight (M + 1) • ((Finset.range (M + 1)).sum fun i => chi i)‖ +
              ‖∑ i ∈ Finset.Ioc M (K - 1),
                (weight (i + 1) - weight i) •
                  ((Finset.range (i + 1)).sum fun j => chi j)‖ := by
            calc
              _ ≤ ‖weight K • ((Finset.range (K + 1)).sum fun i => chi i) -
                    weight (M + 1) • ((Finset.range (M + 1)).sum fun i => chi i)‖ +
                  ‖∑ i ∈ Finset.Ioc M (K - 1),
                    (weight (i + 1) - weight i) •
                      ((Finset.range (i + 1)).sum fun j => chi j)‖ := norm_sub_le _ _
              _ ≤ _ := by gcongr; exact norm_sub_le _ _
        _ ≤ _ := by
          gcongr
          · simpa using mul_le_mul_of_nonneg_left (hprefix K) (norm_nonneg (weight K))
          · simpa using mul_le_mul_of_nonneg_left (hprefix M) (norm_nonneg (weight (M + 1)))
          · refine le_trans (norm_sum_le _ _) ?_
            gcongr with i hi
            simpa using mul_le_mul_of_nonneg_left (hprefix i)
              (norm_nonneg (weight (i + 1) - weight i))
    _ = 2 * m * ((M + 1 : ℕ) : ℝ) ^ (-sigma : ℝ) := by
      rw [hweight_norm K (by omega), hweight_norm (M + 1) (Nat.succ_pos M),
        ← Finset.sum_mul, hvariation_sum]
      ring
    _ ≤ 2 * m * ((M + 1 : ℕ) : ℝ) ^ (-1 : ℝ) := by
      have hbase : (1 : ℝ) ≤ ((M + 1 : ℕ) : ℝ) := by
        exact_mod_cast (Nat.succ_pos M)
      have hrpow : ((M + 1 : ℕ) : ℝ) ^ (-sigma : ℝ) ≤
          ((M + 1 : ℕ) : ℝ) ^ (-1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hbase (by linarith)
      exact mul_le_mul_of_nonneg_left hrpow
        (mul_nonneg (by norm_num) (Nat.cast_nonneg m))
    _ = 2 * m / (M + 1) := by
      rw [Real.rpow_neg (Nat.cast_nonneg (M + 1)), Real.rpow_one]
      norm_num [div_eq_mul_inv]

/-- A positive-index real-exponent `LSeries.term` has the expected negative
complex-power form used by the finite Dirichlet-test estimate. -/
lemma dirichlet_L_character_LSeries_term_real_eq
    {m : ℕ} (chi : DirichletCharacter ℂ m) {sigma : ℝ} {i : ℕ}
    (hi : i ≠ 0) :
    LSeries.term (fun n : ℕ => chi n) (sigma : ℂ) i =
      chi i * (i : ℂ) ^ (-(sigma : ℂ)) := by
  rw [LSeries.term_of_ne_zero hi, div_eq_mul_inv, ← Complex.cpow_neg]

/-- In the absolute-convergence half-plane, natural `LSeries.term` prefixes
converge to Mathlib's `LSeries` value. -/
lemma dirichlet_L_character_halfplane_naturalPrefix_tendsto_LSeries
    {m : ℕ} (chi : DirichletCharacter ℂ m) {sigma : ℝ} (hsigma : 1 < sigma) :
    Filter.Tendsto
      (fun N : ℕ => (Finset.range (N + 1)).sum
        (LSeries.term (fun n : ℕ => chi n) (sigma : ℂ)))
      Filter.atTop
      (nhds (LSeries (fun n : ℕ => chi n) (sigma : ℂ))) := by
  have hsigma_re : 1 < (sigma : ℂ).re := by simpa
  exact
    ((DirichletCharacter.LSeriesSummable_of_one_lt_re chi hsigma_re).hasSum.tendsto_sum_nat).comp
      (Filter.tendsto_add_atTop_nat 1)

/-- The finite Dirichlet-test bound persists after passing the upper cutoff to
the half-plane `LSeries` limit. -/
lemma dirichlet_L_nontrivial_character_halfplane_naturalPrefix_dist_LSeries_le
    {m : ℕ} [NeZero m] (chi : DirichletCharacter ℂ m) (hchi : chi ≠ 1)
    (M : ℕ) {sigma : ℝ} (hsigma : 1 < sigma) :
    dist
      ((Finset.range (M + 1)).sum
        (LSeries.term (fun n : ℕ => chi n) (sigma : ℂ)))
      (LSeries (fun n : ℕ => chi n) (sigma : ℂ)) ≤
      2 * (m : ℝ) / ((M + 1 : ℕ) : ℝ) := by
  let partialSum : ℕ → ℂ := fun N => (Finset.range (N + 1)).sum
    (LSeries.term (fun n : ℕ => chi n) (sigma : ℂ))
  have hprefix_tendsto : Filter.Tendsto partialSum Filter.atTop
      (nhds (LSeries (fun n : ℕ => chi n) (sigma : ℂ))) := by
    simpa [partialSum] using
      dirichlet_L_character_halfplane_naturalPrefix_tendsto_LSeries chi hsigma
  have hdist_tendsto : Filter.Tendsto (fun K => dist (partialSum M) (partialSum K))
      Filter.atTop
      (nhds (dist (partialSum M) (LSeries (fun n : ℕ => chi n) (sigma : ℂ)))) :=
    tendsto_const_nhds.dist hprefix_tendsto
  apply le_of_tendsto hdist_tendsto
  filter_upwards [Filter.eventually_ge_atTop M] with K hMK
  have hset : Finset.Ioc M K = Finset.Ico (M + 1) (K + 1) := by
    ext i
    simp
  have htail :
      partialSum K - partialSum M =
        ∑ i ∈ Finset.Ioc M K, chi i * (i : ℂ) ^ (-(sigma : ℂ)) := by
    calc
      partialSum K - partialSum M =
          ∑ i ∈ Finset.Ico (M + 1) (K + 1),
            LSeries.term (fun n : ℕ => chi n) (sigma : ℂ) i := by
        simpa [partialSum] using
          (Finset.sum_Ico_eq_sub
            (LSeries.term (fun n : ℕ => chi n) (sigma : ℂ))
            (Nat.succ_le_succ hMK)).symm
      _ = ∑ i ∈ Finset.Ico (M + 1) (K + 1),
            chi i * (i : ℂ) ^ (-(sigma : ℂ)) := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        rw [dirichlet_L_character_LSeries_term_real_eq chi]
        have hi_lower : M + 1 ≤ i := (Finset.mem_Ico.mp hi).1
        omega
      _ = ∑ i ∈ Finset.Ioc M K,
            chi i * (i : ℂ) ^ (-(sigma : ℂ)) := by rw [hset]
  rw [dist_comm, dist_eq_norm, htail]
  simpa [Nat.cast_add, Nat.cast_one] using
    dirichlet_L_nontrivial_character_naturalCpow_tail_norm_le
      chi hchi hMK hsigma.le

/-- Every fixed natural `LSeries.term` prefix is continuous as the real
exponent approaches the endpoint from the right. -/
lemma dirichlet_L_character_finite_LSeries_prefix_tendsto_endpoint
    {m : ℕ} (chi : DirichletCharacter ℂ m) (M : ℕ) :
    Filter.Tendsto
      (fun sigma : ℝ => (Finset.range (M + 1)).sum
        (LSeries.term (fun n : ℕ => chi n) (sigma : ℂ)))
      (nhdsWithin (1 : ℝ) (Set.Ioi 1))
      (nhds ((Finset.range (M + 1)).sum
        (LSeries.term (fun n : ℕ => chi n) (1 : ℂ)))) := by
  refine tendsto_finset_sum (Finset.range (M + 1)) ?_
  intro i hi
  by_cases hi0 : i = 0
  · subst i
    simp [LSeries.term_zero]
  simp only [LSeries.term_of_ne_zero hi0]
  have hcast : Filter.Tendsto (fun sigma : ℝ => (sigma : ℂ))
      (nhdsWithin (1 : ℝ) (Set.Ioi 1)) (nhds (1 : ℂ)) :=
    Complex.continuous_ofReal.continuousAt.tendsto.mono_left inf_le_left
  have hpow : Filter.Tendsto (fun sigma : ℝ => (i : ℂ) ^ (sigma : ℂ))
      (nhdsWithin (1 : ℝ) (Set.Ioi 1)) (nhds ((i : ℂ) ^ (1 : ℂ))) :=
    hcast.const_cpow (Or.inl (by exact_mod_cast hi0))
  exact tendsto_const_nhds.div hpow (by simp [hi0])

/-- Natural ordered endpoint character-series prefixes converge to the
analytic-continuation value `LFunction chi 1`. This is deliberately a
sequential cutoff statement rather than endpoint `Summable`, which would
assert unconditional convergence. -/
lemma dirichlet_L_nontrivial_character_endpoint_naturalPrefix_tendsto_LFunction_one
    {m : ℕ} [NeZero m] (chi : DirichletCharacter ℂ m) (hchi : chi ≠ 1) :
    Filter.Tendsto
      (fun M : ℕ => (Finset.range (M + 1)).sum
        (LSeries.term (fun n : ℕ => chi n) (1 : ℂ)))
      Filter.atTop
      (nhds (DirichletCharacter.LFunction chi 1)) := by
  let P : ℕ → ℝ → ℂ := fun M sigma => (Finset.range (M + 1)).sum
    (LSeries.term (fun n : ℕ => chi n) (sigma : ℂ))
  let E : ℕ → ℂ := fun M => (Finset.range (M + 1)).sum
    (LSeries.term (fun n : ℕ => chi n) (1 : ℂ))
  let F : ℝ → ℂ := fun sigma => LSeries (fun n : ℕ => chi n) (sigma : ℂ)
  apply tendsto_endpoint_of_eventually_uniform_halfplane_tail P E F
    (DirichletCharacter.LFunction chi 1)
  · intro M
    simpa [P, E] using dirichlet_L_character_finite_LSeries_prefix_tendsto_endpoint chi M
  · simpa [F] using
      dirichlet_L_nontrivial_character_LSeries_tendsto_LFunction_one chi hchi
  · intro epsilon hepsilon
    have hden : Filter.Tendsto (fun M : ℕ => (((M + 1 : ℕ) : ℝ)))
        Filter.atTop Filter.atTop :=
      tendsto_natCast_atTop_atTop.comp (Filter.tendsto_add_atTop_nat 1)
    have hbound : Filter.Tendsto
        (fun M : ℕ => 2 * (m : ℝ) / (((M + 1 : ℕ) : ℝ)))
        Filter.atTop (nhds 0) := by
      simpa [div_eq_mul_inv] using
        (Filter.Tendsto.inv_tendsto_atTop hden).const_mul (2 * (m : ℝ))
    have hsmall : ∀ᶠ M : ℕ in Filter.atTop,
        2 * (m : ℝ) / (((M + 1 : ℕ) : ℝ)) < epsilon :=
      (tendsto_order.1 hbound).2 epsilon hepsilon
    rcases (Filter.eventually_atTop.1 hsmall) with ⟨M0, hM0⟩
    refine ⟨M0, ?_⟩
    intro M hM
    filter_upwards [self_mem_nhdsWithin] with sigma hsigma
    have htail :=
      dirichlet_L_nontrivial_character_halfplane_naturalPrefix_dist_LSeries_le
        (m := m) chi hchi M hsigma
    have htail' : dist (P M sigma) (F sigma) ≤
        2 * (m : ℝ) / (((M + 1 : ℕ) : ℝ)) := by
      simpa [P, F] using htail
    exact lt_of_le_of_lt htail' (hM0 M hM)

/-- Quantitative error bound for the natural endpoint character-harmonic
prefix. This is obtained by passing the finite Dirichlet-test tail estimate
to the already identified natural-cutoff endpoint limit. -/
lemma dirichlet_L_nontrivial_character_endpoint_harmonicPrefix_dist_LFunction_one_le
    {m : ℕ} [NeZero m] (chi : DirichletCharacter ℂ m) (hchi : chi ≠ 1)
    (M : ℕ) :
    dist (∑ i ∈ Finset.Icc 1 M, chi i / (i : ℂ))
        (DirichletCharacter.LFunction chi 1) ≤
      2 * (m : ℝ) / (((M + 1 : ℕ) : ℝ)) := by
  let partialSum : ℕ → ℂ := fun K =>
    (Finset.range (K + 1)).sum
      (LSeries.term (fun n : ℕ => chi n) (1 : ℂ))
  have hprefix_tendsto : Filter.Tendsto partialSum Filter.atTop
      (nhds (DirichletCharacter.LFunction chi 1)) := by
    simpa [partialSum] using
      dirichlet_L_nontrivial_character_endpoint_naturalPrefix_tendsto_LFunction_one
        chi hchi
  have hdist_tendsto : Filter.Tendsto (fun K => dist (partialSum M) (partialSum K))
      Filter.atTop
      (nhds (dist (partialSum M) (DirichletCharacter.LFunction chi 1))) :=
    tendsto_const_nhds.dist hprefix_tendsto
  have hbound : dist (partialSum M) (DirichletCharacter.LFunction chi 1) ≤
      2 * (m : ℝ) / (((M + 1 : ℕ) : ℝ)) := by
    apply le_of_tendsto hdist_tendsto
    filter_upwards [Filter.eventually_ge_atTop M] with K hMK
    have hset : Finset.Ioc M K = Finset.Ico (M + 1) (K + 1) := by
      ext i
      simp
    have htail :
        partialSum K - partialSum M =
          ∑ i ∈ Finset.Ioc M K, chi i * (i : ℂ) ^ (-((1 : ℝ) : ℂ)) := by
      calc
        partialSum K - partialSum M =
            ∑ i ∈ Finset.Ico (M + 1) (K + 1),
              LSeries.term (fun n : ℕ => chi n) (1 : ℂ) i := by
          simpa [partialSum] using
            (Finset.sum_Ico_eq_sub
              (LSeries.term (fun n : ℕ => chi n) (1 : ℂ))
              (Nat.succ_le_succ hMK)).symm
        _ = ∑ i ∈ Finset.Ico (M + 1) (K + 1),
              chi i * (i : ℂ) ^ (-((1 : ℝ) : ℂ)) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          have hi_lower : M + 1 ≤ i := (Finset.mem_Ico.mp hi).1
          rw [LSeries.term_of_ne_zero (by omega)]
          rw [show (-((1 : ℝ) : ℂ)) = -(1 : ℂ) by norm_num,
            Complex.cpow_neg_one]
          simp [div_eq_mul_inv]
        _ = ∑ i ∈ Finset.Ioc M K,
              chi i * (i : ℂ) ^ (-((1 : ℝ) : ℂ)) := by rw [hset]
    rw [dist_comm, dist_eq_norm, htail]
    simpa using dirichlet_L_nontrivial_character_naturalCpow_tail_norm_le
      chi hchi hMK (show (1 : ℝ) ≤ 1 by rfl)
  have hprefix :
      partialSum M = ∑ i ∈ Finset.Icc 1 M, chi i / (i : ℂ) := by
    have hset : Finset.Icc 1 M = Finset.Ico 1 (M + 1) := by
      ext i
      simp
    rw [hset]
    have hsum := Finset.sum_Ico_eq_sub
      (LSeries.term (fun n : ℕ => chi n) (1 : ℂ))
      (show 1 ≤ M + 1 by omega)
    calc
      partialSum M = ∑ i ∈ Finset.Ico 1 (M + 1),
          LSeries.term (fun n : ℕ => chi n) (1 : ℂ) i := by
        rw [hsum]
        simp [partialSum, LSeries.term_zero]
      _ = ∑ i ∈ Finset.Ico 1 (M + 1), chi i / (i : ℂ) := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        have hi0 : i ≠ 0 := by
          have hi1 : 1 ≤ i := (Finset.mem_Ico.mp hi).1
          omega
        rw [LSeries.term_of_ne_zero hi0]
        norm_num
  rwa [hprefix] at hbound

/-- The complex log-weighted character term agrees with the real
`log(i) / i` scalar form used in finite Abel summation. -/
lemma dirichlet_L_character_log_div_term_eq
    {m i : ℕ} (chi : DirichletCharacter ℂ m) :
    (Real.log (i : ℝ) : ℂ) * chi i / (i : ℂ) =
      chi i * ((Real.log (i : ℝ) / (i : ℝ) : ℝ) : ℂ) := by
  rw [Complex.ofReal_div]
  norm_num
  ring

/-- Finite Abel bound for the natural log-weighted character tail beginning
after `2`, where `log(x) / x` is decreasing. -/
lemma dirichlet_L_nontrivial_character_logDiv_tail_norm_le
    {m : ℕ} [NeZero m] (chi : DirichletCharacter ℂ m) (hchi : chi ≠ 1)
    {K : ℕ} (hK : 2 ≤ K) :
    ‖∑ i ∈ Finset.Ioc 2 K,
        chi i * ((Real.log (i : ℝ) / (i : ℝ) : ℝ) : ℂ)‖ ≤
      2 * (m : ℝ) * (Real.log 3 / 3) := by
  by_cases hK2 : K = 2
  · subst K
    simp
    positivity
  have h2K : 2 < K := lt_of_le_of_ne hK (Ne.symm hK2)
  let weight : ℕ → ℂ := fun i => ((Real.log (i : ℝ) / (i : ℝ) : ℝ) : ℂ)
  have hleft :
      (∑ i ∈ Finset.Ioc 2 K, weight i • chi i) =
        ∑ i ∈ Finset.Ioc 2 K,
          chi i * ((Real.log (i : ℝ) / (i : ℝ) : ℝ) : ℂ) := by
    refine Finset.sum_congr rfl ?_
    intro i hi
    simp [weight, mul_comm]
  have hparts := Finset.sum_Ioc_by_parts weight (fun i => chi i) h2K
  have hidentity :
      (∑ i ∈ Finset.Ioc 2 K,
          chi i * ((Real.log (i : ℝ) / (i : ℝ) : ℝ) : ℂ)) =
        weight K • ((Finset.range (K + 1)).sum fun i => chi i) -
          weight 3 • ((Finset.range 3).sum fun i => chi i) -
          (∑ i ∈ Finset.Ioc 2 (K - 1),
            (weight (i + 1) - weight i) •
              ((Finset.range (i + 1)).sum fun j => chi j)) := by
    rw [← hleft]
    simpa using hparts
  have hweight_antitone {i j : ℕ} (hi : 3 ≤ i) (hij : i ≤ j) :
      Real.log (j : ℝ) / (j : ℝ) ≤ Real.log (i : ℝ) / (i : ℝ) := by
    apply Real.log_div_self_antitoneOn
    · exact Real.exp_one_lt_three.le.trans (by exact_mod_cast hi)
    · exact Real.exp_one_lt_three.le.trans
        (by exact_mod_cast (le_trans hi hij))
    · exact_mod_cast hij
  have hweight_nonneg (i : ℕ) (hi : 1 ≤ i) :
      0 ≤ Real.log (i : ℝ) / (i : ℝ) := by
    exact div_nonneg (Real.log_nonneg (by exact_mod_cast hi)) (Nat.cast_nonneg i)
  have hweight_norm (i : ℕ) (hi : 1 ≤ i) :
      ‖weight i‖ = Real.log (i : ℝ) / (i : ℝ) := by
    rw [show weight i = ((Real.log (i : ℝ) / (i : ℝ) : ℝ) : ℂ) by rfl,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hweight_nonneg i hi)]
  have hvariation (i : ℕ) (hi : i ∈ Finset.Ioc 2 (K - 1)) :
      ‖weight (i + 1) - weight i‖ =
        Real.log (i : ℝ) / (i : ℝ) -
          Real.log ((i + 1 : ℕ) : ℝ) / ((i + 1 : ℕ) : ℝ) := by
    have hi2 : 2 < i := (Finset.mem_Ioc.mp hi).1
    have hi3 : 3 ≤ i := by omega
    simp only [weight, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_nonpos (sub_nonpos.mpr (hweight_antitone hi3 (Nat.le_succ i)))]
    norm_num [Nat.cast_add, Nat.cast_one]
  have hvariation_sum :
      (∑ i ∈ Finset.Ioc 2 (K - 1), ‖weight (i + 1) - weight i‖) =
        Real.log 3 / 3 - Real.log (K : ℝ) / (K : ℝ) := by
    rw [Finset.sum_congr rfl hvariation]
    simpa using sum_Ioc_consecutive_sub
      (fun i : ℕ => Real.log (i : ℝ) / (i : ℝ)) h2K
  have hprefix (J : ℕ) :
      ‖(Finset.range (J + 1)).sum fun i => chi i‖ ≤ (m : ℝ) :=
    dirichlet_L_nontrivial_character_naturalPrefix_norm_le_modulus chi hchi (J + 1)
  rw [hidentity]
  calc
    ‖weight K • ((Finset.range (K + 1)).sum fun i => chi i) -
          weight 3 • ((Finset.range 3).sum fun i => chi i) -
          (∑ i ∈ Finset.Ioc 2 (K - 1),
            (weight (i + 1) - weight i) •
              ((Finset.range (i + 1)).sum fun j => chi j))‖
        ≤ ‖weight K‖ * m + ‖weight 3‖ * m +
            (∑ i ∈ Finset.Ioc 2 (K - 1), ‖weight (i + 1) - weight i‖ * m) := by
      calc
        _ ≤ ‖weight K • ((Finset.range (K + 1)).sum fun i => chi i)‖ +
              ‖weight 3 • ((Finset.range 3).sum fun i => chi i)‖ +
              ‖∑ i ∈ Finset.Ioc 2 (K - 1),
                (weight (i + 1) - weight i) •
                  ((Finset.range (i + 1)).sum fun j => chi j)‖ := by
            calc
              _ ≤ ‖weight K • ((Finset.range (K + 1)).sum fun i => chi i) -
                    weight 3 • ((Finset.range 3).sum fun i => chi i)‖ +
                  ‖∑ i ∈ Finset.Ioc 2 (K - 1),
                    (weight (i + 1) - weight i) •
                      ((Finset.range (i + 1)).sum fun j => chi j)‖ := norm_sub_le _ _
              _ ≤ _ := by gcongr; exact norm_sub_le _ _
        _ ≤ _ := by
          gcongr
          · simpa using mul_le_mul_of_nonneg_left (hprefix K) (norm_nonneg (weight K))
          · simpa using mul_le_mul_of_nonneg_left (hprefix 2) (norm_nonneg (weight 3))
          · refine le_trans (norm_sum_le _ _) ?_
            gcongr with i hi
            simpa using mul_le_mul_of_nonneg_left (hprefix i)
              (norm_nonneg (weight (i + 1) - weight i))
    _ = 2 * (m : ℝ) * (Real.log 3 / 3) := by
      rw [hweight_norm K (by omega), hweight_norm 3 (by norm_num),
        ← Finset.sum_mul, hvariation_sum]
      ring_nf

/-- Natural prefixes of `(log n) * chi(n) / n` are uniformly bounded. This
is the second periodic-character input to the finite
von-Mangoldt deconvolution. -/
lemma dirichlet_L_nontrivial_character_logWeighted_naturalPrefix_bounded
    {m : ℕ} [NeZero m] (chi : DirichletCharacter ℂ m) (hchi : chi ≠ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ,
      ‖∑ i ∈ Finset.range (N + 1),
        (Real.log (i : ℝ) : ℂ) * chi i / (i : ℂ)‖ ≤ C := by
  let term : ℕ → ℂ := fun i =>
    (Real.log (i : ℝ) : ℂ) * chi i / (i : ℂ)
  let initial : ℝ := ∑ i ∈ Finset.range 3, ‖term i‖
  let tailBound : ℝ := 2 * (m : ℝ) * (Real.log 3 / 3)
  refine ⟨initial + tailBound, ?_, ?_⟩
  · exact add_nonneg (Finset.sum_nonneg fun i hi => norm_nonneg _)
      (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg m))
        (div_nonneg (Real.log_nonneg (by norm_num)) (by norm_num)))
  intro N
  by_cases hN : N ≤ 2
  · have hsubset : Finset.range (N + 1) ⊆ Finset.range 3 := by
      intro i hi
      simp only [Finset.mem_range] at hi ⊢
      omega
    calc
      ‖∑ i ∈ Finset.range (N + 1), term i‖ ≤
          ∑ i ∈ Finset.range (N + 1), ‖term i‖ := norm_sum_le _ _
      _ ≤ initial := Finset.sum_le_sum_of_subset_of_nonneg hsubset
        (fun i hi hi' => norm_nonneg _)
      _ ≤ initial + tailBound := le_add_of_nonneg_right
        (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg m))
          (div_nonneg (Real.log_nonneg (by norm_num)) (by norm_num)))
  · have hN2 : 2 ≤ N := by omega
    have hset : Finset.Ioc 2 N = Finset.Ico 3 (N + 1) := by
      ext i
      simp
      omega
    have hsplit :
        (∑ i ∈ Finset.range (N + 1), term i) =
          (∑ i ∈ Finset.range 3, term i) + ∑ i ∈ Finset.Ioc 2 N, term i := by
      have htail := Finset.sum_Ico_eq_sub term (show 3 ≤ N + 1 by omega)
      rw [← hset] at htail
      rw [htail]
      abel
    rw [hsplit]
    calc
      ‖(∑ i ∈ Finset.range 3, term i) + ∑ i ∈ Finset.Ioc 2 N, term i‖ ≤
          ‖∑ i ∈ Finset.range 3, term i‖ + ‖∑ i ∈ Finset.Ioc 2 N, term i‖ :=
        norm_add_le _ _
      _ ≤ initial + tailBound := by
        gcongr
        · exact norm_sum_le _ _
        · rw [show (∑ i ∈ Finset.Ioc 2 N, term i) =
              ∑ i ∈ Finset.Ioc 2 N,
                chi i * ((Real.log (i : ℝ) / (i : ℝ) : ℝ) : ℂ) by
            refine Finset.sum_congr rfl ?_
            intro i hi
            exact dirichlet_L_character_log_div_term_eq chi]
          simpa [tailBound] using
            dirichlet_L_nontrivial_character_logDiv_tail_norm_le chi hchi hN2

/-- Finite Dirichlet-hyperbola reindexing. Divisor pairs `(n, d)` with
`1 <= n <= N` correspond to positive pairs `(d, k)` with `k <= N / d` via
`n = d * k`. -/
lemma sum_divisor_hyperbola {A : Type*} [AddCommMonoid A]
    (f : ℕ → ℕ → A) (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, ∑ d ∈ n.divisors, f n d) =
      ∑ d ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 (N / d), f (d * k) d := by
  rw [Finset.sum_sigma', Finset.sum_sigma']
  let S := (Finset.Icc 1 N).sigma fun n => n.divisors
  let T := (Finset.Icc 1 N).sigma fun d => Finset.Icc 1 (N / d)
  let forward : (a : Σ _n : ℕ, ℕ) → a ∈ S → (Σ _d : ℕ, ℕ) :=
    fun a _ => ⟨a.2, a.1 / a.2⟩
  let backward : (a : Σ _d : ℕ, ℕ) → a ∈ T → (Σ _n : ℕ, ℕ) :=
    fun a _ => ⟨a.1 * a.2, a.1⟩
  refine Finset.sum_bij' forward backward ?_ ?_ ?_ ?_ ?_
  · intro a ha
    rcases Finset.mem_sigma.mp ha with ⟨haN, hadiv⟩
    have ha1 : 1 ≤ a.1 := (Finset.mem_Icc.mp haN).1
    have haN' : a.1 ≤ N := (Finset.mem_Icc.mp haN).2
    have had : a.2 ∣ a.1 := (Nat.mem_divisors.mp hadiv).1
    have ha_ne : a.1 ≠ 0 := by omega
    have had_pos : 0 < a.2 := Nat.pos_of_dvd_of_pos had ha1
    have had_le : a.2 ≤ a.1 := Nat.le_of_dvd ha1 had
    simp only [forward, Finset.mem_sigma]
    exact ⟨Finset.mem_Icc.mpr ⟨had_pos, had_le.trans haN'⟩,
      Finset.mem_Icc.mpr ⟨
        (Nat.one_le_div_iff had_pos).mpr had_le,
        Nat.div_le_div_right haN'⟩⟩
  · intro a ha
    rcases Finset.mem_sigma.mp ha with ⟨hadN, hak⟩
    have had_pos : 0 < a.1 := (Finset.mem_Icc.mp hadN).1
    have hak_pos : 0 < a.2 := (Finset.mem_Icc.mp hak).1
    have hak_le : a.2 ≤ N / a.1 := (Finset.mem_Icc.mp hak).2
    have hmul_le : a.1 * a.2 ≤ N := by
      rw [mul_comm]
      exact (Nat.le_div_iff_mul_le had_pos).mp hak_le
    simp only [backward, Finset.mem_sigma]
    exact ⟨Finset.mem_Icc.mpr ⟨Nat.mul_pos had_pos hak_pos, hmul_le⟩,
      Nat.mem_divisors.mpr ⟨dvd_mul_right _ _, (Nat.mul_pos had_pos hak_pos).ne'⟩⟩
  · intro a ha
    apply Sigma.ext
    · simp only [backward, forward]
      rcases Finset.mem_sigma.mp ha with ⟨haN, hadiv⟩
      have had : a.2 ∣ a.1 := (Nat.mem_divisors.mp hadiv).1
      rw [mul_comm, Nat.div_mul_cancel had]
    · simp [backward, forward]
  · intro a ha
    apply Sigma.ext
    · simp [backward, forward]
    · simp only [backward, forward]
      rcases Finset.mem_sigma.mp ha with ⟨hadN, hak⟩
      have had_pos : 0 < a.1 := (Finset.mem_Icc.mp hadN).1
      rw [Nat.mul_div_cancel_left a.2 had_pos]
  · intro a ha
    rcases Finset.mem_sigma.mp ha with ⟨haN, hadiv⟩
    have had : a.2 ∣ a.1 := (Nat.mem_divisors.mp hadiv).1
    simp only [forward]
    rw [mul_comm, Nat.div_mul_cancel had]

/-- Exact finite von-Mangoldt convolution for the log-weighted natural
Dirichlet-character prefix. This is a finite cutoff identity; no infinite
convolution or endpoint summability is used. -/
lemma dirichlet_L_character_logWeighted_prefix_eq_vonMangoldt_convolution
    {m : ℕ} (chi : DirichletCharacter ℂ m) (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N,
        (Real.log (n : ℝ) : ℂ) * chi n / (n : ℂ)) =
      ∑ d ∈ Finset.Icc 1 N,
        ((ArithmeticFunction.vonMangoldt d : ℂ) * chi d / (d : ℂ)) *
          (∑ k ∈ Finset.Icc 1 (N / d), chi k / (k : ℂ)) := by
  calc
    (∑ n ∈ Finset.Icc 1 N,
        (Real.log (n : ℝ) : ℂ) * chi n / (n : ℂ)) =
      ∑ n ∈ Finset.Icc 1 N, ∑ d ∈ n.divisors,
        (ArithmeticFunction.vonMangoldt d : ℂ) * chi n / (n : ℂ) := by
      refine Finset.sum_congr rfl ?_
      intro n hn
      rw [← ArithmeticFunction.vonMangoldt_sum]
      push_cast
      rw [Finset.sum_mul, Finset.sum_div]
    _ = ∑ d ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 (N / d),
        (ArithmeticFunction.vonMangoldt d : ℂ) * chi (d * k) / (d * k : ℂ) := by
      simpa only [Nat.cast_mul] using sum_divisor_hyperbola
        (fun n d => (ArithmeticFunction.vonMangoldt d : ℂ) * chi n / (n : ℂ)) N
    _ = ∑ d ∈ Finset.Icc 1 N,
        ((ArithmeticFunction.vonMangoldt d : ℂ) * chi d / (d : ℂ)) *
          (∑ k ∈ Finset.Icc 1 (N / d), chi k / (k : ℂ)) := by
      refine Finset.sum_congr rfl ?_
      intro d hd
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro k hk
      have hd_pos : 1 ≤ d := (Finset.mem_Icc.mp hd).1
      have hk_pos : 1 ≤ k := (Finset.mem_Icc.mp hk).1
      have hd0 : (d : ℂ) ≠ 0 := by
        exact_mod_cast (show d ≠ 0 by omega)
      have hk0 : (k : ℂ) ≠ 0 := by
        exact_mod_cast (show k ≠ 0 by omega)
      rw [map_mul]
      field_simp

private lemma nat_div_succ_reciprocal_le
    {N d : ℕ} (hN : 1 ≤ N) (hd : 1 ≤ d) :
    1 / (((N / d + 1 : ℕ) : ℝ)) ≤ (d : ℝ) / (N : ℝ) := by
  have hq : 0 < (((N / d + 1 : ℕ) : ℝ)) := by positivity
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
  apply (div_le_div_iff₀ hq hNr).2
  norm_num
  exact_mod_cast (Nat.lt_mul_div_succ N hd).le

private lemma vonMangoldt_Icc_sum_eq_chebyshevPsi (N : ℕ) :
    (∑ d ∈ Finset.Icc 1 N, ArithmeticFunction.vonMangoldt d) =
      Chebyshev.psi (N : ℝ) := by
  rw [Chebyshev.psi]
  congr 1
  ext d
  simp
  omega

/-- The finite von-Mangoldt convolution error is controlled by the ordinary
Chebyshev function. The estimate uses only natural cutoffs, the quantitative
endpoint Dirichlet test, and the elementary floor inequality
`1 / (N / d + 1) <= d / N`. -/
lemma dirichlet_L_nontrivial_character_logWeighted_convolution_error_norm_le_psi
    {m : ℕ} [NeZero m] (chi : DirichletCharacter ℂ m) (hchi : chi ≠ 1)
    {N : ℕ} (hN : 1 ≤ N) :
    ‖(∑ n ∈ Finset.Icc 1 N,
          (Real.log (n : ℝ) : ℂ) * chi n / (n : ℂ)) -
        DirichletCharacter.LFunction chi 1 *
          (∑ d ∈ Finset.Icc 1 N,
            (ArithmeticFunction.vonMangoldt d : ℂ) * chi d / (d : ℂ))‖ ≤
      (2 * (m : ℝ) / (N : ℝ)) * Chebyshev.psi (N : ℝ) := by
  let L1 : ℂ := DirichletCharacter.LFunction chi 1
  let coefficient : ℕ → ℂ := fun d =>
    (ArithmeticFunction.vonMangoldt d : ℂ) * chi d / (d : ℂ)
  let harmonicPrefix : ℕ → ℂ := fun r =>
    ∑ k ∈ Finset.Icc 1 r, chi k / (k : ℂ)
  have hidentity :
      (∑ n ∈ Finset.Icc 1 N,
          (Real.log (n : ℝ) : ℂ) * chi n / (n : ℂ)) -
          L1 * (∑ d ∈ Finset.Icc 1 N, coefficient d) =
        ∑ d ∈ Finset.Icc 1 N,
          coefficient d * (harmonicPrefix (N / d) - L1) := by
    rw [dirichlet_L_character_logWeighted_prefix_eq_vonMangoldt_convolution,
      Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl ?_
    intro d hd
    simp only [coefficient, harmonicPrefix, L1]
    ring
  rw [show DirichletCharacter.LFunction chi 1 = L1 by rfl]
  change ‖(∑ n ∈ Finset.Icc 1 N,
      (Real.log (n : ℝ) : ℂ) * chi n / (n : ℂ)) -
        L1 * (∑ d ∈ Finset.Icc 1 N, coefficient d)‖ ≤ _
  rw [hidentity]
  calc
    ‖∑ d ∈ Finset.Icc 1 N,
        coefficient d * (harmonicPrefix (N / d) - L1)‖ ≤
        ∑ d ∈ Finset.Icc 1 N,
          ‖coefficient d * (harmonicPrefix (N / d) - L1)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ d ∈ Finset.Icc 1 N,
        (2 * (m : ℝ) / (N : ℝ)) * ArithmeticFunction.vonMangoldt d := by
      gcongr with d hdmem
      have hd : 1 ≤ d := (Finset.mem_Icc.mp hdmem).1
      have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
      have hcoefficient : ‖coefficient d‖ ≤
          ArithmeticFunction.vonMangoldt d / (d : ℝ) := by
        simp only [coefficient, norm_div, norm_mul, Complex.norm_real,
          Real.norm_eq_abs, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg,
          Complex.norm_natCast]
        apply div_le_div_of_nonneg_right _ hdR.le
        calc
          ArithmeticFunction.vonMangoldt d * ‖chi d‖ ≤
              ArithmeticFunction.vonMangoldt d * 1 :=
            mul_le_mul_of_nonneg_left
              (by simpa using chi.norm_le_one (d : ZMod m))
              (ArithmeticFunction.vonMangoldt_nonneg (n := d))
          _ = ArithmeticFunction.vonMangoldt d := mul_one _
      have hprefix : ‖harmonicPrefix (N / d) - L1‖ ≤
          2 * (m : ℝ) / (((N / d + 1 : ℕ) : ℝ)) := by
        simpa [harmonicPrefix, L1, dist_eq_norm] using
          dirichlet_L_nontrivial_character_endpoint_harmonicPrefix_dist_LFunction_one_le
            chi hchi (N / d)
      calc
        ‖coefficient d * (harmonicPrefix (N / d) - L1)‖ =
            ‖coefficient d‖ * ‖harmonicPrefix (N / d) - L1‖ := norm_mul _ _
        _ ≤ (ArithmeticFunction.vonMangoldt d / (d : ℝ)) *
              (2 * (m : ℝ) / (((N / d + 1 : ℕ) : ℝ))) := by
          exact mul_le_mul hcoefficient hprefix (norm_nonneg _)
            (div_nonneg ArithmeticFunction.vonMangoldt_nonneg hdR.le)
        _ ≤ (ArithmeticFunction.vonMangoldt d / (d : ℝ)) *
              (2 * (m : ℝ) * ((d : ℝ) / (N : ℝ))) := by
          apply mul_le_mul_of_nonneg_left _
            (div_nonneg ArithmeticFunction.vonMangoldt_nonneg hdR.le)
          calc
            2 * (m : ℝ) / (((N / d + 1 : ℕ) : ℝ)) =
                2 * (m : ℝ) * (1 / (((N / d + 1 : ℕ) : ℝ))) := by ring
            _ ≤ 2 * (m : ℝ) * ((d : ℝ) / (N : ℝ)) :=
              mul_le_mul_of_nonneg_left
                (nat_div_succ_reciprocal_le hN hd) (by positivity)
        _ = (2 * (m : ℝ) / (N : ℝ)) *
              ArithmeticFunction.vonMangoldt d := by
          field_simp
    _ = (2 * (m : ℝ) / (N : ℝ)) * Chebyshev.psi (N : ℝ) := by
      rw [← Finset.mul_sum, vonMangoldt_Icc_sum_eq_chebyshevPsi]

/-- Uniform form of the finite von-Mangoldt convolution error bound, obtained
from the elementary Chebyshev estimate for `psi`. -/
lemma dirichlet_L_nontrivial_character_logWeighted_convolution_error_norm_le
    {m : ℕ} [NeZero m] (chi : DirichletCharacter ℂ m) (hchi : chi ≠ 1)
    {N : ℕ} (hN : 1 ≤ N) :
    ‖(∑ n ∈ Finset.Icc 1 N,
          (Real.log (n : ℝ) : ℂ) * chi n / (n : ℂ)) -
        DirichletCharacter.LFunction chi 1 *
          (∑ d ∈ Finset.Icc 1 N,
            (ArithmeticFunction.vonMangoldt d : ℂ) * chi d / (d : ℂ))‖ ≤
      2 * (m : ℝ) * (Real.log 4 + 4) := by
  calc
    _ ≤ (2 * (m : ℝ) / (N : ℝ)) * Chebyshev.psi (N : ℝ) :=
      dirichlet_L_nontrivial_character_logWeighted_convolution_error_norm_le_psi
        chi hchi hN
    _ ≤ (2 * (m : ℝ) / (N : ℝ)) * ((Real.log 4 + 4) * (N : ℝ)) := by
      apply mul_le_mul_of_nonneg_left
        (Chebyshev.psi_le_const_mul_self (by positivity))
      positivity
    _ = 2 * (m : ℝ) * (Real.log 4 + 4) := by
      field_simp

/-- Twisted von-Mangoldt prefixes at the endpoint are uniformly bounded. The
proof is finite: bounded log-weighted character prefixes and the convolution
error bound control `L(1, chi)` times the prefix, and Mathlib's endpoint
nonvanishing theorem permits division by its norm. -/
lemma dirichlet_L_nontrivial_character_vonMangoldtWeighted_naturalPrefix_bounded
    {m : ℕ} [NeZero m] (chi : DirichletCharacter ℂ m) (hchi : chi ≠ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ,
      ‖∑ d ∈ Finset.Icc 1 N,
        (ArithmeticFunction.vonMangoldt d : ℂ) * chi d / (d : ℂ)‖ ≤ C := by
  rcases dirichlet_L_nontrivial_character_logWeighted_naturalPrefix_bounded
      chi hchi with ⟨CD, hCD, hDbound⟩
  let L1 : ℂ := DirichletCharacter.LFunction chi 1
  let E : ℝ := 2 * (m : ℝ) * (Real.log 4 + 4)
  let termD : ℕ → ℂ := fun n =>
    (Real.log (n : ℝ) : ℂ) * chi n / (n : ℂ)
  let termT : ℕ → ℂ := fun d =>
    (ArithmeticFunction.vonMangoldt d : ℂ) * chi d / (d : ℂ)
  have hL1 : L1 ≠ 0 := by
    exact DirichletCharacter.LFunction_apply_one_ne_zero hchi
  have hL1norm : 0 < ‖L1‖ := norm_pos_iff.mpr hL1
  have hE : 0 ≤ E := by
    dsimp [E]
    positivity
  refine ⟨(CD + E) / ‖L1‖,
    div_nonneg (add_nonneg hCD hE) hL1norm.le, ?_⟩
  intro N
  by_cases hN0 : N = 0
  · subst N
    simp
    exact div_nonneg (add_nonneg hCD hE) hL1norm.le
  have hN : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr hN0
  have hDset : Finset.Icc 1 N = Finset.Ico 1 (N + 1) := by
    ext n
    simp
  have hDprefix :
      (∑ n ∈ Finset.Icc 1 N, termD n) =
        ∑ n ∈ Finset.range (N + 1), termD n := by
    rw [hDset]
    have hsum := Finset.sum_Ico_eq_sub termD (show 1 ≤ N + 1 by omega)
    rw [hsum]
    simp [termD]
  have hD : ‖∑ n ∈ Finset.Icc 1 N, termD n‖ ≤ CD := by
    rw [hDprefix]
    simpa [termD] using hDbound N
  have herr :
      ‖(∑ n ∈ Finset.Icc 1 N, termD n) -
          L1 * (∑ d ∈ Finset.Icc 1 N, termT d)‖ ≤ E := by
    simpa [termD, termT, L1, E] using
      dirichlet_L_nontrivial_character_logWeighted_convolution_error_norm_le
        chi hchi hN
  have hmul :
      ‖L1 * (∑ d ∈ Finset.Icc 1 N, termT d)‖ ≤ CD + E := by
    calc
      ‖L1 * (∑ d ∈ Finset.Icc 1 N, termT d)‖ =
          ‖(∑ n ∈ Finset.Icc 1 N, termD n) -
            ((∑ n ∈ Finset.Icc 1 N, termD n) -
              L1 * (∑ d ∈ Finset.Icc 1 N, termT d))‖ := by ring_nf
      _ ≤ ‖∑ n ∈ Finset.Icc 1 N, termD n‖ +
            ‖(∑ n ∈ Finset.Icc 1 N, termD n) -
              L1 * (∑ d ∈ Finset.Icc 1 N, termT d)‖ := norm_sub_le _ _
      _ ≤ CD + E := add_le_add hD herr
  apply (le_div_iff₀ hL1norm).2
  simpa [norm_mul, mul_comm] using hmul

private lemma higherPrimePower_vonMangoldt_variation_le {i : ℕ} (hi : 1 ≤ i) :
    (1 / (i : ℝ) - 1 / ((i + 1 : ℕ) : ℝ)) *
        (2 * Real.sqrt (i : ℝ) * Real.log (i : ℝ)) ≤
      8 * (i : ℝ) ^ (-(5 / 4 : ℝ)) := by
  have hiR : 0 < (i : ℝ) := by exact_mod_cast hi
  have hlog := Real.log_natCast_le_rpow_div i
    (show (0 : ℝ) < 1 / 4 by norm_num)
  have hgrowth :
      2 * Real.sqrt (i : ℝ) * Real.log (i : ℝ) ≤
        8 * (i : ℝ) ^ (3 / 4 : ℝ) := by
    rw [Real.sqrt_eq_rpow]
    calc
      2 * (i : ℝ) ^ (1 / 2 : ℝ) * Real.log (i : ℝ) ≤
          2 * (i : ℝ) ^ (1 / 2 : ℝ) *
            ((i : ℝ) ^ (1 / 4 : ℝ) / (1 / 4 : ℝ)) := by
        gcongr
      _ = 8 * ((i : ℝ) ^ (1 / 2 : ℝ) * (i : ℝ) ^ (1 / 4 : ℝ)) := by
        ring
      _ = 8 * (i : ℝ) ^ (3 / 4 : ℝ) := by
        rw [← Real.rpow_add hiR]
        norm_num
  have hvariation :
      0 ≤ 1 / (i : ℝ) - 1 / ((i + 1 : ℕ) : ℝ) := by
    rw [sub_nonneg]
    exact one_div_le_one_div_of_le hiR (by norm_num)
  calc
    (1 / (i : ℝ) - 1 / ((i + 1 : ℕ) : ℝ)) *
          (2 * Real.sqrt (i : ℝ) * Real.log (i : ℝ)) ≤
        (1 / (i : ℝ) - 1 / ((i + 1 : ℕ) : ℝ)) *
          (8 * (i : ℝ) ^ (3 / 4 : ℝ)) :=
      mul_le_mul_of_nonneg_left hgrowth hvariation
    _ ≤ (1 / ((i : ℝ) ^ 2)) *
          (8 * (i : ℝ) ^ (3 / 4 : ℝ)) := by
      gcongr
      have hdiff :
          1 / (i : ℝ) - 1 / ((i + 1 : ℕ) : ℝ) =
            1 / ((i : ℝ) * ((i : ℝ) + 1)) := by
        norm_num [Nat.cast_add, Nat.cast_one]
        field_simp
        ring
      rw [hdiff]
      apply one_div_le_one_div_of_le (sq_pos_of_pos hiR)
      nlinarith
    _ = 8 * (i : ℝ) ^ (-(5 / 4 : ℝ)) := by
      have hinv : 1 / ((i : ℝ) ^ 2) = (i : ℝ) ^ (-2 : ℝ) := by
        norm_num [Real.rpow_neg_ofNat, zpow_neg]
        rfl
      calc
        (1 / ((i : ℝ) ^ 2)) * (8 * (i : ℝ) ^ (3 / 4 : ℝ)) =
            8 * ((i : ℝ) ^ (3 / 4 : ℝ) * (i : ℝ) ^ (-2 : ℝ)) := by
          rw [hinv]
          ring
        _ = 8 * (i : ℝ) ^ ((3 / 4 : ℝ) + (-2)) := by
          rw [Real.rpow_add hiR]
        _ = 8 * (i : ℝ) ^ (-(5 / 4 : ℝ)) := by norm_num

/-- The real absolute majorant for the nonprime part of a finite
von-Mangoldt prefix is uniformly bounded. Finite Abel summation expresses its
partial sums through `psi - theta`; Mathlib's square-root Chebyshev bound and
a summable `n^(-5/4)` variation majorant finish the estimate. -/
lemma dirichlet_L_higherPrimePower_vonMangoldt_realPrefix_bounded :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ,
      ∑ d ∈ (Finset.Icc 1 N).filter (fun d => ¬d.Prime),
          ArithmeticFunction.vonMangoldt d / (d : ℝ) ≤ C := by
  let majorant : ℕ → ℝ := fun i => 8 * (i : ℝ) ^ (-(5 / 4 : ℝ))
  have hmajorant : Summable majorant := by
    exact (Real.summable_nat_rpow.mpr (by norm_num)).mul_left 8
  refine ⟨4 + ∑' i : ℕ, majorant i,
    add_nonneg (by norm_num) (tsum_nonneg fun i => by positivity), ?_⟩
  intro N
  by_cases hN0 : N = 0
  · subst N
    simp
    exact add_nonneg (by norm_num) (tsum_nonneg fun i => by positivity)
  have hN : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr hN0
  let a : ℕ → ℝ := fun n =>
    if ¬n.Prime then ArithmeticFunction.vonMangoldt n else 0
  let weight : ℕ → ℝ := fun n => 1 / (n : ℝ)
  let B : ℕ → ℝ := fun J => Chebyshev.psi (J : ℝ) - Chebyshev.theta (J : ℝ)
  have hprefix (J : ℕ) : (Finset.range (J + 1)).sum a = B J := by
    change (Finset.range (J + 1)).sum a =
      Chebyshev.psi (J : ℝ) - Chebyshev.theta (J : ℝ)
    rw [Chebyshev.psi_sub_theta_eq_sum_not_prime]
    have hset : Finset.Ioc 0 ⌊(J : ℝ)⌋₊ = Finset.Ico 1 (J + 1) := by
      ext n
      simp
      omega
    rw [hset, Finset.sum_filter]
    change (Finset.range (J + 1)).sum a = (Finset.Ico 1 (J + 1)).sum a
    rw [Finset.sum_Ico_eq_sub]
    · simp [a, ArithmeticFunction.vonMangoldt_apply, not_isPrimePow_zero]
    · omega
  have hBbound {J : ℕ} (hJ : 1 ≤ J) :
      B J ≤ 2 * Real.sqrt (J : ℝ) * Real.log (J : ℝ) := by
    exact (le_abs_self (B J)).trans
      (by simpa [B] using
        (Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log
          (x := (J : ℝ)) (by exact_mod_cast hJ)))
  have hparts := Finset.sum_Ioc_by_parts weight a (show 0 < N by omega)
  simp_rw [hprefix] at hparts
  have hBzero : B 0 = 0 := by
    simp [B, Chebyshev.psi, Chebyshev.theta]
  have hidentity :
      (∑ i ∈ Finset.Ioc 0 N, weight i * a i) =
        weight N * B N +
          ∑ i ∈ Finset.Ioc 0 (N - 1), (weight i - weight (i + 1)) * B i := by
    rw [show (∑ i ∈ Finset.Ioc 0 N, weight i * a i) =
        ∑ i ∈ Finset.Ioc 0 N, weight i • a i by
      refine Finset.sum_congr rfl ?_
      simp]
    rw [hparts, hBzero]
    simp only [smul_eq_mul, mul_zero, sub_zero]
    rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
    congr 1
    refine Finset.sum_congr rfl ?_
    intro i hi
    ring
  have htarget :
      (∑ d ∈ (Finset.Icc 1 N).filter (fun d => ¬d.Prime),
          ArithmeticFunction.vonMangoldt d / (d : ℝ)) =
        ∑ i ∈ Finset.Ioc 0 N, weight i * a i := by
    have hset : Finset.Icc 1 N = Finset.Ioc 0 N := by
      ext i
      simp
      omega
    rw [hset, Finset.sum_filter]
    refine Finset.sum_congr rfl ?_
    intro i hi
    simp only [a, weight]
    split_ifs <;> ring
  rw [htarget, hidentity]
  have hendpoint : weight N * B N ≤ 4 := by
    have hBN := hBbound hN
    have hlog := Real.log_natCast_le_rpow_div N
      (show (0 : ℝ) < 1 / 2 by norm_num)
    have hlog' : Real.log (N : ℝ) ≤ 2 * Real.sqrt (N : ℝ) := by
      calc
        Real.log (N : ℝ) ≤ (N : ℝ) ^ (1 / 2 : ℝ) / (1 / 2 : ℝ) := hlog
        _ = 2 * Real.sqrt (N : ℝ) := by
          rw [Real.sqrt_eq_rpow]
          ring
    have hsqrt : Real.sqrt (N : ℝ) ^ 2 = (N : ℝ) :=
      Real.sq_sqrt (Nat.cast_nonneg N)
    have hscaled := mul_le_mul_of_nonneg_left hlog'
      (mul_nonneg (show (0 : ℝ) ≤ 2 by norm_num) (Real.sqrt_nonneg (N : ℝ)))
    dsimp [weight]
    rw [show 1 / (N : ℝ) * B N = B N / (N : ℝ) by ring]
    apply (div_le_iff₀ (show (0 : ℝ) < N by exact_mod_cast hN)).2
    nlinarith
  calc
    weight N * B N +
          ∑ i ∈ Finset.Ioc 0 (N - 1), (weight i - weight (i + 1)) * B i ≤
        4 + ∑ i ∈ Finset.Ioc 0 (N - 1), majorant i := by
      gcongr with i hi
      have hi1 : 1 ≤ i := (Finset.mem_Ioc.mp hi).1
      have hvariation : 0 ≤ weight i - weight (i + 1) := by
        dsimp [weight]
        rw [sub_nonneg]
        exact one_div_le_one_div_of_le (by positivity) (by norm_num)
      calc
        (weight i - weight (i + 1)) * B i ≤
            (weight i - weight (i + 1)) *
              (2 * Real.sqrt (i : ℝ) * Real.log (i : ℝ)) :=
          mul_le_mul_of_nonneg_left (hBbound hi1) hvariation
        _ ≤ majorant i := higherPrimePower_vonMangoldt_variation_le hi1
    _ ≤ 4 + ∑' i : ℕ, majorant i := by
      gcongr
      exact Summable.sum_le_tsum (Finset.Ioc 0 (N - 1))
        (fun i hi => by positivity) hmajorant

/-- Exact finite split of the twisted von-Mangoldt prefix into its prime
contribution and its nonprime, hence higher-prime-power, contribution. -/
lemma dirichlet_L_character_vonMangoldtWeighted_prefix_eq_prime_add_higherPrimePower
    {m : ℕ} (chi : DirichletCharacter ℂ m) (N : ℕ) :
    (∑ d ∈ Finset.Icc 1 N,
        (ArithmeticFunction.vonMangoldt d : ℂ) * chi d / (d : ℂ)) =
      ((N + 1).primesBelow.sum fun p =>
        (Real.log (p : ℝ) : ℂ) * chi p / (p : ℂ)) +
      ∑ d ∈ (Finset.Icc 1 N).filter (fun d => ¬d.Prime),
        (ArithmeticFunction.vonMangoldt d : ℂ) * chi d / (d : ℂ) := by
  let term : ℕ → ℂ := fun d =>
    (ArithmeticFunction.vonMangoldt d : ℂ) * chi d / (d : ℂ)
  have hprimeSet :
      (Finset.Icc 1 N).filter Nat.Prime = (N + 1).primesBelow := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_primesBelow]
    constructor
    · rintro ⟨⟨hp1, hpN⟩, hp⟩
      exact ⟨by omega, hp⟩
    · rintro ⟨hpN, hp⟩
      exact ⟨⟨hp.one_le, by omega⟩, hp⟩
  calc
    (∑ d ∈ Finset.Icc 1 N, term d) =
        (∑ d ∈ (Finset.Icc 1 N).filter Nat.Prime, term d) +
          ∑ d ∈ (Finset.Icc 1 N).filter (fun d => ¬d.Prime), term d := by
      rw [Finset.sum_filter_add_sum_filter_not]
    _ = ((N + 1).primesBelow.sum fun p =>
          (Real.log (p : ℝ) : ℂ) * chi p / (p : ℂ)) +
        ∑ d ∈ (Finset.Icc 1 N).filter (fun d => ¬d.Prime), term d := by
      rw [hprimeSet]
      congr 1
      refine Finset.sum_congr rfl ?_
      intro p hp
      simp only [term]
      rw [ArithmeticFunction.vonMangoldt_apply_prime
        (Nat.prime_of_mem_primesBelow hp)]

/-- The higher-prime-power contribution to a twisted finite von-Mangoldt
prefix is uniformly bounded in norm. -/
lemma dirichlet_L_character_higherPrimePower_vonMangoldtPrefix_bounded
    {m : ℕ} (chi : DirichletCharacter ℂ m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ,
      ‖∑ d ∈ (Finset.Icc 1 N).filter (fun d => ¬d.Prime),
        (ArithmeticFunction.vonMangoldt d : ℂ) * chi d / (d : ℂ)‖ ≤ C := by
  rcases dirichlet_L_higherPrimePower_vonMangoldt_realPrefix_bounded with
    ⟨C, hC, hbound⟩
  refine ⟨C, hC, ?_⟩
  intro N
  calc
    ‖∑ d ∈ (Finset.Icc 1 N).filter (fun d => ¬d.Prime),
        (ArithmeticFunction.vonMangoldt d : ℂ) * chi d / (d : ℂ)‖ ≤
      ∑ d ∈ (Finset.Icc 1 N).filter (fun d => ¬d.Prime),
        ‖(ArithmeticFunction.vonMangoldt d : ℂ) * chi d / (d : ℂ)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ d ∈ (Finset.Icc 1 N).filter (fun d => ¬d.Prime),
        ArithmeticFunction.vonMangoldt d / (d : ℝ) := by
      gcongr with d hdmem
      have hdIcc := (Finset.mem_filter.mp hdmem).1
      have hd : 1 ≤ d := (Finset.mem_Icc.mp hdIcc).1
      have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
      simp only [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg, Complex.norm_natCast]
      apply div_le_div_of_nonneg_right _ hdR.le
      calc
        ArithmeticFunction.vonMangoldt d * ‖chi d‖ ≤
            ArithmeticFunction.vonMangoldt d * 1 :=
          mul_le_mul_of_nonneg_left
            (by simpa using chi.norm_le_one (d : ZMod m))
            (ArithmeticFunction.vonMangoldt_nonneg (n := d))
        _ = ArithmeticFunction.vonMangoldt d := mul_one _
    _ ≤ C := hbound N

/-- Quantitative Abel reduction for the ordered endpoint prime-character
series. If the logarithmically weighted prime prefixes are uniformly bounded
by `C`, then every ordered tail of `χ(p) / p` is bounded by
`2 C / log M`. This is the final step after a bounded twisted
von-Mangoldt prefix estimate. -/
lemma dirichlet_L_character_endpoint_firstOrder_tail_norm_le_of_primeLog_prefix_bounded
    {m : ℕ} (chi : DirichletCharacter ℂ m) {C : ℝ}
    (hC : 0 ≤ C)
    (hprefix : ∀ N : ℕ,
      ‖((N + 1).primesBelow.sum fun p =>
        (Real.log (p : ℝ) : ℂ) *
          (chi p * (p : ℂ) ^ (-((1 : ℕ) : ℂ))))‖ ≤ C)
    {M K : ℕ} (hM : 2 ≤ M) (hMK : M ≤ K) :
    ‖(((K + 1).primesBelow \ (M + 1).primesBelow).sum fun p =>
      chi p * (p : ℂ) ^ (-((1 : ℕ) : ℂ)))‖ ≤
      2 * C / Real.log M := by
  by_cases hKM : K = M
  · subst K
    simp only [Finset.sdiff_self, Finset.sum_empty, norm_zero]
    exact div_nonneg (mul_nonneg (by norm_num) hC)
      (Real.log_pos (by exact_mod_cast (lt_of_lt_of_le Nat.one_lt_two hM))).le
  have hMKlt : M < K := lt_of_le_of_ne hMK (Ne.symm hKM)
  let endpoint : ℕ → ℂ := fun i =>
    chi i * (i : ℂ) ^ (-((1 : ℕ) : ℂ))
  let logTerm : ℕ → ℂ := fun i =>
    (Real.log (i : ℝ) : ℂ) * endpoint i
  let a : ℕ → ℂ := fun i => if 0 < i ∧ i.Prime then logTerm i else 0
  let weight : ℕ → ℂ := fun i => ((Real.log (i : ℝ))⁻¹ : ℝ)
  have ha_prefix (N : ℕ) :
      (Finset.range (N + 1)).sum a =
        (N + 1).primesBelow.sum logTerm := by
    simpa [a] using primesBelow_tail_sum_eq_indicator_range_sum logTerm 0 N
  have ha_bound (N : ℕ) : ‖(Finset.range (N + 1)).sum a‖ ≤ C := by
    rw [ha_prefix]
    simpa [logTerm, endpoint] using hprefix N
  have hleft :
      (∑ i ∈ Finset.Ioc M K, weight i • a i) =
        (((K + 1).primesBelow \ (M + 1).primesBelow).sum endpoint) := by
    have hfilter :
        (Finset.Ioc M K).filter Nat.Prime =
          (K + 1).primesBelow \ (M + 1).primesBelow := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_sdiff,
        Nat.mem_primesBelow]
      constructor
      · intro hp
        exact ⟨⟨Nat.lt_succ_iff.mpr hp.1.2, hp.2⟩,
          fun h => (not_lt.mpr (Nat.succ_le_of_lt hp.1.1)) h.1⟩
      · intro hp
        have hMp : M < p := by
          by_contra hnot
          exact hp.2 ⟨Nat.lt_succ_iff.mpr (Nat.le_of_not_gt hnot), hp.1.2⟩
        exact ⟨⟨hMp, Nat.lt_succ_iff.mp hp.1.1⟩, hp.1.2⟩
    calc
      (∑ i ∈ Finset.Ioc M K, weight i • a i) =
          ∑ i ∈ Finset.Ioc M K, if i.Prime then endpoint i else 0 := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        by_cases hiPrime : i.Prime
        · have hiLog : Real.log (i : ℝ) ≠ 0 :=
            (Real.log_pos (by exact_mod_cast hiPrime.one_lt)).ne'
          have hinv :
              ((((Real.log (i : ℝ))⁻¹ : ℝ) : ℂ) *
                ((Real.log (i : ℝ) : ℝ) : ℂ)) = 1 := by
            rw [← Complex.ofReal_mul, inv_mul_cancel₀ hiLog]
            simp
          simp only [weight, a, logTerm, hiPrime, hiPrime.pos, and_self,
            if_true, smul_eq_mul]
          rw [← mul_assoc, hinv, one_mul]
        · simp [a, hiPrime]
      _ = ((Finset.Ioc M K).filter Nat.Prime).sum endpoint := by
        rw [Finset.sum_filter]
      _ = (((K + 1).primesBelow \ (M + 1).primesBelow).sum endpoint) := by
        rw [hfilter]
  have hparts := Finset.sum_Ioc_by_parts weight a hMKlt
  have hidentity :
      (((K + 1).primesBelow \ (M + 1).primesBelow).sum endpoint) =
        weight K • ((Finset.range (K + 1)).sum a) -
          weight (M + 1) • ((Finset.range (M + 1)).sum a) -
          (∑ i ∈ Finset.Ioc M (K - 1),
            (weight (i + 1) - weight i) •
              ((Finset.range (i + 1)).sum a)) := by
    rw [← hleft]
    exact hparts
  have hweight_pos {i : ℕ} (hi : 2 ≤ i) :
      0 < (Real.log (i : ℝ))⁻¹ := by
    exact inv_pos.mpr (Real.log_pos (by exact_mod_cast (lt_of_lt_of_le Nat.one_lt_two hi)))
  have hweight_antitone {i j : ℕ} (hi : 2 ≤ i) (hij : i ≤ j) :
      (Real.log (j : ℝ))⁻¹ ≤ (Real.log (i : ℝ))⁻¹ := by
    apply inv_anti₀ (Real.log_pos (by exact_mod_cast (lt_of_lt_of_le Nat.one_lt_two hi)))
    exact Real.strictMonoOn_log.monotoneOn
      (by
        change (0 : ℝ) < (i : ℝ)
        exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_two hi))
      (by
        change (0 : ℝ) < (j : ℝ)
        exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_two (le_trans hi hij)))
      (by exact_mod_cast hij)
  have hvariation (i : ℕ) (hi : i ∈ Finset.Ioc M (K - 1)) :
      ‖weight (i + 1) - weight i‖ =
        (Real.log (i : ℝ))⁻¹ - (Real.log ((i + 1 : ℕ) : ℝ))⁻¹ := by
    have hi2 : 2 ≤ i := le_trans hM (Finset.mem_Ioc.mp hi).1.le
    have hle := hweight_antitone hi2 (Nat.le_succ i)
    simp only [weight]
    rw [← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs,
      abs_of_nonpos (sub_nonpos.mpr hle)]
    ring
  have hvariation_sum :
      (∑ i ∈ Finset.Ioc M (K - 1), ‖weight (i + 1) - weight i‖) =
        (Real.log ((M + 1 : ℕ) : ℝ))⁻¹ -
          (Real.log (K : ℝ))⁻¹ := by
    rw [Finset.sum_congr rfl hvariation]
    exact sum_Ioc_sub_succ_eq hMKlt
  have hnorm_weight (i : ℕ) (hi : 2 ≤ i) :
    ‖weight i‖ = (Real.log (i : ℝ))⁻¹ := by
    simp only [weight]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hweight_pos hi)]
  rw [hidentity]
  calc
    ‖weight K • ((Finset.range (K + 1)).sum a) -
          weight (M + 1) • ((Finset.range (M + 1)).sum a) -
          (∑ i ∈ Finset.Ioc M (K - 1),
            (weight (i + 1) - weight i) •
              ((Finset.range (i + 1)).sum a))‖
        ≤ ‖weight K‖ * C + ‖weight (M + 1)‖ * C +
            (∑ i ∈ Finset.Ioc M (K - 1),
              ‖weight (i + 1) - weight i‖ * C) := by
          calc
            _ ≤ ‖weight K • ((Finset.range (K + 1)).sum a)‖ +
                ‖weight (M + 1) • ((Finset.range (M + 1)).sum a)‖ +
                ‖∑ i ∈ Finset.Ioc M (K - 1),
                  (weight (i + 1) - weight i) •
                    ((Finset.range (i + 1)).sum a)‖ := by
                  calc
                    _ ≤ ‖weight K • ((Finset.range (K + 1)).sum a) -
                          weight (M + 1) • ((Finset.range (M + 1)).sum a)‖ +
                        ‖∑ i ∈ Finset.Ioc M (K - 1),
                          (weight (i + 1) - weight i) •
                            ((Finset.range (i + 1)).sum a)‖ := norm_sub_le _ _
                    _ ≤ _ := by
                      gcongr
                      exact norm_sub_le _ _
            _ ≤ _ := by
              gcongr
              · simpa using mul_le_mul_of_nonneg_left (ha_bound K) (norm_nonneg (weight K))
              · simpa using mul_le_mul_of_nonneg_left (ha_bound M) (norm_nonneg (weight (M + 1)))
              · refine le_trans (norm_sum_le _ _) ?_
                gcongr with i hi
                simpa using mul_le_mul_of_nonneg_left (ha_bound i)
                  (norm_nonneg (weight (i + 1) - weight i))
    _ = 2 * C * (Real.log ((M + 1 : ℕ) : ℝ))⁻¹ := by
      rw [hnorm_weight K (le_trans hM hMK), hnorm_weight (M + 1) (by omega),
        ← Finset.sum_mul, hvariation_sum]
      ring
    _ ≤ 2 * C * (Real.log (M : ℝ))⁻¹ := by
      exact mul_le_mul_of_nonneg_left (hweight_antitone hM (Nat.le_succ M))
        (mul_nonneg (by norm_num) hC)
    _ = 2 * C / Real.log M := by rw [div_eq_mul_inv]

/-- Ordered logarithmically weighted prime-character prefixes are uniformly
bounded. This completes the reduction: bounded twisted
von-Mangoldt prefixes are split into prime and higher-prime-power parts, and
the latter is controlled by finite Abel summation and ordinary Chebyshev
bounds. -/
theorem dirichlet_L_nontrivial_character_endpoint_primeLog_prefix_bounded
    {m : ℕ} [NeZero m] (χ : DirichletCharacter ℂ m) (hχ : χ ≠ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ,
      ‖((N + 1).primesBelow.sum fun p =>
        (Real.log (p : ℝ) : ℂ) *
          (χ p * (p : ℂ) ^ (-((1 : ℕ) : ℂ))))‖ ≤ C := by
  rcases dirichlet_L_nontrivial_character_vonMangoldtWeighted_naturalPrefix_bounded
      χ hχ with ⟨CT, hCT, hTbound⟩
  rcases dirichlet_L_character_higherPrimePower_vonMangoldtPrefix_bounded χ with
    ⟨CH, hCH, hHbound⟩
  refine ⟨CT + CH, add_nonneg hCT hCH, ?_⟩
  intro N
  let T : ℂ := ∑ d ∈ Finset.Icc 1 N,
    (ArithmeticFunction.vonMangoldt d : ℂ) * χ d / (d : ℂ)
  let P : ℂ := (N + 1).primesBelow.sum fun p =>
    (Real.log (p : ℝ) : ℂ) * χ p / (p : ℂ)
  let H : ℂ := ∑ d ∈ (Finset.Icc 1 N).filter (fun d => ¬d.Prime),
    (ArithmeticFunction.vonMangoldt d : ℂ) * χ d / (d : ℂ)
  have hsplit : T = P + H := by
    simpa [T, P, H] using
      dirichlet_L_character_vonMangoldtWeighted_prefix_eq_prime_add_higherPrimePower
        χ N
  have hP : ‖P‖ ≤ CT + CH := by
    rw [show P = T - H by rw [hsplit]; ring]
    exact (norm_sub_le T H).trans (add_le_add (hTbound N) (hHbound N))
  have hsource :
      ((N + 1).primesBelow.sum fun p =>
        (Real.log (p : ℝ) : ℂ) *
          (χ p * (p : ℂ) ^ (-((1 : ℕ) : ℂ)))) = P := by
    dsimp [P]
    refine Finset.sum_congr rfl ?_
    intro p hp
    rw [show (-((1 : ℕ) : ℂ)) = -(1 : ℂ) by norm_num,
      Complex.cpow_neg_one]
    ring
  rw [hsource]
  exact hP

/-- Ordinary Cauchy estimate for the endpoint first-order prime-character
term, derived by Abel summation from bounded logarithmically weighted ordered
prime prefixes. -/
theorem dirichlet_L_nontrivial_character_endpoint_firstOrder_prefix_unscaled_cauchy
    {m : ℕ} [NeZero m] (χ : DirichletCharacter ℂ m) (hχ : χ ≠ 1)
    (_hquad : χ ^ 2 = 1) :
    ∀ ε : ℝ, ε > 0 → ∃ M₀ : ℕ,
      ∀ M : ℕ, M ≥ M₀ →
        ∀ K : ℕ, K ≥ M →
        dist
          (((K + 1).primesBelow.sum fun p =>
              χ p * (p : ℂ) ^ (-((1 : ℕ) : ℂ))) -
            ((M + 1).primesBelow.sum fun p =>
              χ p * (p : ℂ) ^ (-((1 : ℕ) : ℂ))))
          0 < ε := by
  rcases dirichlet_L_nontrivial_character_endpoint_primeLog_prefix_bounded
      χ hχ with ⟨C, hC, hprefix⟩
  have hlog_atTop :
      Filter.Tendsto (fun M : ℕ => Real.log (M : ℝ))
        Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hbound_tendsto :
      Filter.Tendsto (fun M : ℕ => 2 * C / Real.log (M : ℝ))
        Filter.atTop (nhds 0) := by
    simpa [div_eq_mul_inv] using
      (Filter.Tendsto.inv_tendsto_atTop hlog_atTop).const_mul (2 * C)
  intro ε hε
  have hsmall : ∀ᶠ M : ℕ in Filter.atTop,
      2 * C / Real.log (M : ℝ) < ε :=
    (tendsto_order.1 hbound_tendsto).2 ε hε
  rcases (Filter.eventually_atTop.1 hsmall) with ⟨M₀, hM₀⟩
  refine ⟨max 2 M₀, ?_⟩
  intro M hM K hK
  have hMtwo : 2 ≤ M := le_trans (le_max_left _ _) hM
  have hM₀le : M₀ ≤ M := le_trans (le_max_right _ _) hM
  rw [← dirichlet_L_character_endpoint_firstOrder_tail_eq_prefix_sub χ hK]
  rw [dist_eq_norm, sub_zero]
  exact lt_of_le_of_lt
    (dirichlet_L_character_endpoint_firstOrder_tail_norm_le_of_primeLog_prefix_bounded
      χ hC hprefix hMtwo hK)
    (hM₀ M hM₀le)

/-- The finite endpoint prime-square prefix is bounded by the full natural
`n^{-2}` tail over positive naturals. -/
lemma dirichlet_L_character_endpoint_prime_inv_sq_prefix_le_nat_tsum
    (M : ℕ) :
    ((M + 1).primesBelow.sum fun p => (p : ℝ) ^ (-2 : ℝ)) ≤
      ∑' n : {n : ℕ // n ∉ Finset.range 1}, (n.1 : ℝ) ^ (-2 : ℝ) := by
  let S : Finset ℕ := (M + 1).primesBelow
  let e : {p : ℕ // p ∈ S} ↪ {n : ℕ // n ∉ Finset.range 1} :=
    ⟨fun p => ⟨p.1, by
        have hpPrime : p.1.Prime := Nat.prime_of_mem_primesBelow p.2
        intro hmem
        rw [Finset.mem_range] at hmem
        exact hpPrime.ne_zero (Nat.le_zero.mp (Nat.lt_succ_iff.mp hmem))⟩,
      by
        intro a b hab
        exact Subtype.ext
          (congrArg (fun q : {n : ℕ // n ∉ Finset.range 1} => q.1) hab)⟩
  let Sc : Finset {n : ℕ // n ∉ Finset.range 1} := S.attach.map e
  have hsum_eq :
      Sc.sum (fun n => (n.1 : ℝ) ^ (-2 : ℝ)) =
        S.sum (fun p => (p : ℝ) ^ (-2 : ℝ)) := by
    change (S.attach.map e).sum (fun n => (n.1 : ℝ) ^ (-2 : ℝ)) =
      S.sum (fun p => (p : ℝ) ^ (-2 : ℝ))
    rw [Finset.sum_map]
    exact Finset.sum_attach S (fun p => (p : ℝ) ^ (-2 : ℝ))
  have hsummable : Summable (fun n : {n : ℕ // n ∉ Finset.range 1} =>
      (n.1 : ℝ) ^ (-2 : ℝ)) := by
    exact (Real.summable_nat_rpow.mpr (by norm_num : (-2 : ℝ) < -1)).subtype _
  have hle : Sc.sum (fun n => (n.1 : ℝ) ^ (-2 : ℝ)) ≤
      ∑' n : {n : ℕ // n ∉ Finset.range 1}, (n.1 : ℝ) ^ (-2 : ℝ) := by
    exact Summable.sum_le_tsum Sc
      (fun n _hn => Real.rpow_nonneg (Nat.cast_nonneg n.1) _) hsummable
  rw [← hsum_eq]
  exact hle

/-- Ordinary endpoint prefix Cauchy control implies eventual boundedness of the
endpoint first-order prime-character prefixes. -/
lemma dirichlet_L_nontrivial_character_endpoint_firstOrder_prefix_eventually_bounded
    {m : ℕ} [NeZero m] (χ : DirichletCharacter ℂ m) (hχ : χ ≠ 1)
    (hquad : χ ^ 2 = 1) :
    ∃ B : ℝ, 0 < B ∧
      ∀ᶠ M : ℕ in Filter.atTop,
        ‖((M + 1).primesBelow.sum fun p =>
          χ p * (p : ℂ) ^ (-((1 : ℕ) : ℂ)))‖ ≤ B := by
  rcases
      dirichlet_L_nontrivial_character_endpoint_firstOrder_prefix_unscaled_cauchy
        χ hχ hquad 1 zero_lt_one with
    ⟨M₀, hM₀⟩
  let A₀ : ℂ :=
    (M₀ + 1).primesBelow.sum fun p =>
      χ p * (p : ℂ) ^ (-((1 : ℕ) : ℂ))
  refine ⟨‖A₀‖ + 1, by positivity, ?_⟩
  rw [Filter.eventually_atTop]
  refine ⟨M₀, ?_⟩
  intro M hM
  let A : ℂ :=
    (M + 1).primesBelow.sum fun p =>
      χ p * (p : ℂ) ^ (-((1 : ℕ) : ℂ))
  have hdist : dist (A - A₀) 0 < 1 := by
    simpa [A, A₀] using hM₀ M₀ le_rfl M hM
  have hdiff : ‖A - A₀‖ < 1 := by
    simpa [dist_eq_norm] using hdist
  calc
    ‖A‖ = ‖(A - A₀) + A₀‖ := by ring_nf
    _ ≤ ‖A - A₀‖ + ‖A₀‖ := norm_add_le _ _
    _ ≤ ‖A₀‖ + 1 := by linarith

/-- The endpoint logarithmic Euler prefix is eventually bounded once the
first-order endpoint prefixes are Cauchy; the quadratic logarithmic remainder
is bounded by the summable prime-square majorant. -/
lemma dirichlet_L_nontrivial_character_endpoint_eulerLog_prefix_eventually_bounded
    {m : ℕ} [NeZero m] (χ : DirichletCharacter ℂ m) (hχ : χ ≠ 1)
    (hquad : χ ^ 2 = 1) :
    ∃ B : ℝ, 0 < B ∧
      ∀ᶠ M : ℕ in Filter.atTop,
        ‖((M + 1).primesBelow.sum fun p =>
          -Complex.log (1 - χ p * (p : ℂ) ^ (-((1 : ℕ) : ℂ))))‖ ≤ B := by
  rcases
      dirichlet_L_nontrivial_character_endpoint_firstOrder_prefix_eventually_bounded
        χ hχ hquad with
    ⟨B₁, hB₁pos, hB₁⟩
  let B₂ : ℝ := ∑' n : {n : ℕ // n ∉ Finset.range 1}, (n.1 : ℝ) ^ (-2 : ℝ)
  have hB₂nonneg : 0 ≤ B₂ := by
    exact tsum_nonneg fun n => Real.rpow_nonneg (Nat.cast_nonneg n.1) _
  refine ⟨B₁ + B₂, by positivity, ?_⟩
  filter_upwards [hB₁] with M hM
  let S : Finset ℕ := (M + 1).primesBelow
  let A : ℂ := S.sum fun p => χ p * (p : ℂ) ^ (-((1 : ℕ) : ℂ))
  let R : ℂ := S.sum fun p =>
    -Complex.log (1 - χ p * (p : ℂ) ^ (-((1 : ℕ) : ℂ))) -
      χ p * (p : ℂ) ^ (-((1 : ℕ) : ℂ))
  have hsum :
      (S.sum fun p =>
          -Complex.log (1 - χ p * (p : ℂ) ^ (-((1 : ℕ) : ℂ)))) =
        A + R := by
    dsimp [A, R]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro p hp
    ring
  have hR :
      ‖R‖ ≤ B₂ := by
    calc
      ‖R‖ ≤ S.sum (fun p => (p : ℝ) ^ (-2 : ℝ)) := by
        calc
          ‖R‖ ≤ S.sum (fun p => ‖-Complex.log
              (1 - χ p * (p : ℂ) ^ (-((1 : ℕ) : ℂ))) -
                χ p * (p : ℂ) ^ (-((1 : ℕ) : ℂ))‖) := by
            dsimp [R]
            exact norm_sum_le S _
          _ ≤ S.sum (fun p => (p : ℝ) ^ (-2 : ℝ)) := by
            refine Finset.sum_le_sum ?_
            intro p hp
            have hpPrime : p.Prime := Nat.prime_of_mem_primesBelow hp
            simpa using
              dirichlet_L_character_endpointRegion_eulerLog_sub_linear_norm_le_inv_sq
                χ le_rfl p hpPrime
      _ ≤ B₂ := by
        simpa [S, B₂] using
          dirichlet_L_character_endpoint_prime_inv_sq_prefix_le_nat_tsum M
  calc
    ‖S.sum fun p =>
        -Complex.log (1 - χ p * (p : ℂ) ^ (-((1 : ℕ) : ℂ)))‖ =
        ‖A + R‖ := by rw [hsum]
    _ ≤ ‖A‖ + ‖R‖ := norm_add_le _ _
    _ ≤ B₁ + B₂ := by
      have hA : ‖A‖ ≤ B₁ := by simpa [S, A] using hM
      exact add_le_add hA hR

/-- Endpoint Euler-prefix boundedness for a nontrivial Dirichlet character,
derived from ordinary Cauchy convergence of `∑ χ(p)/p` plus the already formal
quadratic logarithmic-remainder estimate. -/
theorem dirichlet_L_nontrivial_character_endpoint_eulerPrefix_norm_bounded
    {m : ℕ} [NeZero m] (χ : DirichletCharacter ℂ m) (hχ : χ ≠ 1)
    (hquad : χ ^ 2 = 1) :
    ∃ B : ℝ, 0 < B ∧
      ∀ᶠ M : ℕ in Filter.atTop,
        (‖((M + 1).primesBelow.prod fun p =>
          (1 - χ p * (p : ℂ) ^ (-((1 : ℕ) : ℂ)))⁻¹)‖ + 1) ≤ B := by
  rcases
      dirichlet_L_nontrivial_character_endpoint_eulerLog_prefix_eventually_bounded
        χ hχ hquad with
    ⟨C, hCpos, hC⟩
  refine ⟨Real.exp C + 1, by positivity, ?_⟩
  filter_upwards [hC] with M hM
  let S : Finset ℕ := (M + 1).primesBelow
  let Z : ℂ := S.sum fun p =>
    -Complex.log (1 - χ p * (p : ℂ) ^ (-((1 : ℕ) : ℂ)))
  have hExp :
      S.prod (fun p => (1 - χ p * (p : ℂ) ^ (-((1 : ℕ) : ℂ)))⁻¹) =
        Complex.exp Z := by
    dsimp [Z]
    rw [Complex.exp_sum]
    refine Finset.prod_congr rfl ?_
    intro p hp
    have hpPrime : p.Prime := Nat.prime_of_mem_primesBelow hp
    have hden :
        1 - χ p * (p : ℂ) ^ (-((1 : ℕ) : ℂ)) ≠ 0 :=
      by
        simpa only [Nat.cast_one] using
          dirichlet_L_character_endpointRegion_eulerDenominator_ne_zero
            χ le_rfl p hpPrime
    change (1 - χ p * (p : ℂ) ^ (-((1 : ℕ) : ℂ)))⁻¹ =
      Complex.exp (-Complex.log
        (1 - χ p * (p : ℂ) ^ (-((1 : ℕ) : ℂ))))
    rw [Complex.exp_neg, Complex.exp_log hden]
  have hnorm_exp : ‖Complex.exp Z‖ ≤ Real.exp C := by
    calc
      ‖Complex.exp Z‖ ≤ Real.exp ‖Z‖ := Complex.norm_exp_le_exp_norm Z
      _ ≤ Real.exp C := Real.exp_le_exp.mpr (by simpa [S, Z] using hM)
  calc
    ‖S.prod fun p => (1 - χ p * (p : ℂ) ^ (-((1 : ℕ) : ℂ)))⁻¹‖ + 1 =
        ‖Complex.exp Z‖ + 1 := by rw [hExp]
    _ ≤ Real.exp C + 1 := by simpa [add_comm] using add_le_add_right hnorm_exp 1

/-- Scaled prefix-difference estimate for the endpoint first-order
prime-character term, derived from ordinary Cauchy convergence of
`∑ χ(p)/p` and boundedness of the endpoint Euler prefixes. -/
theorem dirichlet_L_nontrivial_character_endpoint_firstOrder_prefix_scaled_cauchy
    {m : ℕ} [NeZero m] (χ : DirichletCharacter ℂ m) (hχ : χ ≠ 1)
    (hquad : χ ^ 2 = 1) :
    ∀ ε : ℝ, ε > 0 → ∃ M₀ : ℕ,
      ∀ M : ℕ, M ≥ M₀ →
        ∀ K : ℕ, K ≥ M →
        (‖((M + 1).primesBelow.prod fun p =>
          (1 - χ p * (p : ℂ) ^ (-((1 : ℕ) : ℂ)))⁻¹)‖ + 1) *
          dist
            (((K + 1).primesBelow.sum fun p =>
                χ p * (p : ℂ) ^ (-((1 : ℕ) : ℂ))) -
              ((M + 1).primesBelow.sum fun p =>
                χ p * (p : ℂ) ^ (-((1 : ℕ) : ℂ))))
            0 < ε := by
  intro ε hε
  rcases
      dirichlet_L_nontrivial_character_endpoint_eulerPrefix_norm_bounded
        χ hχ hquad with
    ⟨B, hBpos, hB_eventual⟩
  let δ : ℝ := ε / B
  have hδpos : 0 < δ := by
    dsimp [δ]
    positivity
  rcases
      dirichlet_L_nontrivial_character_endpoint_firstOrder_prefix_unscaled_cauchy
        χ hχ hquad δ hδpos with
    ⟨M₁, hM₁⟩
  rw [Filter.eventually_atTop] at hB_eventual
  rcases hB_eventual with ⟨M₂, hM₂⟩
  refine ⟨max M₁ M₂, ?_⟩
  intro M hM K hK
  let C : ℝ :=
    ‖((M + 1).primesBelow.prod fun p =>
      (1 - χ p * (p : ℂ) ^ (-((1 : ℕ) : ℂ)))⁻¹)‖ + 1
  let D : ℝ :=
    dist
      (((K + 1).primesBelow.sum fun p =>
          χ p * (p : ℂ) ^ (-((1 : ℕ) : ℂ))) -
        ((M + 1).primesBelow.sum fun p =>
          χ p * (p : ℂ) ^ (-((1 : ℕ) : ℂ))))
      0
  have hM₁le : M ≥ M₁ := le_trans (le_max_left _ _) hM
  have hM₂le : M ≥ M₂ := le_trans (le_max_right _ _) hM
  have hC_le : C ≤ B := by
    simpa [C] using hM₂ M hM₂le
  have hD_lt : D < δ := by
    simpa [D] using hM₁ M hM₁le K hK
  have hD_nonneg : 0 ≤ D := dist_nonneg
  have hmul_le : C * D ≤ B * D := by
    exact mul_le_mul_of_nonneg_right hC_le hD_nonneg
  have hBD_lt : B * D < ε := by
    have hmul := mul_lt_mul_of_pos_left hD_lt hBpos
    have hcancel : B * δ = ε := by
      dsimp [δ]
      rw [mul_div_cancel₀ ε (ne_of_gt hBpos)]
    simpa [hcancel] using hmul
  exact lt_of_le_of_lt hmul_le hBD_lt

/-- Prefix-difference Cauchy estimate for the endpoint first-order
prime-character term, derived from the cleaner scaled source above.  Finite
tail subtraction is handled formally below. -/
theorem dirichlet_L_nontrivial_character_endpoint_firstOrder_prefix_cauchy
    {m : ℕ} [NeZero m] (χ : DirichletCharacter ℂ m) (hχ : χ ≠ 1)
    (hquad : χ ^ 2 = 1) :
    ∀ ε : ℝ, ε > 0 → ∃ M₀ : ℕ,
      ∀ M : ℕ, M ≥ M₀ →
        ∀ K : ℕ, K ≥ M →
        dist
          (((K + 1).primesBelow.sum fun p =>
              χ p * (p : ℂ) ^ (-((1 : ℕ) : ℂ))) -
            ((M + 1).primesBelow.sum fun p =>
              χ p * (p : ℂ) ^ (-((1 : ℕ) : ℂ))))
          0 <
          (min 1
            ((ε /
              (‖((M + 1).primesBelow.prod fun p =>
                (1 - χ p * (p : ℂ) ^ (-((1 : ℕ) : ℂ)))⁻¹)‖ + 1)) / 2)) / 4
    := by
  intro ε hε
  let δ : ℝ := min 1 ε / 8
  have hδpos : 0 < δ := by
    dsimp [δ]
    positivity
  rcases
      dirichlet_L_nontrivial_character_endpoint_firstOrder_prefix_scaled_cauchy
        χ hχ hquad δ hδpos with
    ⟨M₀, hM₀⟩
  refine ⟨M₀, ?_⟩
  intro M hM K hK
  let C : ℝ :=
    ‖((M + 1).primesBelow.prod fun p =>
      (1 - χ p * (p : ℂ) ^ (-((1 : ℕ) : ℂ)))⁻¹)‖ + 1
  let D : ℝ :=
    dist
      (((K + 1).primesBelow.sum fun p =>
          χ p * (p : ℂ) ^ (-((1 : ℕ) : ℂ))) -
        ((M + 1).primesBelow.sum fun p =>
          χ p * (p : ℂ) ^ (-((1 : ℕ) : ℂ))))
      0
  have hCpos : 0 < C := by
    dsimp [C]
    positivity
  have hCge : 1 ≤ C := by
    dsimp [C]
    linarith [norm_nonneg
      ((M + 1).primesBelow.prod fun p =>
        (1 - χ p * (p : ℂ) ^ (-((1 : ℕ) : ℂ)))⁻¹)]
  have hscaled : C * D < δ := by
    simpa [C, D] using hM₀ M hM K hK
  have hD : D < δ / C := by
    exact (lt_div_iff₀ hCpos).mpr (by simpa [mul_comm] using hscaled)
  have hδnonneg : 0 ≤ δ := le_of_lt hδpos
  have hδ_le_one_eighth : δ ≤ (1 : ℝ) / 8 := by
    dsimp [δ]
    exact div_le_div_of_nonneg_right (min_le_left (1 : ℝ) ε) (by norm_num)
  have hδ_le_eps_eighth : δ ≤ ε / 8 := by
    dsimp [δ]
    exact div_le_div_of_nonneg_right (min_le_right (1 : ℝ) ε) (by norm_num)
  have hfour_left : 4 * (δ / C) ≤ 1 := by
    have hdiv₁ : δ / C ≤ ((1 : ℝ) / 8) / C := by
      exact div_le_div_of_nonneg_right hδ_le_one_eighth (le_of_lt hCpos)
    have hdiv₂ : ((1 : ℝ) / 8) / C ≤ (1 : ℝ) / 8 := by
      have hinv : C⁻¹ ≤ (1 : ℝ) := inv_le_one_of_one_le₀ hCge
      calc
        ((1 : ℝ) / 8) / C = ((1 : ℝ) / 8) * C⁻¹ := by ring
        _ ≤ ((1 : ℝ) / 8) * 1 := by
          exact mul_le_mul_of_nonneg_left hinv (by norm_num)
        _ = (1 : ℝ) / 8 := by ring
    nlinarith [le_trans hdiv₁ hdiv₂]
  have hfour_right : 4 * (δ / C) ≤ (ε / C) / 2 := by
    have hdiv : δ / C ≤ (ε / 8) / C := by
      exact div_le_div_of_nonneg_right hδ_le_eps_eighth (le_of_lt hCpos)
    calc
      4 * (δ / C) ≤ 4 * ((ε / 8) / C) := by
        exact mul_le_mul_of_nonneg_left hdiv (by norm_num)
      _ = (ε / C) / 2 := by ring
  have hle_target :
      δ / C ≤ (min 1 ((ε / C) / 2)) / 4 := by
    calc
      δ / C = (4 * (δ / C)) / 4 := by ring
      _ ≤ (min 1 ((ε / C) / 2)) / 4 := by
        exact div_le_div_of_nonneg_right
          (le_min hfour_left hfour_right) (by norm_num)
  exact lt_of_lt_of_le hD (by simpa [C] using hle_target)

/-- Endpoint Cauchy-tail theorem for the first-order prime-character term in
the endpoint Abel passage, derived from the prefix Cauchy estimate and
the finite cutoff-tail identity. -/
theorem dirichlet_L_nontrivial_character_endpoint_firstOrder_tail
    {m : ℕ} [NeZero m] (χ : DirichletCharacter ℂ m) (hχ : χ ≠ 1)
    (hquad : χ ^ 2 = 1) :
    ∀ ε : ℝ, ε > 0 → ∃ M₀ : ℕ,
      ∀ M : ℕ, M ≥ M₀ →
        ∀ K : ℕ, K ≥ M →
        dist
          (((K + 1).primesBelow \ (M + 1).primesBelow).sum fun p =>
            χ p * (p : ℂ) ^ (-((1 : ℕ) : ℂ)))
          0 <
          (min 1
            ((ε /
              (‖((M + 1).primesBelow.prod fun p =>
                (1 - χ p * (p : ℂ) ^ (-((1 : ℕ) : ℂ)))⁻¹)‖ + 1)) / 2)) / 4 := by
  intro ε hε
  rcases
      dirichlet_L_nontrivial_character_endpoint_firstOrder_prefix_cauchy
        χ hχ hquad ε hε with
    ⟨M₀, hM₀⟩
  refine ⟨M₀, ?_⟩
  intro M hM K hK
  rw [dirichlet_L_character_endpoint_firstOrder_tail_eq_prefix_sub χ hK]
  exact hM₀ M hM K hK

/-- Abel-continuity theorem for the first-order prime-character term, in its
narrowed form: once the endpoint prefix differences satisfy the scaled Cauchy
estimate, the finite Abel estimate gives the corresponding locally uniform
half-plane variation estimate. -/
theorem dirichlet_L_character_endpoint_halfplane_firstOrder_variation_prefix_of_prefix_cauchy
    {m : ℕ} (χ : DirichletCharacter ℂ m) :
    (∀ ε : ℝ, ε > 0 → ∃ M₀ : ℕ,
      ∀ M : ℕ, M ≥ M₀ →
        ∀ K : ℕ, K ≥ M →
        dist
          (((K + 1).primesBelow.sum fun p =>
              χ p * (p : ℂ) ^ (-((1 : ℕ) : ℂ))) -
            ((M + 1).primesBelow.sum fun p =>
              χ p * (p : ℂ) ^ (-((1 : ℕ) : ℂ))))
          0 <
          (min 1
            ((ε /
              (‖((M + 1).primesBelow.prod fun p =>
                (1 - χ p * (p : ℂ) ^ (-((1 : ℕ) : ℂ)))⁻¹)‖ + 1)) / 2)) / 4) →
    ∀ ε : ℝ, ε > 0 → ∃ M₀ : ℕ,
      ∀ M : ℕ, M ≥ M₀ →
        ∀ᶠ (x : ℝ) in nhdsWithin (1 : ℝ) (Set.Ioi (1 : ℝ)),
        ∀ K : ℕ, K ≥ M →
        dist
          ((((K + 1).primesBelow.sum fun p =>
              χ p * (p : ℂ) ^ (-(x : ℂ))) -
            ((M + 1).primesBelow.sum fun p =>
              χ p * (p : ℂ) ^ (-(x : ℂ)))) -
            (((K + 1).primesBelow.sum fun p =>
              χ p * (p : ℂ) ^ (-((1 : ℕ) : ℂ))) -
            ((M + 1).primesBelow.sum fun p =>
              χ p * (p : ℂ) ^ (-((1 : ℕ) : ℂ)))))
          0 <
          (min 1
            ((ε /
              (‖((M + 1).primesBelow.prod fun p =>
                (1 - χ p * (p : ℂ) ^ (-((1 : ℕ) : ℂ)))⁻¹)‖ + 1)) / 2)) / 4
    := by
  intro hPrefix ε hε
  let η : ℝ := min ε 1 / 16
  have hη_pos : 0 < η := by
    dsimp [η]
    positivity
  rcases hPrefix η hη_pos with ⟨M₀, hM₀⟩
  refine ⟨M₀, ?_⟩
  intro M hM
  filter_upwards [self_mem_nhdsWithin] with x hx
  intro K hK
  let P : ℝ :=
    ‖((M + 1).primesBelow.prod fun p =>
      (1 - χ p * (p : ℂ) ^ (-((1 : ℕ) : ℂ)))⁻¹)‖ + 1
  let δ : ℝ := (min 1 ((ε / P) / 2)) / 4
  let δ' : ℝ := (min 1 ((η / P) / 2)) / 4
  have hPpos : 0 < P := by
    have hnorm_nonneg :
        0 ≤ ‖((M + 1).primesBelow.prod fun p =>
          (1 - χ p * (p : ℂ) ^ (-((1 : ℕ) : ℂ)))⁻¹)‖ := norm_nonneg _
    dsimp [P]
    linarith
  have hPge : 1 ≤ P := by
    have hnorm_nonneg :
        0 ≤ ‖((M + 1).primesBelow.prod fun p =>
          (1 - χ p * (p : ℂ) ^ (-((1 : ℕ) : ℂ)))⁻¹)‖ := norm_nonneg _
    dsimp [P]
    linarith
  have hη_nonneg : 0 ≤ η := le_of_lt hη_pos
  have hη_le_eps_sixteen : η ≤ ε / 16 := by
    dsimp [η]
    exact div_le_div_of_nonneg_right (min_le_left ε 1) (by norm_num)
  have hη_le_one_sixteen : η ≤ 1 / 16 := by
    dsimp [η]
    exact div_le_div_of_nonneg_right (min_le_right ε 1) (by norm_num)
  have hη_divP_le : η / P ≤ η := by
    rw [div_le_iff₀ hPpos]
    nlinarith
  have hη_arg_le_one : (η / P) / 2 ≤ 1 := by
    nlinarith
  have hδ'_eq : δ' = (η / P) / 8 := by
    dsimp [δ']
    rw [min_eq_right hη_arg_le_one]
    ring
  have hδ'_nonneg : 0 ≤ δ' := by
    have hnonneg : 0 ≤ min 1 ((η / P) / 2) := by
      exact le_min (by norm_num) (by positivity)
    exact div_nonneg hnonneg (by norm_num)
  have hsmall : 2 * δ' < δ := by
    by_cases hmain : (ε / P) / 2 ≤ 1
    · have hη_lt_half_eps : 2 * η < ε := by
        nlinarith [hη_le_eps_sixteen, hε]
      dsimp [δ]
      rw [min_eq_right hmain, hδ'_eq]
      field_simp [hPpos.ne']
      nlinarith
    · have hmain_ge : 1 ≤ (ε / P) / 2 := le_of_not_ge hmain
      dsimp [δ]
      rw [min_eq_left hmain_ge, hδ'_eq]
      nlinarith [hη_divP_le, hη_le_one_sixteen]
  have hδ_pos : 0 < δ := by
    have harg_pos : 0 < (ε / P) / 2 := by positivity
    have hmin_pos : 0 < min 1 ((ε / P) / 2) := lt_min (by norm_num) harg_pos
    exact div_pos hmin_pos (by norm_num)
  by_cases hKM : K = M
  · subst K
    have hzero :
        ((((M + 1).primesBelow.sum fun p =>
            χ p * (p : ℂ) ^ (-(x : ℂ))) -
          ((M + 1).primesBelow.sum fun p =>
            χ p * (p : ℂ) ^ (-(x : ℂ)))) -
          (((M + 1).primesBelow.sum fun p =>
            χ p * (p : ℂ) ^ (-((1 : ℕ) : ℂ))) -
          ((M + 1).primesBelow.sum fun p =>
            χ p * (p : ℂ) ^ (-((1 : ℕ) : ℂ))))) = 0 := by
      abel
    rw [hzero, dist_self]
    exact hδ_pos
  · have hMKlt : M < K := lt_of_le_of_ne hK (fun h => hKM h.symm)
    have hTail :
        ∀ J : ℕ, M ≤ J → J ≤ K →
          ‖(Finset.range (J + 1)).sum fun i =>
            if M < i ∧ i.Prime then χ i * (i : ℂ) ^ (-((1 : ℕ) : ℂ)) else 0‖
            ≤ δ' := by
      intro J hMJ hJK
      have hPrefixJ := hM₀ M hM J hMJ
      rw [primesBelow_tail_sum_eq_indicator_range_sum
        (fun p => χ p * (p : ℂ) ^ (-((1 : ℕ) : ℂ))) M J]
      have htail_le :
          ‖(((J + 1).primesBelow \ (M + 1).primesBelow).sum fun p =>
            χ p * (p : ℂ) ^ (-((1 : ℕ) : ℂ)))‖ ≤ δ' := by
        rw [dirichlet_L_character_endpoint_firstOrder_tail_eq_prefix_sub χ hMJ]
        simpa [dist_eq_norm, δ', P] using le_of_lt hPrefixJ
      exact htail_le
    have hweighted :
        ‖(((K + 1).primesBelow \ (M + 1).primesBelow).sum fun p =>
          (χ p * (p : ℂ) ^ (-((1 : ℕ) : ℂ))) *
            ((p : ℂ) ^ ((1 : ℂ) - (x : ℂ)) - 1))‖ ≤ δ' * 2 :=
      dirichlet_L_character_endpoint_weighted_endpoint_tail_norm_le_two_mul
        χ hMKlt hx hTail
    have hweighted' :
        ‖(((K + 1).primesBelow \ (M + 1).primesBelow).sum fun p =>
          (χ p * (p : ℂ) ^ (-((1 : ℕ) : ℂ))) *
            ((p : ℂ) ^ ((1 : ℂ) - (x : ℂ)) - 1))‖ ≤ 2 * δ' := by
      simpa [mul_comm] using hweighted
    have hvariation_eq :
        ((((K + 1).primesBelow.sum fun p =>
            χ p * (p : ℂ) ^ (-(x : ℂ))) -
          ((M + 1).primesBelow.sum fun p =>
            χ p * (p : ℂ) ^ (-(x : ℂ)))) -
          (((K + 1).primesBelow.sum fun p =>
            χ p * (p : ℂ) ^ (-((1 : ℕ) : ℂ))) -
          ((M + 1).primesBelow.sum fun p =>
            χ p * (p : ℂ) ^ (-((1 : ℕ) : ℂ))))) =
          (((K + 1).primesBelow \ (M + 1).primesBelow).sum fun p =>
            (χ p * (p : ℂ) ^ (-((1 : ℕ) : ℂ))) *
              ((p : ℂ) ^ ((1 : ℂ) - (x : ℂ)) - 1)) :=
      dirichlet_L_character_endpoint_halfplane_firstOrder_variation_prefix_eq_weighted_endpoint_tail
        χ hK x
    rw [hvariation_eq, dist_eq_norm]
    simpa [δ, P] using lt_of_le_of_lt hweighted' hsmall

/-- Prefix-difference Abel-continuity step for the first-order
prime-character term in the endpoint passage.  After the endpoint prefix
difference is subtracted, the half-plane prefix difference is locally
uniformly close to it as `x -> 1+`; finite tail subtraction is handled
formally below.  This theorem is derived from the general Abel-continuity
source and the endpoint prefix Cauchy source. -/
theorem dirichlet_L_nontrivial_character_endpoint_halfplane_firstOrder_variation_prefix
    {m : ℕ} [NeZero m] (χ : DirichletCharacter ℂ m) (hχ : χ ≠ 1)
    (hquad : χ ^ 2 = 1) :
    ∀ ε : ℝ, ε > 0 → ∃ M₀ : ℕ,
      ∀ M : ℕ, M ≥ M₀ →
        ∀ᶠ (x : ℝ) in nhdsWithin (1 : ℝ) (Set.Ioi (1 : ℝ)),
        ∀ K : ℕ, K ≥ M →
        dist
          ((((K + 1).primesBelow.sum fun p =>
              χ p * (p : ℂ) ^ (-(x : ℂ))) -
            ((M + 1).primesBelow.sum fun p =>
              χ p * (p : ℂ) ^ (-(x : ℂ)))) -
            (((K + 1).primesBelow.sum fun p =>
              χ p * (p : ℂ) ^ (-((1 : ℕ) : ℂ))) -
            ((M + 1).primesBelow.sum fun p =>
              χ p * (p : ℂ) ^ (-((1 : ℕ) : ℂ)))))
          0 <
          (min 1
            ((ε /
              (‖((M + 1).primesBelow.prod fun p =>
                (1 - χ p * (p : ℂ) ^ (-((1 : ℕ) : ℂ)))⁻¹)‖ + 1)) / 2)) / 4 :=
  dirichlet_L_character_endpoint_halfplane_firstOrder_variation_prefix_of_prefix_cauchy
    χ (dirichlet_L_nontrivial_character_endpoint_firstOrder_prefix_cauchy
      χ hχ hquad)

/-- Abel-continuity step for the first-order prime-character term
in the endpoint passage, derived from the prefix-difference source and the
finite cutoff-tail identity. -/
theorem dirichlet_L_nontrivial_character_endpoint_halfplane_firstOrder_variation_tail
    {m : ℕ} [NeZero m] (χ : DirichletCharacter ℂ m) (hχ : χ ≠ 1)
    (hquad : χ ^ 2 = 1) :
    ∀ ε : ℝ, ε > 0 → ∃ M₀ : ℕ,
      ∀ M : ℕ, M ≥ M₀ →
        ∀ᶠ (x : ℝ) in nhdsWithin (1 : ℝ) (Set.Ioi (1 : ℝ)),
        ∀ K : ℕ, K ≥ M →
        dist
          (((K + 1).primesBelow \ (M + 1).primesBelow).sum fun p =>
            χ p * ((p : ℂ) ^ (-(x : ℂ)) - (p : ℂ) ^ (-((1 : ℕ) : ℂ))))
          0 <
          (min 1
            ((ε /
              (‖((M + 1).primesBelow.prod fun p =>
                (1 - χ p * (p : ℂ) ^ (-((1 : ℕ) : ℂ)))⁻¹)‖ + 1)) / 2)) / 4 := by
  intro ε hε
  rcases
      dirichlet_L_nontrivial_character_endpoint_halfplane_firstOrder_variation_prefix
        χ hχ hquad ε hε with
    ⟨M₀, hM₀⟩
  refine ⟨M₀, ?_⟩
  intro M hM
  filter_upwards [hM₀ M hM] with x hx
  intro K hK
  rw [dirichlet_L_character_endpoint_halfplane_firstOrder_variation_tail_eq_prefix_sub
    χ hK x]
  exact hx K hK

/-- First-order analytic step for the endpoint Abel passage,
formally reduced to an endpoint Cauchy tail and an Abel-continuity variation
tail.  Near `s = 1+`, the finite prime-character tail from cutoff `M` to
cutoff `K` is locally uniformly close to `0`. -/
theorem dirichlet_L_nontrivial_character_endpoint_halfplane_firstOrder_tail
    {m : ℕ} [NeZero m] (χ : DirichletCharacter ℂ m) (hχ : χ ≠ 1)
    (hquad : χ ^ 2 = 1) :
    ∀ ε : ℝ, ε > 0 → ∃ M₀ : ℕ,
      ∀ M : ℕ, M ≥ M₀ →
        ∀ᶠ (x : ℝ) in nhdsWithin (1 : ℝ) (Set.Ioi (1 : ℝ)),
        ∀ K : ℕ, K ≥ M →
        dist
          (((K + 1).primesBelow \ (M + 1).primesBelow).sum fun p =>
            χ p * (p : ℂ) ^ (-(x : ℂ)))
          0 <
          (min 1
            ((ε /
              (‖((M + 1).primesBelow.prod fun p =>
                (1 - χ p * (p : ℂ) ^ (-((1 : ℕ) : ℂ)))⁻¹)‖ + 1)) / 2)) / 2 := by
  intro ε hε
  rcases
      dirichlet_L_nontrivial_character_endpoint_firstOrder_tail
        χ hχ hquad ε hε with
    ⟨M₁, hM₁⟩
  rcases
      dirichlet_L_nontrivial_character_endpoint_halfplane_firstOrder_variation_tail
        χ hχ hquad ε hε with
    ⟨M₂, hM₂⟩
  refine ⟨max M₁ M₂, ?_⟩
  intro M hM
  have hM₁le : M ≥ M₁ := le_trans (le_max_left _ _) hM
  have hM₂le : M ≥ M₂ := le_trans (le_max_right _ _) hM
  filter_upwards [hM₂ M hM₂le] with x hxVariation
  intro K hK
  let S : Finset ℕ := (K + 1).primesBelow \ (M + 1).primesBelow
  let A : ℂ := S.sum fun p => χ p * (p : ℂ) ^ (-((1 : ℕ) : ℂ))
  let B : ℂ := S.sum fun p =>
    χ p * ((p : ℂ) ^ (-(x : ℂ)) - (p : ℂ) ^ (-((1 : ℕ) : ℂ)))
  let δ : ℝ :=
    min 1
      ((ε /
        (‖((M + 1).primesBelow.prod fun p =>
          (1 - χ p * (p : ℂ) ^ (-((1 : ℕ) : ℂ)))⁻¹)‖ + 1)) / 2)
  have hA : dist A 0 < δ / 4 := by
    simpa [S, A, δ] using hM₁ M hM₁le K hK
  have hB : dist B 0 < δ / 4 := by
    simpa [S, B, δ] using hxVariation K hK
  have hsum :
      (S.sum fun p => χ p * (p : ℂ) ^ (-(x : ℂ))) = A + B := by
    dsimp [A, B]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro p hp
    ring
  rw [show
      (((K + 1).primesBelow \ (M + 1).primesBelow).sum fun p =>
        χ p * (p : ℂ) ^ (-(x : ℂ))) = A + B by
      simpa [S] using hsum]
  rw [dist_eq_norm] at hA hB ⊢
  simp only [sub_zero] at hA hB ⊢
  calc
    ‖A + B‖ ≤ ‖A‖ + ‖B‖ := norm_add_le A B
    _ < δ / 4 + δ / 4 := add_lt_add hA hB
    _ = δ / 2 := by ring

/-- The finite prime `p^{-2}` tail is bounded by the full complementary tail of
the summable natural sequence `n^{-2}`.  This removes the finite prime cutoff
bookkeeping from the remaining prefix-scaled quadratic-tail source. -/
theorem dirichlet_L_character_endpoint_prime_inv_sq_tail_le_nat_compl_tsum
    (M K : ℕ) :
    (((K + 1).primesBelow \ (M + 1).primesBelow).sum fun p =>
      (p : ℝ) ^ (-2 : ℝ)) ≤
      ∑' n : {n : ℕ // n ∉ Finset.range (M + 1)}, (n.1 : ℝ) ^ (-2 : ℝ) := by
  let S : Finset ℕ := (K + 1).primesBelow \ (M + 1).primesBelow
  let e : {p : ℕ // p ∈ S} ↪ {n : ℕ // n ∉ Finset.range (M + 1)} :=
    ⟨fun p => ⟨p.1, by
        have hpnot : p.1 ∉ (M + 1).primesBelow := (Finset.mem_sdiff.mp p.2).2
        intro hpr
        have hpPrime : p.1.Prime :=
          Nat.prime_of_mem_primesBelow (Finset.mem_sdiff.mp p.2).1
        exact hpnot
          (Nat.mem_primesBelow.mpr ⟨by simpa [Finset.mem_range] using hpr, hpPrime⟩)⟩,
      by
        intro a b hab
        exact Subtype.ext
          (congrArg (fun q : {n : ℕ // n ∉ Finset.range (M + 1)} => q.1) hab)⟩
  let Sc : Finset {n : ℕ // n ∉ Finset.range (M + 1)} := S.attach.map e
  have hsum_eq :
      Sc.sum (fun n => (n.1 : ℝ) ^ (-2 : ℝ)) =
        S.sum (fun p => (p : ℝ) ^ (-2 : ℝ)) := by
    change (S.attach.map e).sum (fun n => (n.1 : ℝ) ^ (-2 : ℝ)) =
      S.sum (fun p => (p : ℝ) ^ (-2 : ℝ))
    rw [Finset.sum_map]
    exact Finset.sum_attach S (fun p => (p : ℝ) ^ (-2 : ℝ))
  have hsummable : Summable (fun n : {n : ℕ // n ∉ Finset.range (M + 1)} =>
      (n.1 : ℝ) ^ (-2 : ℝ)) := by
    exact (Real.summable_nat_rpow.mpr (by norm_num : (-2 : ℝ) < -1)).subtype _
  have hle : Sc.sum (fun n => (n.1 : ℝ) ^ (-2 : ℝ)) ≤
      ∑' n : {n : ℕ // n ∉ Finset.range (M + 1)}, (n.1 : ℝ) ^ (-2 : ℝ) := by
    exact Summable.sum_le_tsum Sc
      (fun n _hn => Real.rpow_nonneg (Nat.cast_nonneg n.1) _) hsummable
  rw [← hsum_eq]
  exact hle

/-- The canonical complementary natural `n^{-2}` tail used in the endpoint
quadratic-remainder source is bounded by the elementary p-series estimate
`2 / (M + 1)`.  This isolates the remaining scalar source to endpoint
Euler-prefix growth, rather than any further summable-tail bookkeeping. -/
theorem dirichlet_L_character_endpoint_nat_inv_sq_compl_tsum_le (M : ℕ) :
    (∑' n : {n : ℕ // n ∉ Finset.range (M + 1)}, (n.1 : ℝ) ^ (-2 : ℝ)) ≤
      2 / (M + 1 : ℝ) := by
  refine Real.tsum_le_of_sum_le
    (fun n => Real.rpow_nonneg (Nat.cast_nonneg n.1) _) ?_
  intro u
  by_cases hu : u.Nonempty
  · have hNu :
        (u.image (fun n : {n : ℕ // n ∉ Finset.range (M + 1)} => n.1)).Nonempty :=
      by
        rcases hu with ⟨a, hau⟩
        exact ⟨a.1, Finset.mem_image.mpr ⟨a, hau, rfl⟩⟩
    let N : ℕ :=
      (u.image (fun n : {n : ℕ // n ∉ Finset.range (M + 1)} => n.1)).max' hNu
    have hu_subset :
        u.image (fun n : {n : ℕ // n ∉ Finset.range (M + 1)} => n.1) ⊆
          Finset.Ioo M (N + 1) := by
      intro n hn
      rw [Finset.mem_Ioo]
      rcases Finset.mem_image.mp hn with ⟨a, hau, rfl⟩
      constructor
      · have ha_not : a.1 ∉ Finset.range (M + 1) := a.2
        rw [Finset.mem_range] at ha_not
        exact Nat.lt_of_not_ge fun hle => ha_not (Nat.lt_succ_iff.mpr hle)
      · exact Nat.lt_succ_of_le <|
          Finset.le_max'
            (u.image (fun n : {n : ℕ // n ∉ Finset.range (M + 1)} => n.1)) a.1
            (Finset.mem_image.mpr ⟨a, hau, rfl⟩)
    have hsum_image :
        (u.image (fun n : {n : ℕ // n ∉ Finset.range (M + 1)} => n.1)).sum
            (fun n => (n : ℝ) ^ (-2 : ℝ)) =
          u.sum (fun n => (n.1 : ℝ) ^ (-2 : ℝ)) := by
      rw [Finset.sum_image]
      intro a _ b _ hab
      exact Subtype.ext hab
    calc
      u.sum (fun n => (n.1 : ℝ) ^ (-2 : ℝ)) =
          (u.image (fun n : {n : ℕ // n ∉ Finset.range (M + 1)} => n.1)).sum
            (fun n => (n : ℝ) ^ (-2 : ℝ)) := hsum_image.symm
      _ ≤ ∑ n ∈ Finset.Ioo M (N + 1), (n : ℝ) ^ (-2 : ℝ) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg hu_subset ?_
        intro n _hn hn_not
        exact Real.rpow_nonneg (Nat.cast_nonneg n) _
      _ = ∑ n ∈ Finset.Ioo M (N + 1), ((n : ℝ) ^ 2)⁻¹ := by
        refine Finset.sum_congr rfl ?_
        intro n hn
        have hn_pos : (0 : ℝ) < n := by
          have hMn : M < n := (Finset.mem_Ioo.mp hn).1
          exact_mod_cast Nat.zero_lt_of_lt hMn
        rw [Real.rpow_neg hn_pos.le]
        exact congrArg Inv.inv (Real.rpow_natCast (n : ℝ) 2)
      _ ≤ 2 / (M + 1 : ℝ) := by
        simpa using (sum_Ioo_inv_sq_le (α := ℝ) M (N + 1))
  · simp only [Finset.not_nonempty_iff_eq_empty.mp hu, Finset.sum_empty]
    positivity

/-- One Euler factor in the endpoint Dirichlet-character prefix is bounded in
norm by the corresponding principal absolute Euler factor. -/
lemma dirichlet_L_character_endpoint_eulerFactor_norm_le_principal
    {m : ℕ} (χ : DirichletCharacter ℂ m) (p : ℕ) (hp : p.Prime) :
    ‖(1 - χ p * (p : ℂ) ^ (-((1 : ℕ) : ℂ)))⁻¹‖ ≤
      (1 - (p : ℝ) ^ (-1 : ℝ))⁻¹ := by
  let z : ℂ := χ p * (p : ℂ) ^ (-((1 : ℕ) : ℂ))
  let a : ℝ := (p : ℝ)⁻¹
  have ha_rpow : (p : ℝ) ^ (-1 : ℝ) = a := by
    rw [Real.rpow_neg (Nat.cast_nonneg p)]
    simp [a]
  have hpow : ‖(p : ℂ) ^ (-((1 : ℕ) : ℂ))‖ = a := by
    rw [Complex.norm_natCast_cpow_of_pos hp.pos]
    simp only [Complex.neg_re, Nat.cast_one]
    rw [Real.rpow_neg (Nat.cast_nonneg p)]
    simp [a]
  have hz_le : ‖z‖ ≤ a := by
    have hχ : ‖χ p‖ ≤ 1 := χ.norm_le_one p
    calc
      ‖z‖ = ‖χ p‖ * ‖(p : ℂ) ^ (-((1 : ℕ) : ℂ))‖ := by simp [z]
      _ ≤ 1 * ‖(p : ℂ) ^ (-((1 : ℕ) : ℂ))‖ := by
        exact mul_le_mul hχ le_rfl (norm_nonneg _) zero_le_one
      _ = a := by simpa using hpow
  have ha_lt_one : a < 1 := by
    have hp_real : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
    dsimp [a]
    exact inv_lt_one_of_one_lt₀ hp_real
  have hz_lt_one : ‖z‖ < 1 := lt_of_le_of_lt hz_le ha_lt_one
  have hden_lower : 1 - ‖z‖ ≤ ‖1 - z‖ := by
    simpa [sub_eq_add_neg] using norm_sub_norm_le (1 : ℂ) z
  have hden_pos : 0 < 1 - ‖z‖ := sub_pos.mpr hz_lt_one
  have hnorm_pos : 0 < ‖1 - z‖ := lt_of_lt_of_le hden_pos hden_lower
  have hfirst : ‖1 - z‖⁻¹ ≤ (1 - ‖z‖)⁻¹ :=
    (inv_le_inv₀ hnorm_pos hden_pos).mpr hden_lower
  have hsecond : (1 - ‖z‖)⁻¹ ≤ (1 - a)⁻¹ := by
    have ha_pos : 0 < 1 - a := sub_pos.mpr ha_lt_one
    have hle : 1 - a ≤ 1 - ‖z‖ := by linarith
    exact (inv_le_inv₀ hden_pos ha_pos).mpr hle
  calc
    ‖(1 - χ p * (p : ℂ) ^ (-((1 : ℕ) : ℂ)))⁻¹‖ = ‖1 - z‖⁻¹ := by
      simp [z, norm_inv]
    _ ≤ (1 - ‖z‖)⁻¹ := hfirst
    _ ≤ (1 - a)⁻¹ := hsecond
    _ = (1 - (p : ℝ) ^ (-1 : ℝ))⁻¹ := by simp [ha_rpow]

/-- The endpoint Dirichlet-character Euler prefix is bounded by the principal
absolute Euler prefix. -/
lemma dirichlet_L_character_endpoint_prefix_norm_le_principal_abs_prefix
    {m : ℕ} (χ : DirichletCharacter ℂ m) (M : ℕ) :
    ‖((M + 1).primesBelow.prod fun p =>
      (1 - χ p * (p : ℂ) ^ (-((1 : ℕ) : ℂ)))⁻¹)‖ ≤
      ((M + 1).primesBelow.prod fun p =>
        (1 - (p : ℝ) ^ (-1 : ℝ))⁻¹) := by
  let S : Finset ℕ := (M + 1).primesBelow
  let f : ℕ → ℂ := fun p => (1 - χ p * (p : ℂ) ^ (-((1 : ℕ) : ℂ)))⁻¹
  let g : ℕ → ℝ := fun p => (1 - (p : ℝ) ^ (-1 : ℝ))⁻¹
  calc
    ‖S.prod f‖ ≤ S.prod fun p => ‖f p‖ := by
      exact Finset.norm_prod_le S f
    _ ≤ S.prod g := by
      refine Finset.prod_le_prod (fun p _hp => norm_nonneg (f p)) ?_
      intro p hp
      exact dirichlet_L_character_endpoint_eulerFactor_norm_le_principal χ p
        (Nat.prime_of_mem_primesBelow hp)

/-- Positivity of one principal endpoint Euler factor. -/
lemma dirichlet_L_character_endpoint_principal_abs_eulerFactor_pos
    (p : ℕ) (hp : p.Prime) :
    0 < (1 - (p : ℝ) ^ (-1 : ℝ))⁻¹ := by
  have hp_real : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
  have hlt : (p : ℝ) ^ (-1 : ℝ) < 1 := by
    rw [Real.rpow_neg (Nat.cast_nonneg p)]
    simpa using inv_lt_one_of_one_lt₀ hp_real
  exact inv_pos.mpr (sub_pos.mpr hlt)

/-- The logarithm of the principal absolute endpoint Euler prefix is the
corresponding additive Mertens sum. -/
lemma dirichlet_L_character_endpoint_principal_abs_prefix_log_eq_sum (M : ℕ) :
    Real.log ((M + 1).primesBelow.prod fun p =>
        (1 - (p : ℝ) ^ (-1 : ℝ))⁻¹) =
      ((M + 1).primesBelow.sum fun p =>
        -Real.log (1 - (p : ℝ) ^ (-1 : ℝ))) := by
  rw [Real.log_prod]
  · refine Finset.sum_congr rfl ?_
    intro p hp
    simp [Real.log_inv]
  · intro p hp
    exact ne_of_gt
      (dirichlet_L_character_endpoint_principal_abs_eulerFactor_pos p
        (Nat.prime_of_mem_primesBelow hp))

/-- Monotonicity of the repository's prime cutoff sets in successor notation. -/
lemma primesBelow_succ_mono {a b : ℕ} (h : a ≤ b) :
    (a + 1).primesBelow ⊆ (b + 1).primesBelow := by
  intro p hp
  rw [Nat.mem_primesBelow] at hp ⊢
  exact ⟨lt_of_lt_of_le hp.1 (Nat.succ_le_succ h), hp.2⟩

/-- Split a finite interval difference through an intermediate finite set. -/
lemma finset_sdiff_split_of_subset {α : Type*} [DecidableEq α]
    {A B C : Finset α} (hBA : B ⊆ A) (hAC : A ⊆ C) :
    C \ B = (A \ B) ∪ (C \ A) := by
  ext x
  simp only [Finset.mem_sdiff, Finset.mem_union]
  constructor
  · intro hx
    by_cases hxA : x ∈ A
    · exact Or.inl ⟨hxA, hx.2⟩
    · exact Or.inr ⟨hx.1, hxA⟩
  · intro hx
    rcases hx with hx | hx
    · exact ⟨hAC hx.1, hx.2⟩
    · exact ⟨hx.1, fun hxB => hx.2 (hBA hxB)⟩

/-- Chebyshev's upper bound for the prime-counting function in the repository's
`Nat.primesBelow (M + 1)` cutoff notation.  This is the unweighted cutoff
input needed by the Abel route from Chebyshev bounds to sublinear principal
Euler-prefix growth. -/
lemma dirichlet_L_character_endpoint_primeCounting_primesBelow_le_log4_add
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ M : ℕ in Filter.atTop,
      ((M + 1).primesBelow.card : ℝ) ≤
        (Real.log 4 + ε) * (M : ℝ) / Real.log (M : ℝ) := by
  have harg : Filter.Tendsto (fun M : ℕ => (M : ℝ)) Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop
  have hcheb := harg.eventually (Chebyshev.eventually_primeCounting_le hε)
  filter_upwards [hcheb] with M hM
  simpa [Nat.floor_natCast, Nat.primesBelow_card_eq_primeCounting', Nat.primeCounting] using hM

/-- A one-block Abel/Chebyshev estimate for the reciprocal-prime sum.  On the
dyadic block `M < p ≤ 2M`, each reciprocal is at most `(M + 1)⁻¹`, so
Chebyshev's prime-counting bound controls the whole block. -/
lemma dirichlet_L_character_endpoint_prime_harmonic_dyadic_block_le_primeCounting_bound
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ M : ℕ in Filter.atTop,
      (((2 * M + 1).primesBelow \ (M + 1).primesBelow).sum fun p =>
          (p : ℝ) ^ (-1 : ℝ)) ≤
        ((Real.log 4 + ε) * (2 * M : ℝ) / Real.log (2 * M : ℝ)) *
          ((M + 1 : ℝ)⁻¹) := by
  have hcount :=
    dirichlet_L_character_endpoint_primeCounting_primesBelow_le_log4_add hε
  rw [Filter.eventually_atTop] at hcount ⊢
  rcases hcount with ⟨N₀, hN₀⟩
  refine ⟨N₀, ?_⟩
  intro M hM
  let S : Finset ℕ := (2 * M + 1).primesBelow \ (M + 1).primesBelow
  have hterm : ∀ p ∈ S, (p : ℝ) ^ (-1 : ℝ) ≤ ((M + 1 : ℝ)⁻¹) := by
    intro p hpS
    have hp_big : p ∈ (2 * M + 1).primesBelow := (Finset.mem_sdiff.mp hpS).1
    have hp_not_small : p ∉ (M + 1).primesBelow := (Finset.mem_sdiff.mp hpS).2
    have hp_prime : p.Prime := Nat.prime_of_mem_primesBelow hp_big
    have hM_le_p : M + 1 ≤ p := by
      by_contra hlt
      have hp_lt : p < M + 1 := Nat.lt_of_not_ge hlt
      exact hp_not_small (Nat.mem_primesBelow.mpr ⟨hp_lt, hp_prime⟩)
    have hM_pos : 0 < (M + 1 : ℝ) := by positivity
    have hp_pos : 0 < (p : ℝ) := by
      exact_mod_cast hp_prime.pos
    have hM_le_p_real : (M + 1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hM_le_p
    have hinv : (p : ℝ)⁻¹ ≤ (M + 1 : ℝ)⁻¹ :=
      (inv_le_inv₀ hp_pos hM_pos).mpr hM_le_p_real
    simpa [Real.rpow_neg (Nat.cast_nonneg p)] using hinv
  have hsum_const :
      (S.sum fun p => (p : ℝ) ^ (-1 : ℝ)) ≤ S.card * ((M + 1 : ℝ)⁻¹) := by
    calc
      (S.sum fun p => (p : ℝ) ^ (-1 : ℝ))
          ≤ S.sum fun _p => ((M + 1 : ℝ)⁻¹) := by
        exact Finset.sum_le_sum hterm
      _ = S.card * ((M + 1 : ℝ)⁻¹) := by
        simp
  have hcardS : (S.card : ℝ) ≤ ((2 * M + 1).primesBelow.card : ℝ) := by
    have hsubset : S ⊆ (2 * M + 1).primesBelow := by
      intro p hp
      exact (Finset.mem_sdiff.mp hp).1
    exact_mod_cast Finset.card_le_card hsubset
  have hcountM :
      ((2 * M + 1).primesBelow.card : ℝ) ≤
        (Real.log 4 + ε) * (2 * M : ℝ) / Real.log (2 * M : ℝ) := by
    simpa [Nat.cast_mul] using hN₀ (2 * M) (le_trans hM (Nat.le_mul_of_pos_left M zero_lt_two))
  have hfactor_nonneg : 0 ≤ ((M + 1 : ℝ)⁻¹) := by positivity
  have hcard_bound :
      S.card * ((M + 1 : ℝ)⁻¹) ≤
        ((Real.log 4 + ε) * (2 * M : ℝ) / Real.log (2 * M : ℝ)) *
          ((M + 1 : ℝ)⁻¹) := by
    exact mul_le_mul_of_nonneg_right (le_trans hcardS hcountM) hfactor_nonneg
  exact le_trans hsum_const hcard_bound

/-- A cleaner asymptotic form of the dyadic reciprocal-prime block estimate.
For large `M`, the block `M < p ≤ 2M` contributes at most a constant multiple
of `1 / log (M + 1)`.  This is the local input needed for the later dyadic
summation route to the principal endpoint-prefix growth estimate. -/
lemma dirichlet_L_character_endpoint_prime_harmonic_dyadic_block_le_inv_log
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ M : ℕ in Filter.atTop,
      (((2 * M + 1).primesBelow \ (M + 1).primesBelow).sum fun p =>
          (p : ℝ) ^ (-1 : ℝ)) ≤
        (2 * (Real.log 4 + ε)) / Real.log (M + 1 : ℝ) := by
  have hblock :=
    dirichlet_L_character_endpoint_prime_harmonic_dyadic_block_le_primeCounting_bound
      hε
  have hlarge : ∀ᶠ M : ℕ in Filter.atTop, 2 ≤ M := by
    rw [Filter.eventually_atTop]
    exact ⟨2, fun M hM => hM⟩
  filter_upwards [hblock, hlarge] with M hblockM hM_large
  have hcoef_nonneg : 0 ≤ Real.log 4 + ε := by
    exact add_nonneg (Real.log_nonneg (by norm_num)) (le_of_lt hε)
  have hM_succ_pos : 0 < (M + 1 : ℝ) := by positivity
  have hM_succ_one_lt : 1 < (M + 1 : ℝ) := by
    have hnat : 1 < M + 1 := by omega
    exact_mod_cast hnat
  have hlog_succ_pos : 0 < Real.log (M + 1 : ℝ) :=
    Real.log_pos hM_succ_one_lt
  have htwoM_one_lt : 1 < (2 * M : ℝ) := by
    have hnat : 1 < 2 * M := by nlinarith
    exact_mod_cast hnat
  have hlog_twoM_pos : 0 < Real.log (2 * M : ℝ) :=
    Real.log_pos htwoM_one_lt
  have hsucc_le_twoM : (M + 1 : ℝ) ≤ (2 * M : ℝ) := by
    have hnat : M + 1 ≤ 2 * M := by nlinarith
    exact_mod_cast hnat
  have hlog_inv_le :
      (Real.log (2 * M : ℝ))⁻¹ ≤ (Real.log (M + 1 : ℝ))⁻¹ := by
    have hlog_le : Real.log (M + 1 : ℝ) ≤ Real.log (2 * M : ℝ) :=
      Real.log_le_log hM_succ_pos hsucc_le_twoM
    exact (inv_le_inv₀ hlog_twoM_pos hlog_succ_pos).mpr hlog_le
  have hratio_le_two : (2 * M : ℝ) / (M + 1 : ℝ) ≤ 2 := by
    rw [div_le_iff₀ hM_succ_pos]
    ring_nf
    linarith
  have hfactor :
      ((2 * M : ℝ) / Real.log (2 * M : ℝ)) * ((M + 1 : ℝ)⁻¹) ≤
        2 / Real.log (M + 1 : ℝ) := by
    calc
      ((2 * M : ℝ) / Real.log (2 * M : ℝ)) * ((M + 1 : ℝ)⁻¹)
          = ((2 * M : ℝ) / (M + 1 : ℝ)) * (Real.log (2 * M : ℝ))⁻¹ := by
        ring
      _ ≤ 2 * (Real.log (M + 1 : ℝ))⁻¹ := by
        exact mul_le_mul hratio_le_two hlog_inv_le
          (le_of_lt (inv_pos.mpr hlog_twoM_pos))
          (by positivity)
      _ = 2 / Real.log (M + 1 : ℝ) := by
        rw [div_eq_mul_inv]
  have hrhs :
      ((Real.log 4 + ε) * (2 * M : ℝ) / Real.log (2 * M : ℝ)) *
          ((M + 1 : ℝ)⁻¹) ≤
        (2 * (Real.log 4 + ε)) / Real.log (M + 1 : ℝ) := by
    calc
      ((Real.log 4 + ε) * (2 * M : ℝ) / Real.log (2 * M : ℝ)) *
          ((M + 1 : ℝ)⁻¹)
          = (Real.log 4 + ε) *
              (((2 * M : ℝ) / Real.log (2 * M : ℝ)) *
                ((M + 1 : ℝ)⁻¹)) := by
        ring
      _ ≤ (Real.log 4 + ε) * (2 / Real.log (M + 1 : ℝ)) :=
        mul_le_mul_of_nonneg_left hfactor hcoef_nonneg
      _ = (2 * (Real.log 4 + ε)) / Real.log (M + 1 : ℝ) := by
        ring
  exact le_trans hblockM hrhs

/-- The first `r` dyadic reciprocal-prime blocks telescope to the reciprocal
prime sum over the interval `M < p ≤ 2^r M`.  This is the finite-cover
bookkeeping needed before allowing the number of dyadic blocks to vary with
the upper cutoff. -/
lemma dirichlet_L_character_endpoint_prime_harmonic_dyadic_initial_blocks_sum
    (r M : ℕ) :
    (Finset.range r).sum (fun j =>
      ((((2 * ((2 ^ j) * M) + 1).primesBelow \
          (((2 ^ j) * M) + 1).primesBelow).sum fun p =>
          (p : ℝ) ^ (-1 : ℝ)))) =
      (((2 ^ r * M + 1).primesBelow \ (M + 1).primesBelow).sum fun p =>
        (p : ℝ) ^ (-1 : ℝ)) := by
  induction r with
  | zero =>
      simp
  | succ r ih =>
      rw [Finset.sum_range_succ, ih]
      let B : Finset ℕ := (M + 1).primesBelow
      let A : Finset ℕ := (2 ^ r * M + 1).primesBelow
      let C : Finset ℕ := (2 ^ (r + 1) * M + 1).primesBelow
      have hBA : B ⊆ A := by
        exact primesBelow_succ_mono
          (Nat.le_mul_of_pos_left M (pow_pos (by norm_num : (0 : ℕ) < 2) r))
      have hAC : A ⊆ C := by
        exact primesBelow_succ_mono (by
          have hpow : 2 ^ r ≤ 2 ^ (r + 1) :=
            Nat.pow_le_pow_right (by norm_num : 0 < 2) (Nat.le_succ r)
          exact Nat.mul_le_mul_right M hpow)
      have hsplit : C \ B = (A \ B) ∪ (C \ A) :=
        finset_sdiff_split_of_subset hBA hAC
      have hdisj : Disjoint (A \ B) (C \ A) := by
        rw [Finset.disjoint_left]
        intro x hxAB hxCA
        rw [Finset.mem_sdiff] at hxAB hxCA
        exact hxCA.2 hxAB.1
      have hC_eq :
          C \ A =
            (2 * ((2 ^ r) * M) + 1).primesBelow \
              (((2 ^ r) * M) + 1).primesBelow := by
        simp [C, A, pow_succ, Nat.mul_left_comm, Nat.mul_comm]
      calc
        (∑ x ∈ A \ B, (x : ℝ) ^ (-1 : ℝ)) +
            ∑ x ∈ (2 * (2 ^ r * M) + 1).primesBelow \
                (2 ^ r * M + 1).primesBelow,
              (x : ℝ) ^ (-1 : ℝ)
            = (∑ x ∈ A \ B, (x : ℝ) ^ (-1 : ℝ)) +
                ∑ x ∈ C \ A, (x : ℝ) ^ (-1 : ℝ) := by
              rw [hC_eq]
        _ = ∑ x ∈ (A \ B) ∪ (C \ A), (x : ℝ) ^ (-1 : ℝ) := by
              rw [Finset.sum_union hdisj]
        _ = ∑ x ∈ C \ B, (x : ℝ) ^ (-1 : ℝ) := by
              rw [hsplit]
        _ = ∑ x ∈ (2 ^ (r + 1) * M + 1).primesBelow \
              (M + 1).primesBelow,
              (x : ℝ) ^ (-1 : ℝ) := rfl

/-- The scaled dyadic block estimate is uniform in the dyadic scale.  This is
the version needed when the number of dyadic blocks is allowed to depend on
the cutoff. -/
lemma dirichlet_L_character_endpoint_prime_harmonic_dyadic_scaled_block_le_inv_log_uniform
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ M : ℕ in Filter.atTop,
      ∀ j : ℕ,
        (((2 * ((2 ^ j) * M) + 1).primesBelow \
            (((2 ^ j) * M) + 1).primesBelow).sum fun p =>
            (p : ℝ) ^ (-1 : ℝ)) ≤
          (2 * (Real.log 4 + ε)) / Real.log (((2 ^ j) * M : ℕ) + 1 : ℝ) := by
  have hblock :=
    dirichlet_L_character_endpoint_prime_harmonic_dyadic_block_le_inv_log
      hε
  rw [Filter.eventually_atTop] at hblock ⊢
  rcases hblock with ⟨N₀, hN₀⟩
  refine ⟨N₀, ?_⟩
  intro M hM j
  have hpow_pos : 0 < 2 ^ j := pow_pos (by norm_num : (0 : ℕ) < 2) j
  exact hN₀ ((2 ^ j) * M) (le_trans hM (Nat.le_mul_of_pos_left M hpow_pos))

/-- A cutoff-uniform version of the finite dyadic block summation estimate:
for all sufficiently large base cutoffs `M`, every initial family of `r`
dyadic blocks is bounded by `r` times the common logarithmic block bound. -/
lemma dirichlet_L_character_endpoint_prime_harmonic_dyadic_scaled_blocks_range_sum_le_card_inv_log_uniform
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ M : ℕ in Filter.atTop,
      ∀ r : ℕ,
        ((Finset.range r).sum fun j =>
          (((2 * ((2 ^ j) * M) + 1).primesBelow \
              (((2 ^ j) * M) + 1).primesBelow).sum fun p =>
              (p : ℝ) ^ (-1 : ℝ))) ≤
          (r : ℝ) *
            ((2 * (Real.log 4 + ε)) / Real.log (M + 1 : ℝ)) := by
  classical
  have hblocks :=
    dirichlet_L_character_endpoint_prime_harmonic_dyadic_scaled_block_le_inv_log_uniform
      hε
  have hlarge : ∀ᶠ M : ℕ in Filter.atTop, 2 ≤ M := by
    rw [Filter.eventually_atTop]
    exact ⟨2, fun M hM => hM⟩
  filter_upwards [hblocks, hlarge] with M hblocksM hM_large r
  let C : ℝ := 2 * (Real.log 4 + ε)
  have hC_nonneg : 0 ≤ C := by
    exact mul_nonneg zero_le_two
      (add_nonneg (Real.log_nonneg (by norm_num)) (le_of_lt hε))
  have hM_succ_pos : 0 < (M + 1 : ℝ) := by positivity
  have hM_succ_one_lt : 1 < (M + 1 : ℝ) := by
    have hnat : 1 < M + 1 := by omega
    exact_mod_cast hnat
  have hlog_succ_pos : 0 < Real.log (M + 1 : ℝ) :=
    Real.log_pos hM_succ_one_lt
  have hterm :
      ∀ j ∈ Finset.range r,
        (((2 * ((2 ^ j) * M) + 1).primesBelow \
            (((2 ^ j) * M) + 1).primesBelow).sum fun p =>
            (p : ℝ) ^ (-1 : ℝ)) ≤
          C / Real.log (M + 1 : ℝ) := by
    intro j _hj
    have hpow_pos : 0 < 2 ^ j := pow_pos (by norm_num : (0 : ℕ) < 2) j
    have hbase_le_nat : M + 1 ≤ ((2 ^ j) * M) + 1 := by
      exact Nat.succ_le_succ (Nat.le_mul_of_pos_left M hpow_pos)
    have hbase_le_real :
        (M + 1 : ℝ) ≤ (((2 ^ j) * M : ℕ) + 1 : ℝ) := by
      exact_mod_cast hbase_le_nat
    have hlog_le :
        Real.log (M + 1 : ℝ) ≤
          Real.log (((2 ^ j) * M : ℕ) + 1 : ℝ) :=
      Real.log_le_log hM_succ_pos hbase_le_real
    have hlog_scaled_pos :
        0 < Real.log (((2 ^ j) * M : ℕ) + 1 : ℝ) :=
      lt_of_lt_of_le hlog_succ_pos hlog_le
    have hinv :
        (Real.log (((2 ^ j) * M : ℕ) + 1 : ℝ))⁻¹ ≤
          (Real.log (M + 1 : ℝ))⁻¹ :=
      (inv_le_inv₀ hlog_scaled_pos hlog_succ_pos).mpr hlog_le
    have hfactor :
        C / Real.log (((2 ^ j) * M : ℕ) + 1 : ℝ) ≤
          C / Real.log (M + 1 : ℝ) := by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_left hinv hC_nonneg
    exact le_trans (by simpa [C] using hblocksM j) hfactor
  calc
    ((Finset.range r).sum fun j =>
        (((2 * ((2 ^ j) * M) + 1).primesBelow \
            (((2 ^ j) * M) + 1).primesBelow).sum fun p =>
            (p : ℝ) ^ (-1 : ℝ)))
        ≤ (Finset.range r).sum fun _j => C / Real.log (M + 1 : ℝ) := by
          exact Finset.sum_le_sum hterm
    _ = (r : ℝ) * (C / Real.log (M + 1 : ℝ)) := by
          simp
    _ = (r : ℝ) *
          ((2 * (Real.log 4 + ε)) / Real.log (M + 1 : ℝ)) := by
          rfl

/-- Cutoff-uniform dyadic initial-segment estimate.  Unlike the preceding
fixed-`r` version, the eventual lower cutoff is independent of the number of
dyadic blocks, so a later Abel summation may choose `r` from the endpoint
cutoff. -/
lemma dirichlet_L_character_endpoint_prime_harmonic_dyadic_initial_segment_le_card_inv_log_uniform
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ M : ℕ in Filter.atTop,
      ∀ r : ℕ,
        (((2 ^ r * M + 1).primesBelow \ (M + 1).primesBelow).sum fun p =>
            (p : ℝ) ^ (-1 : ℝ)) ≤
          (r : ℝ) *
            ((2 * (Real.log 4 + ε)) / Real.log (M + 1 : ℝ)) := by
  have hblocks :=
    dirichlet_L_character_endpoint_prime_harmonic_dyadic_scaled_blocks_range_sum_le_card_inv_log_uniform
      hε
  filter_upwards [hblocks] with M hM r
  calc
    (((2 ^ r * M + 1).primesBelow \ (M + 1).primesBelow).sum fun p =>
        (p : ℝ) ^ (-1 : ℝ))
        = (Finset.range r).sum (fun j =>
            ((((2 * ((2 ^ j) * M) + 1).primesBelow \
                (((2 ^ j) * M) + 1).primesBelow).sum fun p =>
                (p : ℝ) ^ (-1 : ℝ)))) := by
              rw [dirichlet_L_character_endpoint_prime_harmonic_dyadic_initial_blocks_sum]
    _ ≤ (r : ℝ) *
          ((2 * (Real.log 4 + ε)) / Real.log (M + 1 : ℝ)) := hM r

/-- A cutoff-dependent dyadic cover for reciprocal-prime tails.  The uniform
initial-segment estimate can be applied with `r = Nat.clog 2 (K + 1)`, so any
tail from a large base cutoff `M` to a later cutoff `K` is bounded by the
number of dyadic blocks needed to dominate `K`. -/
lemma dirichlet_L_character_endpoint_prime_harmonic_tail_le_clog_inv_log_uniform
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ M : ℕ in Filter.atTop,
      ∀ K : ℕ, M ≤ K →
        (((K + 1).primesBelow \ (M + 1).primesBelow).sum fun p =>
            (p : ℝ) ^ (-1 : ℝ)) ≤
          (Nat.clog 2 (K + 1) : ℝ) *
            ((2 * (Real.log 4 + ε)) / Real.log (M + 1 : ℝ)) := by
  have hdyadic :=
    dirichlet_L_character_endpoint_prime_harmonic_dyadic_initial_segment_le_card_inv_log_uniform
      hε
  have hlarge : ∀ᶠ M : ℕ in Filter.atTop, 1 ≤ M := by
    rw [Filter.eventually_atTop]
    exact ⟨1, fun M hM => hM⟩
  filter_upwards [hdyadic, hlarge] with M hdyadicM hM_pos K _hMK
  let r : ℕ := Nat.clog 2 (K + 1)
  have hK_le_pow : K + 1 ≤ 2 ^ r := by
    exact (Nat.clog_le_iff_le_pow (by norm_num : 1 < 2)).mp le_rfl
  have hK_le_mul : K ≤ 2 ^ r * M := by
    exact le_trans (Nat.le_succ K)
      (le_trans hK_le_pow (Nat.le_mul_of_pos_right (2 ^ r) hM_pos))
  have hupper :
      (K + 1).primesBelow ⊆ (2 ^ r * M + 1).primesBelow :=
    primesBelow_succ_mono hK_le_mul
  have hsubset :
      (K + 1).primesBelow \ (M + 1).primesBelow ⊆
        (2 ^ r * M + 1).primesBelow \ (M + 1).primesBelow := by
    intro p hp
    rw [Finset.mem_sdiff] at hp ⊢
    exact ⟨hupper hp.1, hp.2⟩
  have hsum_subset :
      (((K + 1).primesBelow \ (M + 1).primesBelow).sum fun p =>
          (p : ℝ) ^ (-1 : ℝ)) ≤
        (((2 ^ r * M + 1).primesBelow \ (M + 1).primesBelow).sum fun p =>
          (p : ℝ) ^ (-1 : ℝ)) := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
      (by
        intro p _hp_upper _hp_tail
        exact Real.rpow_nonneg (Nat.cast_nonneg p) _)
  exact le_trans hsum_subset (by simpa [r] using hdyadicM r)

/-- The dyadic ceiling used in the Chebyshev tail bound is controlled by the
ordinary real logarithm. -/
lemma nat_clog_two_succ_cast_le_log_div_log_two_add_one (K : ℕ) :
    (Nat.clog 2 (K + 1) : ℝ) ≤
      Real.log (K + 1 : ℝ) / Real.log 2 + 1 := by
  have hsucc_one : (1 : ℝ) ≤ (K + 1 : ℝ) := by
    exact_mod_cast (Nat.succ_le_succ (Nat.zero_le K) : 1 ≤ K + 1)
  have hlog_nonneg : 0 ≤ Real.logb 2 (K + 1 : ℝ) := by
    exact Real.logb_nonneg (by norm_num : (1 : ℝ) < 2) hsucc_one
  have hceil : (⌈Real.logb 2 (K + 1 : ℝ)⌉₊ : ℝ) <
      Real.logb 2 (K + 1 : ℝ) + 1 :=
    Nat.ceil_lt_add_one hlog_nonneg
  have hceil_eq :
      ⌈Real.logb 2 (K + 1 : ℝ)⌉₊ = Nat.clog 2 (K + 1) := by
    simpa using (Real.natCeil_logb_natCast 2 (K + 1))
  have hle :
      (Nat.clog 2 (K + 1) : ℝ) ≤
        Real.logb 2 (K + 1 : ℝ) + 1 :=
    le_of_lt (by simpa [hceil_eq] using hceil)
  simpa [Real.logb] using hle

/-- The cutoff-uniform reciprocal-prime tail bound with the dyadic ceiling
converted to an ordinary real-logarithmic upper bound.  This is the analytic
bookkeeping needed before proving a principal Euler-prefix growth estimate
from the Chebyshev/Abel route. -/
lemma dirichlet_L_character_endpoint_prime_harmonic_tail_le_log_inv_log_uniform
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ M : ℕ in Filter.atTop,
      ∀ K : ℕ, M ≤ K →
        (((K + 1).primesBelow \ (M + 1).primesBelow).sum fun p =>
            (p : ℝ) ^ (-1 : ℝ)) ≤
          (Real.log (K + 1 : ℝ) / Real.log 2 + 1) *
            ((2 * (Real.log 4 + ε)) / Real.log (M + 1 : ℝ)) := by
  have htail :=
    dirichlet_L_character_endpoint_prime_harmonic_tail_le_clog_inv_log_uniform hε
  have hlarge : ∀ᶠ M : ℕ in Filter.atTop, 2 ≤ M := by
    rw [Filter.eventually_atTop]
    exact ⟨2, fun M hM => hM⟩
  filter_upwards [htail, hlarge] with M htailM hM_large K hMK
  let C : ℝ := (2 * (Real.log 4 + ε)) / Real.log (M + 1 : ℝ)
  have hM_succ_one_lt : 1 < (M + 1 : ℝ) := by
    have hnat : 1 < M + 1 := by omega
    exact_mod_cast hnat
  have hlog_pos : 0 < Real.log (M + 1 : ℝ) :=
    Real.log_pos hM_succ_one_lt
  have hcoef_nonneg : 0 ≤ 2 * (Real.log 4 + ε) := by
    exact mul_nonneg zero_le_two
      (add_nonneg (Real.log_nonneg (by norm_num)) (le_of_lt hε))
  have hC_nonneg : 0 ≤ C := by
    exact div_nonneg hcoef_nonneg (le_of_lt hlog_pos)
  have hclog_le := nat_clog_two_succ_cast_le_log_div_log_two_add_one K
  have hmul :
      (Nat.clog 2 (K + 1) : ℝ) * C ≤
        (Real.log (K + 1 : ℝ) / Real.log 2 + 1) * C := by
    exact mul_le_mul_of_nonneg_right hclog_le hC_nonneg
  exact le_trans (by simpa [C] using htailM K hMK) hmul

/-- The Chebyshev/Abel dyadic tail estimate implies that the reciprocal-prime
prefix is eventually smaller than any fixed positive multiple of
`log (K + 1)`.  This is the first growth statement needed for the
principal Euler-prefix `o(M)` route. -/
lemma dirichlet_L_character_endpoint_prime_harmonic_prefix_le_log_mul
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ K : ℕ in Filter.atTop,
      ((K + 1).primesBelow.sum fun p => (p : ℝ) ^ (-1 : ℝ)) ≤
        ε * Real.log (K + 1 : ℝ) := by
  classical
  have hlog_two_pos : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  let A : ℝ := 2 * (Real.log 4 + 1)
  have harg :
      Filter.Tendsto (fun M : ℕ => (M + 1 : ℝ)) Filter.atTop Filter.atTop := by
    simpa [Nat.cast_add, Nat.cast_one] using
      (tendsto_natCast_atTop_atTop.atTop_add (tendsto_const_nhds (x := (1 : ℝ))))
  have hlog_atTop :
      Filter.Tendsto (fun M : ℕ => Real.log (M + 1 : ℝ))
        Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp harg
  have hcoef_tendsto :
      Filter.Tendsto (fun M : ℕ => A * (Real.log (M + 1 : ℝ))⁻¹)
        Filter.atTop (nhds 0) := by
    simpa using (Filter.Tendsto.inv_tendsto_atTop hlog_atTop).const_mul A
  have hcoef_small :
      ∀ᶠ M : ℕ in Filter.atTop,
        A / Real.log (M + 1 : ℝ) ≤ ε * Real.log 2 / 4 := by
    have htarget_pos : 0 < ε * Real.log 2 / 4 := by positivity
    have hsmall :
        ∀ᶠ M : ℕ in Filter.atTop,
          A * (Real.log (M + 1 : ℝ))⁻¹ < ε * Real.log 2 / 4 :=
      (tendsto_order.1 hcoef_tendsto).2 (ε * Real.log 2 / 4) htarget_pos
    filter_upwards [hsmall] with M hM
    simpa [div_eq_mul_inv] using le_of_lt hM
  have htail :=
    dirichlet_L_character_endpoint_prime_harmonic_tail_le_log_inv_log_uniform
      (by norm_num : (0 : ℝ) < 1)
  rw [Filter.eventually_atTop] at htail hcoef_small
  rcases htail with ⟨M₁, hM₁⟩
  rcases hcoef_small with ⟨M₂, hM₂⟩
  let M₀ : ℕ := max M₁ M₂
  let C : ℝ := A / Real.log (M₀ + 1 : ℝ)
  let B : ℝ :=
    ((M₀ + 1).primesBelow.sum fun p => (p : ℝ) ^ (-1 : ℝ)) + C
  have htail_M₀ :
      ∀ K : ℕ, M₀ ≤ K →
        (((K + 1).primesBelow \ (M₀ + 1).primesBelow).sum fun p =>
            (p : ℝ) ^ (-1 : ℝ)) ≤
          (Real.log (K + 1 : ℝ) / Real.log 2 + 1) * C := by
    intro K hMK
    simpa [A, C] using hM₁ M₀ (le_max_left M₁ M₂) K hMK
  have hC_small : C ≤ ε * Real.log 2 / 4 := by
    simpa [A, C, M₀] using hM₂ M₀ (le_max_right M₁ M₂)
  have hcoeff_small : C / Real.log 2 ≤ ε / 4 := by
    rw [div_le_iff₀ hlog_two_pos]
    linarith
  have hlog_scaled_atTop :
      Filter.Tendsto (fun K : ℕ => (3 * ε / 4) * Real.log (K + 1 : ℝ))
        Filter.atTop Filter.atTop := by
    exact Filter.Tendsto.const_mul_atTop (by positivity : 0 < 3 * ε / 4)
      hlog_atTop
  have hB_log :
      ∀ᶠ K : ℕ in Filter.atTop,
        B ≤ (3 * ε / 4) * Real.log (K + 1 : ℝ) :=
    hlog_scaled_atTop.eventually_ge_atTop B
  filter_upwards [Filter.eventually_ge_atTop M₀, hB_log] with K hMK hB_le
  have hsubset : (M₀ + 1).primesBelow ⊆ (K + 1).primesBelow :=
    primesBelow_succ_mono hMK
  have hsum_split :
      ((K + 1).primesBelow.sum fun p => (p : ℝ) ^ (-1 : ℝ)) =
        (((K + 1).primesBelow \ (M₀ + 1).primesBelow).sum fun p =>
            (p : ℝ) ^ (-1 : ℝ)) +
          ((M₀ + 1).primesBelow.sum fun p => (p : ℝ) ^ (-1 : ℝ)) := by
    simpa using
      (Finset.sum_sdiff
        (s₁ := (M₀ + 1).primesBelow) (s₂ := (K + 1).primesBelow)
        (f := fun p => (p : ℝ) ^ (-1 : ℝ)) hsubset).symm
  have hlog_nonneg : 0 ≤ Real.log (K + 1 : ℝ) := by
    exact Real.log_nonneg
      (by exact_mod_cast (Nat.succ_le_succ (Nat.zero_le K) : 1 ≤ K + 1))
  have htail_le :
      (((K + 1).primesBelow \ (M₀ + 1).primesBelow).sum fun p =>
          (p : ℝ) ^ (-1 : ℝ)) ≤
        (ε / 4) * Real.log (K + 1 : ℝ) + C := by
    have hcoeff_mul :
        (C / Real.log 2) * Real.log (K + 1 : ℝ) ≤
          (ε / 4) * Real.log (K + 1 : ℝ) :=
      mul_le_mul_of_nonneg_right hcoeff_small hlog_nonneg
    calc
      (((K + 1).primesBelow \ (M₀ + 1).primesBelow).sum fun p =>
          (p : ℝ) ^ (-1 : ℝ))
          ≤ (Real.log (K + 1 : ℝ) / Real.log 2 + 1) * C := htail_M₀ K hMK
      _ = (C / Real.log 2) * Real.log (K + 1 : ℝ) + C := by ring
      _ ≤ (ε / 4) * Real.log (K + 1 : ℝ) + C := by
        linarith
  calc
    ((K + 1).primesBelow.sum fun p => (p : ℝ) ^ (-1 : ℝ))
        =
          (((K + 1).primesBelow \ (M₀ + 1).primesBelow).sum fun p =>
              (p : ℝ) ^ (-1 : ℝ)) +
            ((M₀ + 1).primesBelow.sum fun p => (p : ℝ) ^ (-1 : ℝ)) := hsum_split
    _ ≤ (ε / 4) * Real.log (K + 1 : ℝ) + B := by
      dsimp [B]
      linarith
    _ ≤ ε * Real.log (K + 1 : ℝ) := by
      linarith

/-- Chebyshev/Abel consequence: the reciprocal-prime prefix is
`o(log M)`.  This is stronger than what is needed for sublinear principal
Euler-prefix growth. -/
lemma dirichlet_L_character_endpoint_prime_harmonic_prefix_isLittleO_log :
    (fun M : ℕ =>
      ((M + 1).primesBelow.sum fun p => (p : ℝ) ^ (-1 : ℝ))) =o[Filter.atTop]
      (fun M : ℕ => Real.log (M + 1 : ℝ)) := by
  rw [Asymptotics.isLittleO_iff]
  intro c hc
  have hprefix :=
    dirichlet_L_character_endpoint_prime_harmonic_prefix_le_log_mul hc
  filter_upwards [hprefix] with M hM
  have hsum_nonneg :
      0 ≤ ((M + 1).primesBelow.sum fun p => (p : ℝ) ^ (-1 : ℝ)) := by
    exact Finset.sum_nonneg fun p _hp =>
      Real.rpow_nonneg (Nat.cast_nonneg p) _
  have hlog_nonneg : 0 ≤ Real.log (M + 1 : ℝ) := by
    exact Real.log_nonneg
      (by exact_mod_cast (Nat.succ_le_succ (Nat.zero_le M) : 1 ≤ M + 1))
  simpa [Real.norm_eq_abs, abs_of_nonneg hsum_nonneg, abs_of_nonneg hlog_nonneg]
    using hM

/-- One logarithmic principal Euler factor differs from the reciprocal-prime
term by at most a summable square term. -/
lemma dirichlet_L_character_endpoint_principal_abs_log_factor_le_harmonic_sq
    (p : ℕ) (hp : p.Prime) :
    -Real.log (1 - (p : ℝ) ^ (-1 : ℝ)) ≤
      (p : ℝ) ^ (-1 : ℝ) + 2 * (p : ℝ) ^ (-2 : ℝ) := by
  let x : ℝ := (p : ℝ) ^ (-1 : ℝ)
  have hp_real_two : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hx_nonneg : 0 ≤ x := Real.rpow_nonneg (Nat.cast_nonneg p) _
  have hx_le_half : x ≤ (1 / 2 : ℝ) := by
    have h_inv : (p : ℝ)⁻¹ ≤ (2 : ℝ)⁻¹ :=
      (inv_le_inv₀
        (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) hp_real_two)
        (by norm_num : (0 : ℝ) < 2)).mpr hp_real_two
    simpa [x, Real.rpow_neg (Nat.cast_nonneg p)] using h_inv
  have hx_lt_one : x < 1 := lt_of_le_of_lt hx_le_half (by norm_num)
  have hden_pos : 0 < 1 - x := sub_pos.mpr hx_lt_one
  have hlog_le :
      -Real.log (1 - x) ≤ (1 - x)⁻¹ - 1 := by
    calc
      -Real.log (1 - x) = Real.log ((1 - x)⁻¹) := by rw [Real.log_inv]
      _ ≤ (1 - x)⁻¹ - 1 :=
        Real.log_le_sub_one_of_pos (inv_pos.mpr hden_pos)
  have hfrac_le : (1 - x)⁻¹ - 1 ≤ x + 2 * x ^ 2 := by
    have hfrac_eq : (1 - x)⁻¹ - 1 = x / (1 - x) := by
      field_simp [ne_of_gt hden_pos]
      ring
    rw [hfrac_eq]
    rw [div_le_iff₀ hden_pos]
    nlinarith [sq_nonneg x, hx_nonneg, hx_le_half]
  have hx_sq : x ^ 2 = (p : ℝ) ^ (-2 : ℝ) := by
    dsimp only [x]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg p)]
    norm_num
  have hx_one : x = (p : ℝ) ^ (-1 : ℝ) := rfl
  calc
    -Real.log (1 - (p : ℝ) ^ (-1 : ℝ)) = -Real.log (1 - x) := rfl
    _ ≤ (1 - x)⁻¹ - 1 := hlog_le
    _ ≤ x + 2 * x ^ 2 := hfrac_le
    _ = (p : ℝ) ^ (-1 : ℝ) + 2 * (p : ℝ) ^ (-2 : ℝ) := by
      rw [hx_one, hx_sq]

/-- Chebyshev/Abel consequence for the logarithm of the principal
absolute endpoint Euler prefix: the additive logarithmic prefix is still
`o(log M)`.  This combines the reciprocal-prime `o(log M)` estimate with the
already formal summable `p^{-2}` correction term. -/
lemma dirichlet_L_character_endpoint_principal_abs_prefix_log_isLittleO_log :
    (fun M : ℕ =>
      ((M + 1).primesBelow.sum fun p =>
        -Real.log (1 - (p : ℝ) ^ (-1 : ℝ)))) =o[Filter.atTop]
      (fun M : ℕ => Real.log (M + 1 : ℝ)) := by
  classical
  let sqTail : ℕ → ℝ := fun M =>
    ((M + 1).primesBelow.sum fun p => 2 * (p : ℝ) ^ (-2 : ℝ))
  let C : ℝ := ∑' n : ℕ, 2 * (n : ℝ) ^ (-2 : ℝ)
  have hsummable_sq : Summable (fun n : ℕ => 2 * (n : ℝ) ^ (-2 : ℝ)) := by
    exact (Real.summable_nat_rpow.mpr (by norm_num : (-2 : ℝ) < -1)).mul_left 2
  have hsquare_bound : ∀ M : ℕ, sqTail M ≤ C := by
    intro M
    simpa [sqTail, C] using
      (Summable.sum_le_tsum (s := (M + 1).primesBelow)
        (f := fun n : ℕ => 2 * (n : ℝ) ^ (-2 : ℝ))
        (fun n _hn => mul_nonneg zero_le_two (Real.rpow_nonneg (Nat.cast_nonneg n) _))
        hsummable_sq)
  have hsqLittle :
      sqTail =o[Filter.atTop] (fun M : ℕ => Real.log (M + 1 : ℝ)) := by
    rw [Asymptotics.isLittleO_iff]
    intro c hc
    have harg :
        Filter.Tendsto (fun M : ℕ => (M + 1 : ℝ)) Filter.atTop Filter.atTop := by
      simpa [Nat.cast_add, Nat.cast_one] using
        (tendsto_natCast_atTop_atTop.atTop_add (tendsto_const_nhds (x := (1 : ℝ))))
    have hlog_atTop :
        Filter.Tendsto (fun M : ℕ => Real.log (M + 1 : ℝ))
          Filter.atTop Filter.atTop :=
      Real.tendsto_log_atTop.comp harg
    have hscaled_atTop :
        Filter.Tendsto (fun M : ℕ => c * Real.log (M + 1 : ℝ))
          Filter.atTop Filter.atTop :=
      Filter.Tendsto.const_mul_atTop hc hlog_atTop
    have hC_eventually :
        ∀ᶠ M : ℕ in Filter.atTop, C ≤ c * Real.log (M + 1 : ℝ) :=
      hscaled_atTop.eventually_ge_atTop C
    filter_upwards [hC_eventually] with M hC_le
    have hsq_nonneg : 0 ≤ sqTail M := by
      exact Finset.sum_nonneg fun p _hp =>
        mul_nonneg zero_le_two (Real.rpow_nonneg (Nat.cast_nonneg p) _)
    have hlog_nonneg : 0 ≤ Real.log (M + 1 : ℝ) := by
      exact Real.log_nonneg
        (by exact_mod_cast (Nat.succ_le_succ (Nat.zero_le M) : 1 ≤ M + 1))
    have hsq_le : sqTail M ≤ c * Real.log (M + 1 : ℝ) :=
      le_trans (hsquare_bound M) hC_le
    simpa [Real.norm_eq_abs, abs_of_nonneg hsq_nonneg, abs_of_nonneg hlog_nonneg]
      using hsq_le
  rw [Asymptotics.isLittleO_iff]
  intro c hc
  have hhalf_pos : 0 < c / 2 := by positivity
  have hharmonic :=
    (Asymptotics.isLittleO_iff.mp
      dirichlet_L_character_endpoint_prime_harmonic_prefix_isLittleO_log) hhalf_pos
  have hsquare := (Asymptotics.isLittleO_iff.mp hsqLittle) hhalf_pos
  filter_upwards [hharmonic, hsquare] with M hharm hsquareM
  let H : ℝ := ((M + 1).primesBelow.sum fun p => (p : ℝ) ^ (-1 : ℝ))
  let Q : ℝ := sqTail M
  let Lg : ℝ := ((M + 1).primesBelow.sum fun p =>
    -Real.log (1 - (p : ℝ) ^ (-1 : ℝ)))
  have hH_nonneg : 0 ≤ H := by
    exact Finset.sum_nonneg fun p _hp =>
      Real.rpow_nonneg (Nat.cast_nonneg p) _
  have hQ_nonneg : 0 ≤ Q := by
    dsimp [Q, sqTail]
    exact Finset.sum_nonneg fun p _hp =>
      mul_nonneg zero_le_two (Real.rpow_nonneg (Nat.cast_nonneg p) _)
  have hLg_nonneg : 0 ≤ Lg := by
    dsimp [Lg]
    refine Finset.sum_nonneg ?_
    intro p hp
    let x : ℝ := (p : ℝ) ^ (-1 : ℝ)
    have hp_real : (1 : ℝ) < (p : ℝ) := by
      exact_mod_cast (Nat.prime_of_mem_primesBelow hp).one_lt
    have hx_lt_one : x < 1 := by
      dsimp [x]
      rw [Real.rpow_neg (Nat.cast_nonneg p)]
      simpa using inv_lt_one_of_one_lt₀ hp_real
    have hx_nonneg : 0 ≤ x := Real.rpow_nonneg (Nat.cast_nonneg p) _
    have hx_pos : 0 < 1 - x := sub_pos.mpr hx_lt_one
    have hone_le_inv : (1 : ℝ) ≤ (1 - x)⁻¹ := by
      have hden_le_one : 1 - x ≤ 1 := by linarith
      exact (one_le_inv₀ hx_pos).2 hden_le_one
    have hlog_nonneg : 0 ≤ Real.log ((1 - x)⁻¹) :=
      Real.log_nonneg hone_le_inv
    have hlog_inv : Real.log ((1 - x)⁻¹) = -Real.log (1 - x) := by
      rw [Real.log_inv]
    have hneg_nonneg : 0 ≤ -Real.log (1 - x) := by
      rw [← hlog_inv]
      exact hlog_nonneg
    simpa [x] using hneg_nonneg
  have hlog_nonneg : 0 ≤ Real.log (M + 1 : ℝ) := by
    exact Real.log_nonneg
      (by exact_mod_cast (Nat.succ_le_succ (Nat.zero_le M) : 1 ≤ M + 1))
  have hLg_le : Lg ≤ H + Q := by
    dsimp [Lg, H, Q, sqTail]
    calc
      ((M + 1).primesBelow.sum fun p =>
          -Real.log (1 - (p : ℝ) ^ (-1 : ℝ)))
          ≤ (M + 1).primesBelow.sum fun p =>
              ((p : ℝ) ^ (-1 : ℝ) + 2 * (p : ℝ) ^ (-2 : ℝ)) := by
        refine Finset.sum_le_sum ?_
        intro p hp
        exact
          dirichlet_L_character_endpoint_principal_abs_log_factor_le_harmonic_sq p
            (Nat.prime_of_mem_primesBelow hp)
      _ = ((M + 1).primesBelow.sum fun p => (p : ℝ) ^ (-1 : ℝ)) +
          ((M + 1).primesBelow.sum fun p => 2 * (p : ℝ) ^ (-2 : ℝ)) := by
        rw [Finset.sum_add_distrib]
  have hH_small : H ≤ (c / 2) * Real.log (M + 1 : ℝ) := by
    simpa [H, Real.norm_eq_abs, abs_of_nonneg hH_nonneg, abs_of_nonneg hlog_nonneg]
      using hharm
  have hQ_small : Q ≤ (c / 2) * Real.log (M + 1 : ℝ) := by
    simpa [Q, Real.norm_eq_abs, abs_of_nonneg hQ_nonneg, abs_of_nonneg hlog_nonneg]
      using hsquareM
  have hLg_small : Lg ≤ c * Real.log (M + 1 : ℝ) := by
    linarith
  have hLg_norm : ‖Lg‖ = Lg := by
    simp [Real.norm_eq_abs, abs_of_nonneg hLg_nonneg]
  have hlog_norm : ‖Real.log (M + 1 : ℝ)‖ = Real.log (M + 1 : ℝ) := by
    simp [Real.norm_eq_abs, abs_of_nonneg hlog_nonneg]
  have hgoal : ‖Lg‖ ≤ c * ‖Real.log (M + 1 : ℝ)‖ := by
    rw [hLg_norm, hlog_norm]
    exact hLg_small
  simpa [Lg] using hgoal

/-- The logarithmic-prefix `o(log M)` bound obtained from the
Chebyshev/Abel reciprocal-prime estimates implies the sublinear principal
absolute endpoint-prefix estimate. -/
lemma dirichlet_L_character_endpoint_principal_abs_prefix_isLittleO :
    (fun M : ℕ => (M + 1).primesBelow.prod fun p =>
        (1 - (p : ℝ) ^ (-1 : ℝ))⁻¹) =o[Filter.atTop]
      (fun M : ℕ => (M + 1 : ℝ)) := by
  classical
  have hlogLittle :=
    dirichlet_L_character_endpoint_principal_abs_prefix_log_isLittleO_log
  have harg :
      Filter.Tendsto (fun M : ℕ => (M + 1 : ℝ)) Filter.atTop Filter.atTop := by
    simpa [Nat.cast_add, Nat.cast_one] using
      (tendsto_natCast_atTop_atTop.atTop_add (tendsto_const_nhds (x := (1 : ℝ))))
  rw [Asymptotics.isLittleO_iff]
  intro c hc
  have hhalf_pos : (0 : ℝ) < 1 / 2 := by norm_num
  have hlog_small :=
    (Asymptotics.isLittleO_iff.mp hlogLittle) hhalf_pos
  have hsqrt_atTop :
      Filter.Tendsto (fun M : ℕ => Real.sqrt (M + 1 : ℝ))
        Filter.atTop Filter.atTop :=
    Real.tendsto_sqrt_atTop.comp harg
  have hsqrt_large :
      ∀ᶠ M : ℕ in Filter.atTop, 1 ≤ c * Real.sqrt (M + 1 : ℝ) :=
    (Filter.Tendsto.const_mul_atTop hc hsqrt_atTop).eventually_ge_atTop 1
  filter_upwards [hlog_small, hsqrt_large] with M hlog_smallM hsqrt_largeM
  let P : ℝ := (M + 1).primesBelow.prod fun p =>
    (1 - (p : ℝ) ^ (-1 : ℝ))⁻¹
  let S : ℝ := (M + 1).primesBelow.sum fun p =>
    -Real.log (1 - (p : ℝ) ^ (-1 : ℝ))
  let N : ℝ := M + 1
  have hP_nonneg : 0 ≤ P := by
    exact Finset.prod_nonneg fun p hp =>
      le_of_lt <|
        dirichlet_L_character_endpoint_principal_abs_eulerFactor_pos p
          (Nat.prime_of_mem_primesBelow hp)
  have hP_pos : 0 < P := by
    exact Finset.prod_pos fun p hp =>
      dirichlet_L_character_endpoint_principal_abs_eulerFactor_pos p
        (Nat.prime_of_mem_primesBelow hp)
  have hN_pos : 0 < N := by
    dsimp [N]
    positivity
  have hlogN_nonneg : 0 ≤ Real.log N := by
    dsimp [N]
    exact Real.log_nonneg
      (by exact_mod_cast (Nat.succ_le_succ (Nat.zero_le M) : 1 ≤ M + 1))
  have hS_small_norm :
      ‖S‖ ≤ (1 / 2 : ℝ) * ‖Real.log N‖ := by
    simpa [S, N] using hlog_smallM
  have hS_le : S ≤ (1 / 2 : ℝ) * Real.log N := by
    have hS_le_norm : S ≤ ‖S‖ := by
      simpa [Real.norm_eq_abs] using le_abs_self S
    calc
      S ≤ ‖S‖ := hS_le_norm
      _ ≤ (1 / 2 : ℝ) * ‖Real.log N‖ := hS_small_norm
      _ = (1 / 2 : ℝ) * Real.log N := by
        simp [Real.norm_eq_abs, abs_of_nonneg hlogN_nonneg]
  have hlogP_eq : Real.log P = S := by
    simpa [P, S] using
      dirichlet_L_character_endpoint_principal_abs_prefix_log_eq_sum M
  have hP_le_sqrt : P ≤ Real.sqrt N := by
    have hsqrt_pos : 0 < Real.sqrt N := Real.sqrt_pos.mpr hN_pos
    have hlog_sqrt : Real.log (Real.sqrt N) = (1 / 2 : ℝ) * Real.log N := by
      rw [Real.log_sqrt (le_of_lt hN_pos)]
      ring
    have hlogP_le_sqrt : Real.log P ≤ Real.log (Real.sqrt N) := by
      rw [hlogP_eq, hlog_sqrt]
      exact hS_le
    exact (Real.log_le_log_iff hP_pos hsqrt_pos).mp hlogP_le_sqrt
  have hsqrt_le_cN : Real.sqrt N ≤ c * N := by
    calc
      Real.sqrt N = 1 * Real.sqrt N := by ring
      _ ≤ (c * Real.sqrt N) * Real.sqrt N := by
        exact mul_le_mul_of_nonneg_right hsqrt_largeM (Real.sqrt_nonneg N)
      _ = c * N := by
        have hsq : Real.sqrt N * Real.sqrt N = N := by
          rw [← pow_two, Real.sq_sqrt (le_of_lt hN_pos)]
        calc
          (c * Real.sqrt N) * Real.sqrt N = c * (Real.sqrt N * Real.sqrt N) := by
            ring
          _ = c * N := by rw [hsq]
  have hP_norm : ‖P‖ = P := by
    simp [Real.norm_eq_abs, abs_of_nonneg hP_nonneg]
  have hcalc :
      ‖P‖ ≤ c * ‖(M + 1 : ℝ)‖ := by
    calc
      ‖P‖ = P := hP_norm
      _ ≤ Real.sqrt N := hP_le_sqrt
      _ ≤ c * N := hsqrt_le_cN
      _ = c * ‖(M + 1 : ℝ)‖ := by
        simp [N, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ (M + 1 : ℝ))]
  simpa [P] using hcalc

/-- A direct Chebyshev/Abel route to the principal endpoint-prefix estimate:
it is enough to show that the principal absolute Euler prefix is `o(M)`.  This
is the exact analytic shape needed to bypass the reciprocal-prime Mertens
source in the quadratic-remainder branch. -/
lemma dirichlet_L_character_endpoint_principal_abs_prefix_mul_two_div_nat_succ_tendsto_zero_of_isLittleO
    (hprefix :
      (fun M : ℕ => (M + 1).primesBelow.prod fun p =>
          (1 - (p : ℝ) ^ (-1 : ℝ))⁻¹) =o[Filter.atTop]
        (fun M : ℕ => (M + 1 : ℝ))) :
    ∀ ε : ℝ, ε > 0 → ∃ M₀ : ℕ,
      ∀ M : ℕ, M ≥ M₀ →
        (((M + 1).primesBelow.prod fun p =>
          (1 - (p : ℝ) ^ (-1 : ℝ))⁻¹) + 1) *
        (2 / (M + 1 : ℝ)) < ε := by
  intro ε hε
  have hprefix_bound :
      ∀ᶠ M : ℕ in Filter.atTop,
        ‖((M + 1).primesBelow.prod fun p =>
          (1 - (p : ℝ) ^ (-1 : ℝ))⁻¹)‖ ≤
          (ε / 4) * ‖(M + 1 : ℝ)‖ :=
    hprefix.def (by positivity)
  have hden_tendsto :
      Filter.Tendsto (fun M : ℕ => 2 / (M + 1 : ℝ)) Filter.atTop (nhds 0) := by
    have harg :
        Filter.Tendsto (fun M : ℕ => (M + 1 : ℝ)) Filter.atTop Filter.atTop := by
      simpa [Nat.cast_add, Nat.cast_one] using
        (tendsto_natCast_atTop_atTop.atTop_add (tendsto_const_nhds (x := (1 : ℝ))))
    have hinv :
        Filter.Tendsto (fun M : ℕ => ((M + 1 : ℝ))⁻¹) Filter.atTop (nhds 0) :=
      tendsto_inv_atTop_zero.comp harg
    simpa [div_eq_mul_inv] using (tendsto_const_nhds (x := (2 : ℝ))).mul hinv
  have hden_small :
      ∀ᶠ M : ℕ in Filter.atTop, 2 / (M + 1 : ℝ) < ε / 2 :=
    (tendsto_order.1 hden_tendsto).2 (ε / 2) (by positivity)
  rw [Filter.eventually_atTop] at hprefix_bound hden_small
  rcases hprefix_bound with ⟨M₁, hM₁⟩
  rcases hden_small with ⟨M₂, hM₂⟩
  refine ⟨max M₁ M₂, ?_⟩
  intro M hM
  have hM₁_le : M₁ ≤ M := le_trans (le_max_left M₁ M₂) hM
  have hM₂_le : M₂ ≤ M := le_trans (le_max_right M₁ M₂) hM
  let P : ℝ := (M + 1).primesBelow.prod fun p =>
    (1 - (p : ℝ) ^ (-1 : ℝ))⁻¹
  have hP_nonneg : 0 ≤ P := by
    exact Finset.prod_nonneg fun p hp =>
      le_of_lt <|
        dirichlet_L_character_endpoint_principal_abs_eulerFactor_pos p
          (Nat.prime_of_mem_primesBelow hp)
  have hden_pos : 0 < (M + 1 : ℝ) := by positivity
  have htwo_div_nonneg : 0 ≤ 2 / (M + 1 : ℝ) := by positivity
  have hP_bound : P ≤ (ε / 4) * (M + 1 : ℝ) := by
    have h := hM₁ M hM₁_le
    change ‖P‖ ≤ (ε / 4) * ‖(M + 1 : ℝ)‖ at h
    have hP_le_norm : P ≤ ‖P‖ := by
      simpa [Real.norm_eq_abs] using le_abs_self P
    have hden_norm : ‖(M + 1 : ℝ)‖ = (M + 1 : ℝ) := by
      simp [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ (M + 1 : ℝ))]
    exact le_trans hP_le_norm (by simpa [hden_norm] using h)
  have hP_scaled : P * (2 / (M + 1 : ℝ)) ≤ ε / 2 := by
    calc
      P * (2 / (M + 1 : ℝ)) ≤
          ((ε / 4) * (M + 1 : ℝ)) * (2 / (M + 1 : ℝ)) := by
        exact mul_le_mul_of_nonneg_right hP_bound htwo_div_nonneg
      _ = ε / 2 := by
        field_simp [ne_of_gt hden_pos]
        ring
  calc
    (P + 1) * (2 / (M + 1 : ℝ)) =
        P * (2 / (M + 1 : ℝ)) + 2 / (M + 1 : ℝ) := by ring
    _ < ε := by
      linarith [hP_scaled, hM₂ M hM₂_le]

/-- Principal absolute endpoint-prefix growth for the quadratic
logarithm-remainder part of the endpoint Abel passage.  This now follows from
the Chebyshev/Abel `o(M)` prefix estimate. -/
theorem dirichlet_L_character_endpoint_principal_abs_prefix_mul_two_div_nat_succ_tendsto_zero :
    ∀ ε : ℝ, ε > 0 → ∃ M₀ : ℕ,
      ∀ M : ℕ, M ≥ M₀ →
        (((M + 1).primesBelow.prod fun p =>
          (1 - (p : ℝ) ^ (-1 : ℝ))⁻¹) + 1) *
        (2 / (M + 1 : ℝ)) < ε := by
  exact
    dirichlet_L_character_endpoint_principal_abs_prefix_mul_two_div_nat_succ_tendsto_zero_of_isLittleO
      dirichlet_L_character_endpoint_principal_abs_prefix_isLittleO

/-- Narrow endpoint-prefix growth theorem for the quadratic
logarithm-remainder part of the endpoint Abel passage.  The character-dependent
prefix is formally reduced to the principal absolute prefix. -/
theorem dirichlet_L_character_endpoint_prefix_mul_two_div_nat_succ_tendsto_zero
    {m : ℕ} (χ : DirichletCharacter ℂ m) :
    ∀ ε : ℝ, ε > 0 → ∃ M₀ : ℕ,
      ∀ M : ℕ, M ≥ M₀ →
        (‖((M + 1).primesBelow.prod fun p =>
          (1 - χ p * (p : ℂ) ^ (-((1 : ℕ) : ℂ)))⁻¹)‖ + 1) *
        (2 / (M + 1 : ℝ)) < ε := by
  intro ε hε
  rcases
      dirichlet_L_character_endpoint_principal_abs_prefix_mul_two_div_nat_succ_tendsto_zero
        ε hε with
    ⟨M₀, hM₀⟩
  refine ⟨M₀, ?_⟩
  intro M hM
  have hprefix :=
    dirichlet_L_character_endpoint_prefix_norm_le_principal_abs_prefix χ M
  have hsum :
      ‖((M + 1).primesBelow.prod fun p =>
        (1 - χ p * (p : ℂ) ^ (-((1 : ℕ) : ℂ)))⁻¹)‖ + 1 ≤
        ((M + 1).primesBelow.prod fun p =>
          (1 - (p : ℝ) ^ (-1 : ℝ))⁻¹) + 1 := by
    linarith
  have htail_nonneg : 0 ≤ 2 / (M + 1 : ℝ) := by positivity
  exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hsum htail_nonneg) (hM₀ M hM)

/-- The previous prefix-scaled canonical natural-tail source is formal from
the narrower endpoint-prefix growth source and the explicit complementary
natural `n^{-2}` tail bound. -/
theorem dirichlet_L_character_endpoint_prefix_scaled_nat_inv_sq_tail
    {m : ℕ} (χ : DirichletCharacter ℂ m) :
    ∀ ε : ℝ, ε > 0 → ∃ M₀ : ℕ,
      ∀ M : ℕ, M ≥ M₀ →
        (‖((M + 1).primesBelow.prod fun p =>
          (1 - χ p * (p : ℂ) ^ (-((1 : ℕ) : ℂ)))⁻¹)‖ + 1) *
        (∑' n : {n : ℕ // n ∉ Finset.range (M + 1)}, (n.1 : ℝ) ^ (-2 : ℝ)) < ε := by
  intro ε hε
  rcases
      dirichlet_L_character_endpoint_prefix_mul_two_div_nat_succ_tendsto_zero
        χ ε hε with
    ⟨M₀, hM₀⟩
  refine ⟨M₀, ?_⟩
  intro M hM
  let A : ℝ := ‖((M + 1).primesBelow.prod fun p =>
    (1 - χ p * (p : ℂ) ^ (-((1 : ℕ) : ℂ)))⁻¹)‖ + 1
  let T : ℝ := ∑' n : {n : ℕ // n ∉ Finset.range (M + 1)}, (n.1 : ℝ) ^ (-2 : ℝ)
  have hA_nonneg : 0 ≤ A := by
    dsimp [A]
    positivity
  have hT_le : T ≤ 2 / (M + 1 : ℝ) := by
    simpa [T] using dirichlet_L_character_endpoint_nat_inv_sq_compl_tsum_le M
  exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left hT_le hA_nonneg)
    (by simpa [A] using hM₀ M hM)

/-- Prefix-scaled scalar `p^{-2}` tail estimate for finite prime cutoffs,
derived from the narrower canonical natural-complement-tail source. -/
theorem dirichlet_L_character_endpoint_prefix_scaled_prime_inv_sq_tail
    {m : ℕ} (χ : DirichletCharacter ℂ m) :
    ∀ ε : ℝ, ε > 0 → ∃ M₀ : ℕ,
      ∀ M : ℕ, M ≥ M₀ →
        ∀ K : ℕ, K ≥ M →
        (‖((M + 1).primesBelow.prod fun p =>
          (1 - χ p * (p : ℂ) ^ (-((1 : ℕ) : ℂ)))⁻¹)‖ + 1) *
        (((K + 1).primesBelow \ (M + 1).primesBelow).sum fun p =>
          (p : ℝ) ^ (-2 : ℝ)) < ε := by
  intro ε hε
  rcases
      dirichlet_L_character_endpoint_prefix_scaled_nat_inv_sq_tail χ ε hε with
    ⟨M₀, hM₀⟩
  refine ⟨M₀, ?_⟩
  intro M hM K _hK
  let A : ℝ := ‖((M + 1).primesBelow.prod fun p =>
    (1 - χ p * (p : ℂ) ^ (-((1 : ℕ) : ℂ)))⁻¹)‖ + 1
  let T : ℝ := ((K + 1).primesBelow \ (M + 1).primesBelow).sum fun p =>
    (p : ℝ) ^ (-2 : ℝ)
  let U : ℝ := ∑' n : {n : ℕ // n ∉ Finset.range (M + 1)}, (n.1 : ℝ) ^ (-2 : ℝ)
  have hA_nonneg : 0 ≤ A := by
    dsimp [A]
    positivity
  have hTU : T ≤ U := by
    simpa [T, U] using
      dirichlet_L_character_endpoint_prime_inv_sq_tail_le_nat_compl_tsum M K
  exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left hTU hA_nonneg)
    (by simpa [A, U] using hM₀ M hM)

/-- The previous scalar `p^{-2}` tail interface is formal cutoff
bookkeeping from the prefix-scaled tail estimate. -/
theorem dirichlet_L_character_endpoint_prime_inv_sq_tail
    {m : ℕ} (χ : DirichletCharacter ℂ m) :
    ∀ ε : ℝ, ε > 0 → ∃ M₀ : ℕ,
      ∀ M : ℕ, M ≥ M₀ →
        ∀ K : ℕ, K ≥ M →
        (((K + 1).primesBelow \ (M + 1).primesBelow).sum fun p =>
          (p : ℝ) ^ (-2 : ℝ)) <
          (min 1
            ((ε /
              (‖((M + 1).primesBelow.prod fun p =>
                (1 - χ p * (p : ℂ) ^ (-((1 : ℕ) : ℂ)))⁻¹)‖ + 1)) / 2)) / 2 := by
  intro ε hε
  have hδpos : 0 < min (ε / 4) (1 / 2 : ℝ) := by
    exact lt_min (by positivity) (by norm_num)
  rcases
      dirichlet_L_character_endpoint_prefix_scaled_prime_inv_sq_tail
        χ (min (ε / 4) (1 / 2 : ℝ)) hδpos with
    ⟨M₀, hM₀⟩
  refine ⟨M₀, ?_⟩
  intro M hM K hK
  let A : ℝ := ‖((M + 1).primesBelow.prod fun p =>
    (1 - χ p * (p : ℂ) ^ (-((1 : ℕ) : ℂ)))⁻¹)‖ + 1
  let T : ℝ := ((K + 1).primesBelow \ (M + 1).primesBelow).sum fun p =>
    (p : ℝ) ^ (-2 : ℝ)
  have hscaled : A * T < min (ε / 4) (1 / 2 : ℝ) := by
    simpa [A, T] using hM₀ M hM K hK
  have hApos : 0 < A := by
    dsimp [A]
    positivity
  have hAle : 1 ≤ A := by
    dsimp [A]
    nlinarith [norm_nonneg ((M + 1).primesBelow.prod fun p =>
      (1 - χ p * (p : ℂ) ^ (-((1 : ℕ) : ℂ)))⁻¹)]
  have hTnonneg : 0 ≤ T := by
    dsimp [T]
    exact Finset.sum_nonneg fun p hp => Real.rpow_nonneg (Nat.cast_nonneg p) _
  have hscaled_eps : A * T < ε / 4 :=
    lt_of_lt_of_le hscaled (min_le_left _ _)
  have hT_eps : T < ε / (4 * A) := by
    rw [lt_div_iff₀ (by positivity : 0 < 4 * A)]
    nlinarith
  have hscaled_half : A * T < (1 / 2 : ℝ) :=
    lt_of_lt_of_le hscaled (min_le_right _ _)
  have hT_half : T < (1 / 2 : ℝ) := by
    have hT_le_scaled : T ≤ A * T := by
      nlinarith
    exact lt_of_le_of_lt hT_le_scaled hscaled_half
  have hT_eps_target : T < ((ε / A) / 2) / 2 := by
    field_simp [hApos.ne']
    nlinarith
  change T < (min 1 ((ε / A) / 2)) / 2
  by_cases hB : (1 : ℝ) ≤ (ε / A) / 2
  · have hmin : min 1 ((ε / A) / 2) = (1 : ℝ) := min_eq_left hB
    simpa [hmin] using hT_half
  · have hBlt : (ε / A) / 2 < (1 : ℝ) := not_le.mp hB
    have hmin : min 1 ((ε / A) / 2) = (ε / A) / 2 :=
      min_eq_right hBlt.le
    simpa [hmin] using hT_eps_target

/-- Quadratic-remainder endpoint source, now reduced to the scalar `p^{-2}`
prime-tail estimate by the endpoint-region logarithm-remainder
majorant.  Near `s = 1+`, after subtracting the first-order term from each
finite logarithmic Euler factor, the remaining finite tail is locally uniformly
small. -/
theorem dirichlet_L_character_endpoint_halfplane_eulerLog_quadratic_tail
    {m : ℕ} (χ : DirichletCharacter ℂ m) :
    ∀ ε : ℝ, ε > 0 → ∃ M₀ : ℕ,
      ∀ M : ℕ, M ≥ M₀ →
        ∀ᶠ (x : ℝ) in nhdsWithin (1 : ℝ) (Set.Ioi (1 : ℝ)),
        ∀ K : ℕ, K ≥ M →
        dist
          (((K + 1).primesBelow \ (M + 1).primesBelow).sum fun p =>
            -Complex.log (1 - χ p * (p : ℂ) ^ (-(x : ℂ))) -
              χ p * (p : ℂ) ^ (-(x : ℂ)))
          0 <
          (min 1
            ((ε /
              (‖((M + 1).primesBelow.prod fun p =>
                (1 - χ p * (p : ℂ) ^ (-((1 : ℕ) : ℂ)))⁻¹)‖ + 1)) / 2)) / 2 := by
  intro ε hε
  rcases dirichlet_L_character_endpoint_prime_inv_sq_tail χ ε hε with
    ⟨M₀, hM₀⟩
  refine ⟨M₀, ?_⟩
  intro M hM
  filter_upwards [self_mem_nhdsWithin] with x hx
  intro K hK
  let S : Finset ℕ := (K + 1).primesBelow \ (M + 1).primesBelow
  let R : ℕ → ℂ := fun p =>
    -Complex.log (1 - χ p * (p : ℂ) ^ (-(x : ℂ))) -
      χ p * (p : ℂ) ^ (-(x : ℂ))
  have hxle : (1 : ℝ) ≤ x := le_of_lt hx
  have hnorm :
      ‖S.sum R‖ ≤ S.sum (fun p => (p : ℝ) ^ (-2 : ℝ)) := by
    calc
      ‖S.sum R‖ ≤ S.sum (fun p => ‖R p‖) := norm_sum_le S R
      _ ≤ S.sum (fun p => (p : ℝ) ^ (-2 : ℝ)) := by
        refine Finset.sum_le_sum ?_
        intro p hp
        have hpPrime : p.Prime :=
          Nat.prime_of_mem_primesBelow (Finset.mem_sdiff.mp hp).1
        simpa [R] using
          dirichlet_L_character_endpointRegion_eulerLog_sub_linear_norm_le_inv_sq
            χ hxle p hpPrime
  have htail := hM₀ M hM K hK
  rw [dist_eq_norm]
  simp only [sub_zero]
  exact lt_of_le_of_lt (by simpa [S, R] using hnorm) htail

/-- Narrow analytic step for the endpoint Abel passage in logarithmic
form, derived from the separated first-order prime-character tail and the
quadratic Taylor-remainder tail.  Near `s = 1+`, the finite Dirichlet Euler
logarithmic tail from cutoff `M` to cutoff `K` is locally uniformly close to
`0`.  The large-cutoff bound is independent of the endpoint exponent, while
the endpoint neighborhood may depend on the fixed cutoff `M`. -/
theorem dirichlet_L_nontrivial_character_endpoint_halfplane_eulerLog_tail
    {m : ℕ} [NeZero m] (χ : DirichletCharacter ℂ m) (hχ : χ ≠ 1)
    (hquad : χ ^ 2 = 1) :
    ∀ ε : ℝ, ε > 0 → ∃ M₀ : ℕ,
      ∀ M : ℕ, M ≥ M₀ →
        ∀ᶠ (x : ℝ) in nhdsWithin (1 : ℝ) (Set.Ioi (1 : ℝ)),
        ∀ K : ℕ, K ≥ M →
        dist
          (((K + 1).primesBelow \ (M + 1).primesBelow).sum fun p =>
            -Complex.log (1 - χ p * (p : ℂ) ^ (-(x : ℂ))))
          0 <
          min 1
            ((ε /
              (‖((M + 1).primesBelow.prod fun p =>
                (1 - χ p * (p : ℂ) ^ (-((1 : ℕ) : ℂ)))⁻¹)‖ + 1)) / 2) := by
  intro ε hε
  rcases
      dirichlet_L_nontrivial_character_endpoint_halfplane_firstOrder_tail
        χ hχ hquad ε hε with
    ⟨M₁, hM₁⟩
  rcases
      dirichlet_L_character_endpoint_halfplane_eulerLog_quadratic_tail
        χ ε hε with
    ⟨M₂, hM₂⟩
  refine ⟨max M₁ M₂, ?_⟩
  intro M hM
  have hM₁le : M ≥ M₁ := le_trans (le_max_left _ _) hM
  have hM₂le : M ≥ M₂ := le_trans (le_max_right _ _) hM
  filter_upwards [hM₁ M hM₁le, hM₂ M hM₂le] with x hxLinear hxQuadratic
  intro K hK
  let S : Finset ℕ := (K + 1).primesBelow \ (M + 1).primesBelow
  let A : ℂ := S.sum fun p => χ p * (p : ℂ) ^ (-(x : ℂ))
  let R : ℂ := S.sum fun p =>
    -Complex.log (1 - χ p * (p : ℂ) ^ (-(x : ℂ))) -
      χ p * (p : ℂ) ^ (-(x : ℂ))
  let δ : ℝ :=
    min 1
      ((ε /
        (‖((M + 1).primesBelow.prod fun p =>
          (1 - χ p * (p : ℂ) ^ (-((1 : ℕ) : ℂ)))⁻¹)‖ + 1)) / 2)
  have hδpos : 0 < δ := by
    dsimp [δ]
    positivity
  have hLinear : dist A 0 < δ / 2 := by
    simpa [S, A, δ] using hxLinear K hK
  have hQuadratic : dist R 0 < δ / 2 := by
    simpa [S, R, δ] using hxQuadratic K hK
  have hsum :
      (S.sum fun p => -Complex.log (1 - χ p * (p : ℂ) ^ (-(x : ℂ)))) =
        A + R := by
    dsimp [A, R]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro p hp
    ring
  rw [show
      (((K + 1).primesBelow \ (M + 1).primesBelow).sum fun p =>
        -Complex.log (1 - χ p * (p : ℂ) ^ (-(x : ℂ)))) = A + R by
      simpa [S] using hsum]
  rw [dist_eq_norm] at hLinear hQuadratic ⊢
  simp only [sub_zero] at hLinear hQuadratic ⊢
  calc
    ‖A + R‖ ≤ ‖A‖ + ‖R‖ := norm_add_le A R
    _ < δ / 2 + δ / 2 := by
      exact add_lt_add hLinear hQuadratic
    _ = δ := by ring

/-- Product-tail form of the endpoint Abel step, derived from the
narrower logarithmic tail source using finite `exp(sum log)` bookkeeping.  Near
`s = 1+`, the finite Dirichlet Euler tail from cutoff `M` to cutoff `K` is
locally uniformly close to `1`.  The scale divides by the endpoint norm of the
fixed prefix because Lean separately bounds that prefix near the endpoint and
then multiplies the tail estimate back into the full-product Cauchy statement.
The large-cutoff bound is independent of the endpoint exponent, while the
endpoint neighborhood may depend on the fixed cutoff `M`. -/
theorem dirichlet_L_nontrivial_character_endpoint_halfplane_eulerProduct_tail_ratio
    {m : ℕ} [NeZero m] (χ : DirichletCharacter ℂ m) (hχ : χ ≠ 1)
    (hquad : χ ^ 2 = 1) :
    ∀ ε : ℝ, ε > 0 → ∃ M₀ : ℕ,
      ∀ M : ℕ, M ≥ M₀ →
        ∀ᶠ (x : ℝ) in nhdsWithin (1 : ℝ) (Set.Ioi (1 : ℝ)),
        ∀ K : ℕ, K ≥ M →
        dist
          (((K + 1).primesBelow \ (M + 1).primesBelow).prod fun p =>
            (1 - χ p * (p : ℂ) ^ (-(x : ℂ)))⁻¹)
          1 <
          ε /
            (‖((M + 1).primesBelow.prod fun p =>
              (1 - χ p * (p : ℂ) ^ (-((1 : ℕ) : ℂ)))⁻¹)‖ + 1) := by
  intro ε hε
  rcases
      dirichlet_L_nontrivial_character_endpoint_halfplane_eulerLog_tail
        χ hχ hquad ε hε with
    ⟨M₀, hM₀⟩
  refine ⟨M₀, ?_⟩
  intro M hM
  filter_upwards [hM₀ M hM, self_mem_nhdsWithin] with x hxLog hx
  intro K hK
  let S : Finset ℕ := (K + 1).primesBelow \ (M + 1).primesBelow
  let Z : ℂ := S.sum fun p =>
    -Complex.log (1 - χ p * (p : ℂ) ^ (-(x : ℂ)))
  let η : ℝ :=
    ε /
      (‖((M + 1).primesBelow.prod fun p =>
        (1 - χ p * (p : ℂ) ^ (-((1 : ℕ) : ℂ)))⁻¹)‖ + 1)
  have hη : 0 < η := by
    dsimp [η]
    positivity
  have hZlt : ‖Z‖ < min 1 (η / 2) := by
    simpa [S, Z, η, dist_eq_norm] using hxLog K hK
  have hZle_one : ‖Z‖ ≤ 1 :=
    (le_of_lt hZlt).trans (min_le_left _ _)
  have hZlt_half : ‖Z‖ < η / 2 :=
    hZlt.trans_le (min_le_right _ _)
  have hExp :
      S.prod (fun p => (1 - χ p * (p : ℂ) ^ (-(x : ℂ)))⁻¹) =
        Complex.exp Z := by
    dsimp [Z]
    rw [Complex.exp_sum]
    refine Finset.prod_congr rfl ?_
    intro p hp
    have hpPrime : p.Prime :=
      Nat.prime_of_mem_primesBelow (Finset.mem_sdiff.mp hp).1
    have hden :
        1 - χ p * (p : ℂ) ^ (-(x : ℂ)) ≠ 0 :=
      dirichlet_L_character_endpointRegion_eulerDenominator_ne_zero
        χ hx.le p hpPrime
    simp [Complex.exp_neg, Complex.exp_log hden]
  calc
    dist
        (((K + 1).primesBelow \ (M + 1).primesBelow).prod fun p =>
          (1 - χ p * (p : ℂ) ^ (-(x : ℂ)))⁻¹)
        1 = ‖Complex.exp Z - 1‖ := by
          rw [dist_eq_norm]
          simp [S, hExp]
    _ ≤ 2 * ‖Z‖ := Complex.norm_exp_sub_one_le hZle_one
    _ < η := by linarith

/-- Analytic step for the endpoint Abel passage,
derived from the product-tail theorem plus finite-prefix
boundedness and finite-product splitting.  Near `s = 1+`, the finite
Dirichlet Euler products are locally uniformly Cauchy in the prime cutoff.
The large-cutoff bound is independent of the endpoint exponent, but the
endpoint neighborhood may depend on the fixed cutoff `M`. -/
theorem dirichlet_L_nontrivial_character_endpoint_halfplane_uniform_eulerProduct_cauchy_tail
    {m : ℕ} [NeZero m] (χ : DirichletCharacter ℂ m) (hχ : χ ≠ 1)
    (hquad : χ ^ 2 = 1) :
    ∀ ε : ℝ, ε > 0 → ∃ M₀ : ℕ,
      ∀ M : ℕ, M ≥ M₀ →
        ∀ᶠ (x : ℝ) in nhdsWithin (1 : ℝ) (Set.Ioi (1 : ℝ)),
        ∀ K : ℕ, K ≥ M →
        dist
          ((M + 1).primesBelow.prod fun p =>
            (1 - χ p * (p : ℂ) ^ (-(x : ℂ)))⁻¹)
          ((K + 1).primesBelow.prod fun p =>
            (1 - χ p * (p : ℂ) ^ (-(x : ℂ)))⁻¹) < ε
    := by
  intro ε hε
  rcases
      dirichlet_L_nontrivial_character_endpoint_halfplane_eulerProduct_tail_ratio
        χ hχ hquad ε hε with
    ⟨M₀, hM₀⟩
  refine ⟨M₀, ?_⟩
  intro M hM
  let P : ℝ → ℂ := fun x =>
    (M + 1).primesBelow.prod fun p =>
      (1 - χ p * (p : ℂ) ^ (-(x : ℂ)))⁻¹
  let E : ℂ :=
    (M + 1).primesBelow.prod fun p =>
      (1 - χ p * (p : ℂ) ^ (-((1 : ℕ) : ℂ)))⁻¹
  have hCpos : 0 < ‖E‖ + 1 := by positivity
  have hprefix :
      ∀ᶠ (x : ℝ) in nhdsWithin (1 : ℝ) (Set.Ioi (1 : ℝ)),
        ‖P x‖ < ‖E‖ + 1 := by
    have hlim : Filter.Tendsto P (nhdsWithin (1 : ℝ) (Set.Ioi (1 : ℝ))) (nhds E) := by
      simpa [P, E] using dirichlet_L_character_finiteEulerProduct_tendsto_endpoint χ M
    have hdist :
        ∀ᶠ (x : ℝ) in nhdsWithin (1 : ℝ) (Set.Ioi (1 : ℝ)),
          dist (P x) E < 1 :=
      (Metric.tendsto_nhds.mp hlim) 1 zero_lt_one
    filter_upwards [hdist] with x hx
    calc
      ‖P x‖ = dist (P x) 0 := by rw [dist_zero_right]
      _ ≤ dist (P x) E + dist E 0 := dist_triangle _ _ _
      _ = dist (P x) E + ‖E‖ := by rw [dist_zero_right]
      _ < 1 + ‖E‖ := by simpa [add_comm] using add_lt_add_right hx ‖E‖
      _ = ‖E‖ + 1 := by ring
  filter_upwards [hprefix, hM₀ M hM] with x hxPrefix hxTail
  intro K hK
  let PM : ℂ :=
    (M + 1).primesBelow.prod fun p =>
      (1 - χ p * (p : ℂ) ^ (-(x : ℂ)))⁻¹
  let T : ℂ :=
    ((K + 1).primesBelow \ (M + 1).primesBelow).prod fun p =>
      (1 - χ p * (p : ℂ) ^ (-(x : ℂ)))⁻¹
  have hsubset :
      (M + 1).primesBelow ⊆ (K + 1).primesBelow := by
    intro p hp
    rw [Nat.mem_primesBelow] at hp ⊢
    exact ⟨lt_of_lt_of_le hp.1 (Nat.succ_le_succ hK), hp.2⟩
  have hKprod :
      ((K + 1).primesBelow.prod fun p =>
        (1 - χ p * (p : ℂ) ^ (-(x : ℂ)))⁻¹) = T * PM := by
    dsimp [T, PM]
    rw [← Finset.prod_sdiff hsubset]
  have htail : dist T 1 < ε / (‖E‖ + 1) := by
    simpa [T, E] using hxTail K hK
  have hdist_eq :
      dist PM (T * PM) = ‖PM‖ * dist T 1 := by
    rw [dist_eq_norm, dist_eq_norm]
    have hfactor : PM - T * PM = PM * (1 - T) := by ring
    rw [hfactor, norm_mul]
    congr 1
    rw [← norm_neg (T - 1)]
    ring_nf
  have hmul : ‖PM‖ * dist T 1 < (‖E‖ + 1) * (ε / (‖E‖ + 1)) := by
    have hle : ‖PM‖ * dist T 1 ≤ (‖E‖ + 1) * dist T 1 :=
      mul_le_mul_of_nonneg_right (le_of_lt hxPrefix) dist_nonneg
    have hlt : (‖E‖ + 1) * dist T 1 <
        (‖E‖ + 1) * (ε / (‖E‖ + 1)) :=
      mul_lt_mul_of_pos_left htail hCpos
    exact lt_of_le_of_lt hle hlt
  calc
    dist
        ((M + 1).primesBelow.prod fun p =>
          (1 - χ p * (p : ℂ) ^ (-(x : ℂ)))⁻¹)
        ((K + 1).primesBelow.prod fun p =>
          (1 - χ p * (p : ℂ) ^ (-(x : ℂ)))⁻¹)
        = dist PM (T * PM) := by simp [PM, hKprod]
    _ = ‖PM‖ * dist T 1 := hdist_eq
    _ < (‖E‖ + 1) * (ε / (‖E‖ + 1)) := hmul
    _ = ε := by field_simp [hCpos.ne']

/-- The uniform tail estimate against the half-plane infinite product,
derived from the locally uniform Cauchy-tail estimate and Mathlib's pointwise
half-plane Euler product. -/
lemma dirichlet_L_nontrivial_character_endpoint_halfplane_uniform_eulerProduct_tail
    {m : ℕ} [NeZero m] (χ : DirichletCharacter ℂ m) (hχ : χ ≠ 1)
    (hquad : χ ^ 2 = 1) :
    ∀ ε : ℝ, ε > 0 → ∃ M₀ : ℕ,
      ∀ M : ℕ, M ≥ M₀ →
        ∀ᶠ (x : ℝ) in nhdsWithin (1 : ℝ) (Set.Ioi (1 : ℝ)),
        dist
          ((M + 1).primesBelow.prod fun p =>
            (1 - χ p * (p : ℂ) ^ (-(x : ℂ)))⁻¹)
          (∏' p : Nat.Primes,
            (1 - χ p * (p : ℂ) ^ (-(x : ℂ)))⁻¹) < ε := by
  intro ε hε
  have hhalf : 0 < ε / 2 := by positivity
  rcases
      dirichlet_L_nontrivial_character_endpoint_halfplane_uniform_eulerProduct_cauchy_tail
        χ hχ hquad (ε / 2) hhalf with
    ⟨M₀, hM₀⟩
  refine ⟨M₀, ?_⟩
  intro M hM
  filter_upwards [hM₀ M hM, self_mem_nhdsWithin] with x hxCauchy hx
  have hxProd :
      Filter.Tendsto
        (fun K : ℕ => (K + 1).primesBelow.prod fun p =>
          (1 - χ p * (p : ℂ) ^ (-(x : ℂ)))⁻¹)
        Filter.atTop
        (nhds (∏' p : Nat.Primes,
          (1 - χ p * (p : ℂ) ^ (-(x : ℂ)))⁻¹)) :=
    dirichlet_L_character_halfplane_complexEulerProduct_tendsto_tprod χ hx
  have hnear :
      ∀ᶠ K : ℕ in Filter.atTop,
        dist
          ((K + 1).primesBelow.prod fun p =>
            (1 - χ p * (p : ℂ) ^ (-(x : ℂ)))⁻¹)
          (∏' p : Nat.Primes,
            (1 - χ p * (p : ℂ) ^ (-(x : ℂ)))⁻¹) < ε / 2 :=
    (Metric.tendsto_nhds.mp hxProd) (ε / 2) hhalf
  rcases (hnear.and (Filter.eventually_ge_atTop M)).exists with ⟨K, hKnear, hKM⟩
  have hMK := hxCauchy K hKM
  calc
    dist
        ((M + 1).primesBelow.prod fun p =>
          (1 - χ p * (p : ℂ) ^ (-(x : ℂ)))⁻¹)
        (∏' p : Nat.Primes,
          (1 - χ p * (p : ℂ) ^ (-(x : ℂ)))⁻¹)
        ≤
      dist
        ((M + 1).primesBelow.prod fun p =>
          (1 - χ p * (p : ℂ) ^ (-(x : ℂ)))⁻¹)
        ((K + 1).primesBelow.prod fun p =>
          (1 - χ p * (p : ℂ) ^ (-(x : ℂ)))⁻¹) +
      dist
        ((K + 1).primesBelow.prod fun p =>
          (1 - χ p * (p : ℂ) ^ (-(x : ℂ)))⁻¹)
        (∏' p : Nat.Primes,
          (1 - χ p * (p : ℂ) ^ (-(x : ℂ)))⁻¹) := by
          exact dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := by
          gcongr
    _ = ε := by ring

/-- The source-facing uniform tail statement in `LSeries` form follows from the
narrower uniform convergence to the half-plane infinite Euler product plus
Mathlib's half-plane Dirichlet Euler product theorem. -/
lemma dirichlet_L_nontrivial_character_endpoint_halfplane_uniform_tail
    {m : ℕ} [NeZero m] (χ : DirichletCharacter ℂ m) (hχ : χ ≠ 1)
    (hquad : χ ^ 2 = 1) :
    ∀ ε : ℝ, ε > 0 → ∃ M₀ : ℕ, ∀ M : ℕ, M ≥ M₀ →
      ∀ᶠ (x : ℝ) in nhdsWithin (1 : ℝ) (Set.Ioi (1 : ℝ)),
        dist
          ((M + 1).primesBelow.prod fun p =>
            (1 - χ p * (p : ℂ) ^ (-(x : ℂ)))⁻¹)
          (LSeries (fun n => χ n) (x : ℂ)) < ε
    := by
  intro ε hε
  rcases
      dirichlet_L_nontrivial_character_endpoint_halfplane_uniform_eulerProduct_tail
        χ hχ hquad ε hε with
    ⟨M₀, hM₀⟩
  refine ⟨M₀, ?_⟩
  intro M hM
  filter_upwards [hM₀ M hM, self_mem_nhdsWithin] with x hxTail hx
  have hxre : 1 < (x : ℂ).re := by
    simpa using hx
  have htprod :
      (∏' p : Nat.Primes,
          (1 - χ p * (p : ℂ) ^ (-(x : ℂ)))⁻¹) =
        LSeries (fun n => χ n) (x : ℂ) :=
    DirichletCharacter.LSeries_eulerProduct_tprod χ hxre
  simpa [htprod] using hxTail

/-- Standard uncut nontrivial Dirichlet-character Euler product at the endpoint
`s = 1`, in Mathlib's `Nat.primesBelow` cutoff notation.  It is derived from
the Abel/uniform tail estimate together with the half-plane boundary-value and
fixed finite-product endpoint-continuity lemmas. -/
lemma dirichlet_L_nontrivial_character_endpoint_complexEulerProduct_tendsto
    {m : ℕ} [NeZero m] (χ : DirichletCharacter ℂ m) (hχ : χ ≠ 1)
    (hquad : χ ^ 2 = 1) :
    Filter.Tendsto
      (fun M : ℕ => (M + 1).primesBelow.prod fun p =>
        (1 - χ p * (p : ℂ) ^ (-((1 : ℕ) : ℂ)))⁻¹)
      Filter.atTop
      (nhds (DirichletCharacter.LFunction χ 1)) := by
  refine tendsto_endpoint_of_eventually_uniform_halfplane_tail
    (P := fun M x => (M + 1).primesBelow.prod fun p =>
      (1 - χ p * (p : ℂ) ^ (-(x : ℂ)))⁻¹)
    (E := fun M => (M + 1).primesBelow.prod fun p =>
      (1 - χ p * (p : ℂ) ^ (-((1 : ℕ) : ℂ)))⁻¹)
    (F := fun x => LSeries (fun n => χ n) (x : ℂ))
    (y := DirichletCharacter.LFunction χ 1) ?_ ?_ ?_
  · intro M
    simpa using dirichlet_L_character_finiteEulerProduct_tendsto_endpoint χ M
  · simpa using dirichlet_L_nontrivial_character_LSeries_tendsto_LFunction_one χ hχ
  · exact dirichlet_L_nontrivial_character_endpoint_halfplane_uniform_tail
      χ hχ hquad

/-- The cutoff-tail endpoint theorem used downstream, derived from the
standard uncut nontrivial Dirichlet-character Euler product by finite cutoff
cancellation. -/
theorem dirichlet_L_nontrivial_character_endpoint_complexTail_tendsto
    {m : ℕ} [NeZero m] (χ : DirichletCharacter ℂ m) (N : ℕ) (hχ : χ ≠ 1)
    (hquad : χ ^ 2 = 1) :
    Filter.Tendsto
      (fun M : ℕ => ((M + 1).primesBelow \ (N + 1).primesBelow).prod fun p =>
        (1 - χ p * (p : ℂ) ^ (-((1 : ℕ) : ℂ)))⁻¹)
      Filter.atTop
      (nhds (DirichletCharacter.LFunction χ 1 /
        ((N + 1).primesBelow.prod fun p =>
          (1 - χ p * (p : ℂ) ^ (-((1 : ℕ) : ℂ)))⁻¹))) := by
  have hzN :
      ((N + 1).primesBelow.prod fun p =>
        (1 - χ p * (p : ℂ) ^ (-((1 : ℕ) : ℂ)))⁻¹) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr ?_
    intro p hp
    exact dirichlet_L_nontrivial_character_endpoint_eulerFactor_ne_zero
      χ p (Nat.prime_of_mem_primesBelow hp)
  have hχprod :=
    (dirichlet_L_nontrivial_character_endpoint_complexEulerProduct_tendsto
      χ hχ hquad).div_const
      ((N + 1).primesBelow.prod fun p =>
        (1 - χ p * (p : ℂ) ^ (-((1 : ℕ) : ℂ)))⁻¹)
  refine Filter.Tendsto.congr' ?_ hχprod
  filter_upwards [Filter.eventually_ge_atTop N] with M hNM
  have hsubset :
      (N + 1).primesBelow ⊆ (M + 1).primesBelow := by
    intro p hp
    rw [Nat.mem_primesBelow] at hp ⊢
    exact ⟨lt_of_lt_of_le hp.1 (Nat.succ_le_succ hNM), hp.2⟩
  calc
    ((M + 1).primesBelow.prod fun p =>
        (1 - χ p * (p : ℂ) ^ (-((1 : ℕ) : ℂ)))⁻¹) /
        ((N + 1).primesBelow.prod fun p =>
          (1 - χ p * (p : ℂ) ^ (-((1 : ℕ) : ℂ)))⁻¹)
        =
      (((M + 1).primesBelow \ (N + 1).primesBelow).prod fun p =>
          (1 - χ p * (p : ℂ) ^ (-((1 : ℕ) : ℂ)))⁻¹) *
        ((N + 1).primesBelow.prod fun p =>
          (1 - χ p * (p : ℂ) ^ (-((1 : ℕ) : ℂ)))⁻¹) /
        ((N + 1).primesBelow.prod fun p =>
          (1 - χ p * (p : ℂ) ^ (-((1 : ℕ) : ℂ)))⁻¹) := by
          rw [Finset.prod_sdiff hsubset]
    _ =
      ((M + 1).primesBelow \ (N + 1).primesBelow).prod fun p =>
        (1 - χ p * (p : ℂ) ^ (-((1 : ℕ) : ℂ)))⁻¹ := by
          exact mul_div_cancel_right₀ _ hzN

/-- The remaining rank-two endpoint in the Schulze--Pillot notation, derived
from the standard nontrivial Dirichlet-character endpoint source. -/
theorem dirichlet_L_goodPrimeEvenCharacterEndpointComplexTail_tendsto
    (L : PositiveDefiniteIntegralLattice n) (N : ℕ) (_hn : n = 2 * 1)
    (hχ : goodPrimeEvenDirichletCharacter L 1 ≠ 1) :
    Filter.Tendsto
      (fun M : ℕ => ((M + 1).primesBelow \ (N + 1).primesBelow).prod fun p =>
        (1 - goodPrimeEvenDirichletCharacter L 1 p *
          (p : ℂ) ^ (-((1 : ℕ) : ℂ)))⁻¹)
      Filter.atTop
      (nhds (goodPrimeEvenCharacterDirichletEndpointComplexTailFactor L N)) := by
  letI : NeZero (goodPrimeEvenDirichletModulus L 1) :=
    ⟨ne_of_gt (goodPrimeEvenDirichletModulus_pos L 1)⟩
  simpa [goodPrimeEvenCharacterDirichletEndpointComplexTailFactor] using
    dirichlet_L_nontrivial_character_endpoint_complexTail_tendsto
      (goodPrimeEvenDirichletCharacter L 1) N hχ
      (goodPrimeEvenDirichletCharacter_sq L 1 _hn)

/-- The rank-two real-valued endpoint theorem used by the compatibility
interface, derived from the narrower complex Dirichlet endpoint source and the
formal Jacobi-symbol-to-Dirichlet finite-product bridge. -/
theorem dirichlet_L_goodPrimeEvenCharacterEndpointInverseProductTendsTo
    (L : PositiveDefiniteIntegralLattice n) (N : ℕ)
    (hB : massBadPrimeSet L ⊆ rationalPrimesUpTo N)
    (hn : n = 2 * 1) :
    goodPrimeEvenCharacterInverseProductTendsTo L N 1
      (goodPrimeEvenCharacterDirichletEndpointTailFactor L N) := by
  unfold goodPrimeEvenCharacterInverseProductTendsTo
  have hcomplex :=
    dirichlet_L_goodPrimeEvenCharacterEndpointComplexTail_tendsto
      (n := n) L N hn
      (goodPrimeEvenDirichletCharacter_ne_one L hn)
  have hreal :
      Filter.Tendsto
        (fun M : ℕ =>
          (((M + 1).primesBelow \ (N + 1).primesBelow).prod fun p =>
            (1 - goodPrimeEvenDirichletCharacter L 1 p *
              (p : ℂ) ^ (-((1 : ℕ) : ℂ)))⁻¹).re)
        Filter.atTop
      (nhds (goodPrimeEvenCharacterDirichletEndpointTailFactor L N)) := by
    change Filter.Tendsto
      (fun M : ℕ =>
        (((M + 1).primesBelow \ (N + 1).primesBelow).prod fun p =>
          (1 - goodPrimeEvenDirichletCharacter L 1 p *
            (p : ℂ) ^ (-((1 : ℕ) : ℂ)))⁻¹).re)
      Filter.atTop
      (nhds (goodPrimeEvenCharacterDirichletEndpointComplexTailFactor L N).re)
    exact Complex.continuous_re.tendsto _ |>.comp hcomplex
  have htail :
      Filter.Tendsto
        (fun M : ℕ =>
          goodPrimeEvenCharacterInverseProduct L
            (rationalPrimesUpTo M \ rationalPrimesUpTo N) 1)
        Filter.atTop
        (nhds (goodPrimeEvenCharacterDirichletEndpointTailFactor L N)) := by
    refine Filter.Tendsto.congr' ?_ hreal
    filter_upwards with M
    have hnotBad :
        ∀ p ∈ rationalPrimesUpTo M \ rationalPrimesUpTo N,
          p ∉ massBadPrimeSet L := by
      intro p hp
      exact fun hpB => (Finset.mem_sdiff.mp hp).2 (hB hpB)
    have hcast :=
      goodPrimeEvenCharacterInverseProduct_ofReal_of_forall_not_mem_bad
        (n := n) L (rationalPrimesUpTo M \ rationalPrimesUpTo N) 1 hnotBad hn
    have hmap :
        ((rationalPrimesUpTo M \ rationalPrimesUpTo N).prod fun p =>
          (1 - goodPrimeEvenDirichletCharacter L 1 p.1 *
            (p.1 : ℂ) ^ (-((1 : ℕ) : ℂ)))⁻¹) =
          (((M + 1).primesBelow \ (N + 1).primesBelow).prod fun p =>
            (1 - goodPrimeEvenDirichletCharacter L 1 p *
              (p : ℂ) ^ (-((1 : ℕ) : ℂ)))⁻¹) := by
      rw [← rationalPrimesUpTo_sdiff_map_val_eq_primesBelow_sdiff N M]
      simp [Finset.prod_map, rationalPrimeValEmbedding]
    have hre := congrArg Complex.re hcast
    rw [Complex.ofReal_re] at hre
    exact (hre.trans (congrArg Complex.re hmap)).symm
  exact htail

/-- Compatibility theorem for the even-rank extra Euler factor.  The only
remaining analytic source input is the endpoint `s = 1`; for `1 < s` this
uses Mathlib's Dirichlet `L`-series Euler product after the finite bad-prime
cutoff. -/
theorem dirichlet_L_goodPrimeEvenCharacterInverseProductTendsTo
    (L : PositiveDefiniteIntegralLattice n) (N s : ℕ)
    (hB : massBadPrimeSet L ⊆ rationalPrimesUpTo N) (hs : 0 < s)
    (hn : n = 2 * s) :
    goodPrimeEvenCharacterInverseProductTendsTo L N s
      (goodPrimeEvenCharacterDirichletTailFactor L N s) := by
  by_cases h1 : s = 1
  · subst s
    simpa [goodPrimeEvenCharacterDirichletTailFactor] using
      dirichlet_L_goodPrimeEvenCharacterEndpointInverseProductTendsTo
        (n := n) L N hB hn
  · have hs_one_lt : 1 < s := by omega
    simpa [goodPrimeEvenCharacterDirichletTailFactor, h1] using
      dirichlet_L_goodPrimeEvenCharacterInverseProductTendsTo_of_one_lt
        (n := n) L N s hB hs_one_lt hn

/-- Convergence predicate for the full even-rank good-prime tail after the
finite bad-prime cutoff has been removed. -/
def goodPrimeEvenEulerInverseProductTendsTo
    (L : PositiveDefiniteIntegralLattice n) (N s : ℕ) (P : ℝ) : Prop :=
  Filter.Tendsto
    (fun M : ℕ =>
      (rationalPrimesUpTo M \ rationalPrimesUpTo N).prod fun p =>
        (goodPrimeEvenEulerFactor L p s)⁻¹)
    Filter.atTop (nhds P)

lemma goodPrimeEvenEulerInverseProductTendsTo_of_core_and_character
    (L : PositiveDefiniteIntegralLattice n) {N s : ℕ} {Pcore Pχ : ℝ}
    (hcore : goodPrimeOddEulerCoreInverseProductTendsTo N s Pcore)
    (hχ : goodPrimeEvenCharacterInverseProductTendsTo L N s Pχ) :
    goodPrimeEvenEulerInverseProductTendsTo L N s (Pcore * Pχ) := by
  unfold goodPrimeEvenEulerInverseProductTendsTo
  unfold goodPrimeOddEulerCoreInverseProductTendsTo at hcore
  unfold goodPrimeEvenCharacterInverseProductTendsTo at hχ
  have hmul := hcore.mul hχ
  refine Filter.Tendsto.congr' ?_ hmul
  filter_upwards with M
  exact
    (goodPrimeEvenEulerProduct_eq_core_mul_characterInverseProduct
      L (rationalPrimesUpTo M \ rationalPrimesUpTo N) s).symm

lemma goodPrimeOddEulerCoreInverseProductTendsTo_of_core
    (N s : ℕ) (P : ℕ → ℝ)
    (hP : ∀ j ∈ Finset.Icc 1 (s - 1),
      goodPrimeEulerCoreInverseProductTendsTo N j (P j)) :
    goodPrimeOddEulerCoreInverseProductTendsTo N s
      ((Finset.Icc 1 (s - 1)).prod P) := by
  unfold goodPrimeOddEulerCoreInverseProductTendsTo
  unfold goodPrimeEulerCoreInverseProductTendsTo at hP
  exact tendsto_finset_prod (Finset.Icc 1 (s - 1)) hP


lemma massPartialPrimeInverseProduct_pos
    (L : PositiveDefiniteIntegralLattice n) (N : ℕ) :
    0 < massPartialPrimeInverseProduct L N := by
  exact massFinitePrimeInverseProduct_pos L (rationalPrimesUpTo N)

lemma massPartialPrimeInverseProduct_eq_of_isSameGenus
    {L₀ L₁ : PositiveDefiniteIntegralLattice n} (h : L₀.IsSameGenus L₁) (N : ℕ) :
    massPartialPrimeInverseProduct L₀ N =
      massPartialPrimeInverseProduct L₁ N := by
  exact massFinitePrimeInverseProduct_eq_of_isSameGenus h
    (rationalPrimesUpTo N)

/-- Once a cutoff contains every bad prime, the partial inverse product splits
as the fixed bad-prime factor times the good-prime classical tail. -/
lemma massPartialPrimeInverseProduct_eq_badPrimeSet_mul_goodPrimeClassical
    (L : PositiveDefiniteIntegralLattice n) (N : ℕ)
    (hB : massBadPrimeSet L ⊆ rationalPrimesUpTo N) :
    massPartialPrimeInverseProduct L N =
      massBadPrimeInverseProduct L *
        massGoodPrimeClassicalInverseProduct L
          (rationalPrimesUpTo N \ massBadPrimeSet L) := by
  exact
    massFinitePrimeInverseProduct_eq_badPrimeSet_mul_goodPrimeClassical
      (n := n) L (rationalPrimesUpTo N) hB

/-- After one cutoff has included all bad primes, increasing the cutoff only
adjoins a classical good-prime tail. -/
lemma massPartialPrimeInverseProduct_eq_mul_goodPrimeClassical_tail_of_le
    (L : PositiveDefiniteIntegralLattice n) {N M : ℕ} (hNM : N ≤ M)
    (hB : massBadPrimeSet L ⊆ rationalPrimesUpTo N) :
    massPartialPrimeInverseProduct L M =
      massPartialPrimeInverseProduct L N *
        massGoodPrimeClassicalInverseProduct L
          (rationalPrimesUpTo M \ rationalPrimesUpTo N) := by
  let S := rationalPrimesUpTo N
  let T := rationalPrimesUpTo M \ rationalPrimesUpTo N
  have hsub : S ⊆ rationalPrimesUpTo M :=
    rationalPrimesUpTo_subset_of_le hNM
  have hunion : S ∪ T = rationalPrimesUpTo M := by
    ext p
    constructor
    · intro hp
      rcases Finset.mem_union.mp hp with hpS | hpT
      · exact hsub hpS
      · exact (Finset.mem_sdiff.mp hpT).1
    · intro hpM
      by_cases hpS : p ∈ S
      · exact Finset.mem_union.mpr (Or.inl hpS)
      · exact Finset.mem_union.mpr (Or.inr (Finset.mem_sdiff.mpr ⟨hpM, hpS⟩))
  have hdisj : Disjoint S T := by
    rw [Finset.disjoint_left]
    intro p hpS hpT
    exact (Finset.mem_sdiff.mp hpT).2 hpS
  have hT : ∀ p ∈ T, p ∉ massBadPrimeSet L := by
    intro p hpT hpB
    exact (Finset.mem_sdiff.mp hpT).2 (hB hpB)
  have hprod :
      massFinitePrimeInverseProduct L (S ∪ T) =
        massFinitePrimeInverseProduct L S *
          massGoodPrimeClassicalInverseProduct L T :=
    massFinitePrimeInverseProduct_union_goodPrimeClassical
      (n := n) L S T hdisj hT
  rw [hunion] at hprod
  simpa [massPartialPrimeInverseProduct, S, T] using hprod

/-! ## First adelic bridge interface -/



/-- Partial product of fixed-`k` inverse local factors over rational primes
`p ≤ N`. -/
def fixedKMassPartialPrimeInverseProduct (L : PositiveDefiniteIntegralLattice n)
    (κ : {p : ℕ // Nat.Prime p} → ℕ)
    (hκ : ∀ p : {p : ℕ // Nat.Prime p},
      @IsLocalDensityAdmissibleExponent n L p.1 (κ p) ⟨p.2⟩)
    (N : ℕ) : ℝ :=
  fixedKMassFinitePrimeInverseProduct L κ hκ
    (rationalPrimesUpTo N)

/-- The fixed-`k` counterpart of
`massLocalInverseProductTendsTo`: cutoff products of chosen
fixed-admissible-exponent local factors converge to `P`.  This route avoids
a `k`-independence hypothesis; the choice of exponents remains visible
in the statement. -/
def fixedKMassLocalInverseProductTendsTo (L : PositiveDefiniteIntegralLattice n)
    (κ : {p : ℕ // Nat.Prime p} → ℕ)
    (hκ : ∀ p : {p : ℕ // Nat.Prime p},
      @IsLocalDensityAdmissibleExponent n L p.1 (κ p) ⟨p.2⟩)
    (P : ℝ) : Prop :=
  Filter.Tendsto
    (fun N : ℕ => fixedKMassPartialPrimeInverseProduct L κ hκ N)
    Filter.atTop (nhds P)

/-- Partial product of one-`k` inverse local factors over rational primes
`p ≤ N`. -/
def oneKMassPartialPrimeInverseProduct
    (L : PositiveDefiniteIntegralLattice n) (N : ℕ) : ℝ :=
  oneKMassFinitePrimeInverseProduct L (rationalPrimesUpTo N)

/-- Cutoff convergence predicate for the one-`k` local product. -/
def oneKMassLocalInverseProductTendsTo
    (L : PositiveDefiniteIntegralLattice n) (P : ℝ) : Prop :=
  Filter.Tendsto
    (fun N : ℕ => oneKMassPartialPrimeInverseProduct L N)
    Filter.atTop (nhds P)

/-- The product side of the ordinary mass formula in Schulze--Pillot's
normalization: the archimedean factor times a limit `P` of the inverse local
density products. -/
def massFormulaProductSide
    (_L : PositiveDefiniteIntegralLattice n) (P : ℝ) : ℝ :=
  archimedeanMassFactor n * P

lemma massFormulaProductSide_pos
    (L : PositiveDefiniteIntegralLattice n) {P : ℝ} (hP : 0 < P) :
    0 < massFormulaProductSide L P := by
  exact mul_pos (archimedeanMassFactor_pos n) hP

end PositiveDefiniteIntegralLattice

end
