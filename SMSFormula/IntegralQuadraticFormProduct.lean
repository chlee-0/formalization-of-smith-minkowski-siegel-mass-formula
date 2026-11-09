import SMSFormula.IntegralQuadraticFormDyadicLocalFactor

/-!
# Direct all-prime products for integral quadratic forms

This module packages the intrinsic odd and dyadic local densities into one
prime-indexed factor.  The definitions below are built from the direct
quadratic form, polar dual, and polar discriminant.  Their comparison with the
scaled integral integral model is proved only afterward, first pointwise and then for
finite products and limits.
-/

noncomputable section

namespace PositiveDefiniteIntegralQuadraticForm

variable {n : ℕ} (H : PositiveDefiniteIntegralQuadraticForm n)

/-- The direct Schulze--Pillot local density of an integral quadratic form.  At
two this is the intrinsic shifted dyadic density; away from two it is the
intrinsic odd-prime density. -/
def normalizedLocalDensity (p : ℕ) [Fact (Nat.Prime p)] : ℝ :=
  if hp : p = 2 then
    H.dyadicNormalizedLocalDensity
  else
    H.oddPrimeNormalizedLocalDensity p hp

/-- The direct all-prime density agrees pointwise with the density of the
scaled integral integral model. -/
theorem normalizedLocalDensity_eq_latticeOfPolarForm
    (p : ℕ) [Fact (Nat.Prime p)] :
    H.normalizedLocalDensity p =
      PositiveDefiniteIntegralLattice.normalizedLocalDensity H.latticeOfPolarForm p := by
  by_cases hp : p = 2
  · subst p
    simpa [normalizedLocalDensity] using
      H.dyadicNormalizedLocalDensity_eq_latticeOfPolarForm
  · simpa [normalizedLocalDensity, hp] using
      H.oddPrimeNormalizedLocalDensity_eq_latticeOfPolarForm p hp

/-- The direct local factor used in the mass product of the integral quadratic form. -/
def massLocalFactor
    (p : ℕ) [Fact (Nat.Prime p)] : ℝ :=
  H.normalizedLocalDensity p

/-- The inverse of the direct local factor of the integral quadratic form. -/
def massLocalInverseFactor
    (p : ℕ) [Fact (Nat.Prime p)] : ℝ :=
  (H.massLocalFactor p)⁻¹

/-- The direct local factor indexed by the subtype of rational primes. -/
def massLocalFactorAtPrime
    (p : {p : ℕ // Nat.Prime p}) : ℝ :=
  letI : Fact (Nat.Prime p.1) := ⟨p.2⟩
  H.massLocalFactor p.1

/-- The inverse direct local factor indexed by rational primes. -/
def massLocalInverseFactorAtPrime
    (p : {p : ℕ // Nat.Prime p}) : ℝ :=
  (H.massLocalFactorAtPrime p)⁻¹

theorem massLocalFactor_eq_latticeOfPolarForm
    (p : ℕ) [Fact (Nat.Prime p)] :
    H.massLocalFactor p =
      PositiveDefiniteIntegralLattice.massLocalFactor
        H.latticeOfPolarForm p := by
  exact H.normalizedLocalDensity_eq_latticeOfPolarForm p

theorem massLocalInverseFactor_eq_latticeOfPolarForm
    (p : ℕ) [Fact (Nat.Prime p)] :
    H.massLocalInverseFactor p =
      PositiveDefiniteIntegralLattice.massLocalInverseFactor
        H.latticeOfPolarForm p := by
  rw [massLocalInverseFactor,
    PositiveDefiniteIntegralLattice.massLocalInverseFactor,
    H.massLocalFactor_eq_latticeOfPolarForm p]

theorem massLocalFactorAtPrime_eq_latticeOfPolarForm
    (p : {p : ℕ // Nat.Prime p}) :
    H.massLocalFactorAtPrime p =
      PositiveDefiniteIntegralLattice.massLocalFactorAtPrime
        H.latticeOfPolarForm p := by
  letI : Fact (Nat.Prime p.1) := ⟨p.2⟩
  exact H.massLocalFactor_eq_latticeOfPolarForm p.1

theorem massLocalInverseFactorAtPrime_eq_latticeOfPolarForm
    (p : {p : ℕ // Nat.Prime p}) :
    H.massLocalInverseFactorAtPrime p =
      PositiveDefiniteIntegralLattice.massLocalInverseFactorAtPrime
        H.latticeOfPolarForm p := by
  rw [massLocalInverseFactorAtPrime,
    PositiveDefiniteIntegralLattice.massLocalInverseFactorAtPrime,
    H.massLocalFactorAtPrime_eq_latticeOfPolarForm p]

/-- A finite product of the intrinsic inverse local factors of the integral quadratic form. -/
def massFinitePrimeInverseProduct
    (S : Finset {p : ℕ // Nat.Prime p}) : ℝ :=
  S.prod fun p => H.massLocalInverseFactorAtPrime p

theorem massFinitePrimeInverseProduct_eq_latticeOfPolarForm
    (S : Finset {p : ℕ // Nat.Prime p}) :
    H.massFinitePrimeInverseProduct S =
      PositiveDefiniteIntegralLattice.massFinitePrimeInverseProduct
        H.latticeOfPolarForm S := by
  unfold massFinitePrimeInverseProduct
    PositiveDefiniteIntegralLattice.massFinitePrimeInverseProduct
  apply Finset.prod_congr rfl
  intro p _hp
  exact H.massLocalInverseFactorAtPrime_eq_latticeOfPolarForm p

/-- The direct inverse local product over rational primes at most `N`. -/
def massPartialPrimeInverseProduct (N : ℕ) : ℝ :=
  H.massFinitePrimeInverseProduct
    (PositiveDefiniteIntegralLattice.rationalPrimesUpTo N)

theorem massPartialPrimeInverseProduct_eq_latticeOfPolarForm
    (N : ℕ) :
    H.massPartialPrimeInverseProduct N =
      PositiveDefiniteIntegralLattice.massPartialPrimeInverseProduct
        H.latticeOfPolarForm N := by
  unfold massPartialPrimeInverseProduct
    PositiveDefiniteIntegralLattice.massPartialPrimeInverseProduct
  exact H.massFinitePrimeInverseProduct_eq_latticeOfPolarForm
    (PositiveDefiniteIntegralLattice.rationalPrimesUpTo N)

/-- Convergence of the direct cutoff products of the integral quadratic form to `P`. -/
def massLocalInverseProductTendsTo (P : ℝ) : Prop :=
  Filter.Tendsto
    (fun N : ℕ => H.massPartialPrimeInverseProduct N)
    Filter.atTop (nhds P)

theorem massLocalInverseProductTendsTo_iff_latticeOfPolarForm
    (P : ℝ) :
    H.massLocalInverseProductTendsTo P ↔
      PositiveDefiniteIntegralLattice.massLocalInverseProductTendsTo
        H.latticeOfPolarForm P := by
  unfold massLocalInverseProductTendsTo
    PositiveDefiniteIntegralLattice.massLocalInverseProductTendsTo
  rw [show
    (fun N : ℕ => H.massPartialPrimeInverseProduct N) =
      (fun N : ℕ => PositiveDefiniteIntegralLattice.massPartialPrimeInverseProduct
        H.latticeOfPolarForm N) by
      funext N
      exact H.massPartialPrimeInverseProduct_eq_latticeOfPolarForm N]

/-- The direct product side of the integral quadratic form, built from the common
archimedean factor and a direct local-product limit. -/
def massFormulaProductSide
    (_H : PositiveDefiniteIntegralQuadraticForm n) (P : ℝ) : ℝ :=
  PositiveDefiniteIntegralLattice.archimedeanMassFactor n * P

theorem massFormulaProductSide_eq_latticeOfPolarForm
    (P : ℝ) :
    H.massFormulaProductSide P =
      PositiveDefiniteIntegralLattice.massFormulaProductSide
        H.latticeOfPolarForm P := by
  rfl

end PositiveDefiniteIntegralQuadraticForm

end
