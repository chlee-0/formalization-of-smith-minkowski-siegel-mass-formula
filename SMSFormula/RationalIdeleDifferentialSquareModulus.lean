import SMSFormula.RationalIdeleDifferentialFiniteIdeleHaar
import SMSFormula.PadicCayleyTangentModulus

/-!
# Square moduli for differential rational ideles

The central coordinate in the local horizontal `GSpin` chart is the square
map.  Its one-dimensional differential modulus is the norm of `2` in the
fixed real or p-adic factor.  This file records those literal moduli at the
same local scales used by differential rational-idele Haar.

At the real place the modulus is `2`; at the dyadic place it is `2⁻¹`; and at
every other finite place it is `1`.  Consequently every finite exceptional
cylinder containing the dyadic place has total real--finite square modulus
exactly one.  The product below is deliberately finite: it is not an Euler
product and carries no sheet-count factor.

This module records the scalar/Jacobian package.  It does not prove the
branchwise square-map change-of-variables theorem or the horizontal
`GSpin -> SO` ambient disintegration.
-/

noncomputable section

open scoped NNReal

namespace RationalQuadraticSpaceMatrix

/-! ## Fixed local moduli -/

/-- The differential modulus of the real square coordinate. -/
def rationalIdeleRealSquareModulus : ℝ≥0 :=
  ‖(2 : ℝ)‖₊

/-- The differential modulus of the p-adic square coordinate. -/
def rationalIdelePadicSquareModulus
    (p : ℕ) [Fact (Nat.Prime p)] : ℝ≥0 :=
  ‖(2 : ℚ_[p])‖₊

@[simp]
theorem rationalIdeleRealSquareModulus_eq_two :
    rationalIdeleRealSquareModulus = 2 := by
  norm_num [rationalIdeleRealSquareModulus]

@[simp]
theorem rationalIdelePadicSquareModulus_eq_one_of_ne_two
    (p : ℕ) [Fact (Nat.Prime p)] (hp : p ≠ 2) :
    rationalIdelePadicSquareModulus p = 1 := by
  exact Matrix.nnnorm_two_padic_eq_one_of_ne_two p hp

@[simp]
theorem rationalIdelePadicSquareModulus_two :
    rationalIdelePadicSquareModulus 2 = (2 : ℝ≥0)⁻¹ := by
  exact Matrix.nnnorm_two_dyadic

@[simp]
theorem rationalIdeleReal_mul_dyadicSquareModulus :
    rationalIdeleRealSquareModulus *
        rationalIdelePadicSquareModulus 2 = 1 := by
  rw [rationalIdeleRealSquareModulus_eq_two,
    rationalIdelePadicSquareModulus_two]
  exact mul_inv_cancel₀ (by norm_num)

/-! ## Finite exceptional-place package -/

/-- The finite rational place above `2`. -/
def rationalIdeleDyadicPlace : IsDedekindDomain.HeightOneSpectrum ℤ :=
  Rat.HeightOneSpectrum.primesEquiv.symm ⟨2, Nat.prime_two⟩

/-- The p-adic square modulus indexed by the finite-place carrier used by
the restricted product. -/
def rationalIdeleFinitePlaceSquareModulus
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) : ℝ≥0 := by
  letI : Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩
  exact rationalIdelePadicSquareModulus
    (Rat.HeightOneSpectrum.primesEquiv v).1

@[simp]
theorem rationalIdeleFinitePlaceSquareModulus_dyadic :
    rationalIdeleFinitePlaceSquareModulus rationalIdeleDyadicPlace =
      (2 : ℝ≥0)⁻¹ := by
  simp [rationalIdeleFinitePlaceSquareModulus, rationalIdeleDyadicPlace]

theorem rationalIdeleFinitePlaceSquareModulus_eq_one_of_ne_dyadic
    (v : IsDedekindDomain.HeightOneSpectrum ℤ)
    (hv : v ≠ rationalIdeleDyadicPlace) :
    rationalIdeleFinitePlaceSquareModulus v = 1 := by
  let p := Rat.HeightOneSpectrum.primesEquiv v
  have hp : p.1 ≠ 2 := by
    intro hp2
    apply hv
    apply Rat.HeightOneSpectrum.primesEquiv.injective
    rw [rationalIdeleDyadicPlace, Equiv.apply_symm_apply]
    apply Subtype.ext
    exact hp2
  letI : Fact (Nat.Prime p.1) := ⟨p.2⟩
  exact rationalIdelePadicSquareModulus_eq_one_of_ne_two p.1 hp

/-- The literal finite product of square moduli exposed by an exceptional
set.  This is a finite cylinder coefficient, never an Euler product. -/
def rationalIdeleFiniteExceptionalSquareModulus
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) : ℝ≥0 :=
  ∏ v ∈ S, rationalIdeleFinitePlaceSquareModulus v

@[simp]
theorem rationalIdeleFiniteExceptionalSquareModulus_eq_one_of_not_mem_dyadic
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hS : rationalIdeleDyadicPlace ∉ S) :
    rationalIdeleFiniteExceptionalSquareModulus S = 1 := by
  rw [rationalIdeleFiniteExceptionalSquareModulus]
  apply Finset.prod_eq_one
  intro v hv
  exact rationalIdeleFinitePlaceSquareModulus_eq_one_of_ne_dyadic v
    (fun h ↦ hS (h ▸ hv))

@[simp]
theorem rationalIdeleFiniteExceptionalSquareModulus_eq_inv_two_of_mem_dyadic
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hS : rationalIdeleDyadicPlace ∈ S) :
    rationalIdeleFiniteExceptionalSquareModulus S = (2 : ℝ≥0)⁻¹ := by
  classical
  rw [rationalIdeleFiniteExceptionalSquareModulus]
  calc
    ∏ v ∈ S, rationalIdeleFinitePlaceSquareModulus v =
        rationalIdeleFinitePlaceSquareModulus rationalIdeleDyadicPlace *
          ∏ v ∈ S.erase rationalIdeleDyadicPlace,
            rationalIdeleFinitePlaceSquareModulus v := by
      rw [Finset.mul_prod_erase _ _ hS]
    _ = (2 : ℝ≥0)⁻¹ * 1 := by
      rw [rationalIdeleFinitePlaceSquareModulus_dyadic]
      congr 1
      apply Finset.prod_eq_one
      intro v hv
      exact rationalIdeleFinitePlaceSquareModulus_eq_one_of_ne_dyadic v
        (Finset.ne_of_mem_erase hv)
    _ = (2 : ℝ≥0)⁻¹ := mul_one _

/-- The real square modulus and the finite exceptional modulus cancel on
every cylinder that exposes the dyadic place. -/
@[simp]
theorem rationalIdeleReal_mul_finiteExceptionalSquareModulus_eq_one
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hS : rationalIdeleDyadicPlace ∈ S) :
    rationalIdeleRealSquareModulus *
        rationalIdeleFiniteExceptionalSquareModulus S = 1 := by
  rw [rationalIdeleRealSquareModulus_eq_two,
    rationalIdeleFiniteExceptionalSquareModulus_eq_inv_two_of_mem_dyadic S hS]
  exact mul_inv_cancel₀ (by norm_num)

end RationalQuadraticSpaceMatrix
