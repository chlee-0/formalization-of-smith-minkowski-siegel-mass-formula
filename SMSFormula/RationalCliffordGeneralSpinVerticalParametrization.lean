import SMSFormula.RationalCliffordGeneralSpinRawVerticalCrossedCutoff

/-!
# Carrier parametrization of the vertical general-Spin fibers

The chosen representative over an idele class and the embedded intrinsic
Spin quotient jointly parametrize the rational adelic general-Spin quotient.
This is the carrier map underlying the existing vertical iterated integral.
It uses only the completed neutral-fiber exactness, not any measure or
Tamagawa comparison.
-/

noncomputable section

open PositiveDefiniteIntegralLattice

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

set_option synthInstance.maxHeartbeats 500000
set_option maxHeartbeats 1600000

/-- Successive right translations on the rational general-Spin quotient
multiply their translating adelic points in the same order. -/
theorem fullAdelicCliffordGeneralSpinLeftQuotientRightMul_rightMul
    (x y : V.FullAdelicCliffordGeneralSpinGroup)
    (z : V.FullAdelicCliffordGeneralSpinLeftQuotient) :
    V.fullAdelicCliffordGeneralSpinLeftQuotientRightMul y
        (V.fullAdelicCliffordGeneralSpinLeftQuotientRightMul x z) =
      V.fullAdelicCliffordGeneralSpinLeftQuotientRightMul (x * y) z := by
  induction z using Quot.inductionOn with
  | _ z =>
    change V.fullAdelicCliffordGeneralSpinLeftQuotientMap ((z * x) * y) =
      V.fullAdelicCliffordGeneralSpinLeftQuotientMap (z * (x * y))
    rw [mul_assoc]

/-- Translation by the identity is the identity on the quotient. -/
@[simp]
theorem fullAdelicCliffordGeneralSpinLeftQuotientRightMul_one
    (z : V.FullAdelicCliffordGeneralSpinLeftQuotient) :
    V.fullAdelicCliffordGeneralSpinLeftQuotientRightMul 1 z = z := by
  induction z using Quot.inductionOn with
  | _ z =>
    change V.fullAdelicCliffordGeneralSpinLeftQuotientMap (z * 1) =
      V.fullAdelicCliffordGeneralSpinLeftQuotientMap z
    rw [mul_one]

/-- An idele class and an intrinsic Spin quotient point give the point on the
corresponding translated vertical fiber. -/
noncomputable def fullAdelicCliffordGeneralSpinVerticalParametrization
    (hsurj : Function.Surjective
      V.fullAdelicCliffordGeneralSpinLeftQuotientToIdeleClass) :
    RationalIdeleClassGroup ×
        V.FullAdelicCliffordSpinCandidateLeftQuotient →
      V.FullAdelicCliffordGeneralSpinLeftQuotient :=
  fun z =>
    V.fullAdelicCliffordGeneralSpinLeftQuotientRightMul
      (V.verticalGeneralSpinRepresentative hsurj z.1)
      (V.fullAdelicCliffordSpinCandidateLeftQuotientToGeneralSpin z.2)

/-- The idele-class coordinate of the vertical parametrization is its first
coordinate. -/
@[simp]
theorem fullAdelicCliffordGeneralSpinVerticalParametrization_ideleClass
    (hsurj : Function.Surjective
      V.fullAdelicCliffordGeneralSpinLeftQuotientToIdeleClass)
    (z : RationalIdeleClassGroup ×
      V.FullAdelicCliffordSpinCandidateLeftQuotient) :
    V.fullAdelicCliffordGeneralSpinLeftQuotientToIdeleClass
        (V.fullAdelicCliffordGeneralSpinVerticalParametrization hsurj z) = z.1 := by
  rcases z with ⟨c, u⟩
  rw [fullAdelicCliffordGeneralSpinVerticalParametrization,
    V.fullAdelicCliffordGeneralSpinLeftQuotientToIdeleClass_rightMul]
  have hneutral :
      V.fullAdelicCliffordGeneralSpinLeftQuotientToIdeleClass
          (V.fullAdelicCliffordSpinCandidateLeftQuotientToGeneralSpin u) = 1 := by
    induction u using Quot.inductionOn with
    | _ x =>
      exact V.fullAdelicCliffordSpinCandidateLeftQuotientToGeneralSpin_neutral x
  rw [hneutral]
  exact (one_mul _).trans
    (V.verticalGeneralSpinRepresentative_ideleClass hsurj c)

end RationalQuadraticSpaceMatrix

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- Rank-at-least-three form of the completed neutral-fiber exactness. -/
theorem mem_range_fullAdelicCliffordSpinCandidateLeftQuotientToGeneralSpin_iff_of_rankAtLeastThree
    (L : PositiveDefiniteIntegralLattice n) (hn : 3 ≤ n)
    (c : L.rationalQuadraticSpaceMatrix.FullAdelicCliffordGeneralSpinLeftQuotient) :
    c ∈ Set.range
        L.rationalQuadraticSpaceMatrix.fullAdelicCliffordSpinCandidateLeftQuotientToGeneralSpin ↔
      L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinLeftQuotientToIdeleClass c = 1 := by
  obtain ⟨r, rfl⟩ : ∃ r, n = r + 2 := ⟨n - 2, by omega⟩
  exact L.mem_range_fullAdelicCliffordSpinCandidateLeftQuotientToGeneralSpin_iff
    (by omega) c

/-- In every lattice rank at least three, the vertical parametrization fills
the complete rational adelic general-Spin quotient. -/
theorem fullAdelicCliffordGeneralSpinVerticalParametrization_surjective
    (L : PositiveDefiniteIntegralLattice n) (hn : 3 ≤ n)
    (hsurj : Function.Surjective
      L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinLeftQuotientToIdeleClass) :
    Function.Surjective
      (L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinVerticalParametrization
        hsurj) := by
  let V := L.rationalQuadraticSpaceMatrix
  intro z
  let c := V.fullAdelicCliffordGeneralSpinLeftQuotientToIdeleClass z
  let x := V.verticalGeneralSpinRepresentative hsurj c
  let w := V.fullAdelicCliffordGeneralSpinLeftQuotientRightMul x⁻¹ z
  have hwneutral :
      V.fullAdelicCliffordGeneralSpinLeftQuotientToIdeleClass w = 1 := by
    dsimp only [w]
    rw [V.fullAdelicCliffordGeneralSpinLeftQuotientToIdeleClass_rightMul,
      map_inv, map_inv, V.verticalGeneralSpinRepresentative_ideleClass]
    exact mul_inv_cancel c
  have hwmem : w ∈ Set.range
      V.fullAdelicCliffordSpinCandidateLeftQuotientToGeneralSpin :=
    (L.mem_range_fullAdelicCliffordSpinCandidateLeftQuotientToGeneralSpin_iff_of_rankAtLeastThree
      hn w).2 hwneutral
  rcases hwmem with ⟨u, hu⟩
  refine ⟨⟨c, u⟩, ?_⟩
  change V.fullAdelicCliffordGeneralSpinLeftQuotientRightMul x
      (V.fullAdelicCliffordSpinCandidateLeftQuotientToGeneralSpin u) = z
  rw [hu]
  rw [V.fullAdelicCliffordGeneralSpinLeftQuotientRightMul_rightMul]
  simp

end PositiveDefiniteIntegralLattice
