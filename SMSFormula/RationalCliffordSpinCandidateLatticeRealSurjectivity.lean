import SMSFormula.RationalCliffordGeneralSpinFieldSurjectivity
import SMSFormula.RationalCliffordGeneralSpinLatticeRealSimilitude
import SMSFormula.RationalCliffordSpinCandidateGeneralSpinEmbedding

/-!
# Real surjectivity of the represented lattice Spin cover

For a positive-definite lattice form, every real intrinsic general-Spin
similitude is positive.  Starting from an arbitrary general-Spin lift of a
real special-orthogonal point, multiplication by the central scalar with
positive inverse square root moves the lift into the literal similitude-one
fiber without changing its special-orthogonal image.  The already proved
identification of the represented Spin carrier with that fiber then gives
surjectivity of the actual real candidate point map.
-/

noncomputable section

open PositiveDefiniteIntegralLattice

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- The represented intrinsic Spin group surjects onto the real
special-orthogonal group of a positive-definite integral lattice. -/
theorem realCliffordSpinCandidateToSpecialOrthogonalHom_surjective
    (L : PositiveDefiniteIntegralLattice n) :
    Function.Surjective
      L.rationalQuadraticSpaceMatrix.realCliffordSpinCandidateToSpecialOrthogonalHom := by
  let V := L.rationalQuadraticSpaceMatrix
  intro g
  change V.specialOrthogonalMatrixGroup ℝ at g
  obtain ⟨x, hx⟩ :=
    RationalQuadraticSpaceMatrix.CliffordGeneralSpinIntrinsicPoint.toSpecialOrthogonalGroupHom_surjective
      V ℝ g
  have hxpos : 0 < (x.similitude : ℝ) := by
    exact RationalQuadraticSpaceMatrix.realCliffordGeneralSpinSimilitude_pos L x
  have hxinvpos : 0 < ((x.similitude⁻¹ : ℝˣ) : ℝ) := by
    simpa using inv_pos.mpr hxpos
  let z : ℝˣ := Units.mk0 (Real.sqrt ((x.similitude⁻¹ : ℝˣ) : ℝ))
    (ne_of_gt (Real.sqrt_pos.2 hxinvpos))
  have hzsq : z ^ 2 = x.similitude⁻¹ := by
    apply Units.ext
    change Real.sqrt ((x.similitude⁻¹ : ℝˣ) : ℝ) ^ 2 =
      ((x.similitude⁻¹ : ℝˣ) : ℝ)
    exact Real.sq_sqrt (le_of_lt hxinvpos)
  let y : V.CliffordGeneralSpinIntrinsicPoint ℝ :=
    RationalQuadraticSpaceMatrix.CliffordGeneralSpinIntrinsicPoint.ofScalar V ℝ z * x
  have hysim : y.similitude = 1 := by
    change
      (RationalQuadraticSpaceMatrix.CliffordGeneralSpinIntrinsicPoint.ofScalar
          V ℝ z * x).similitude = 1
    rw [RationalQuadraticSpaceMatrix.CliffordGeneralSpinIntrinsicPoint.mul_similitude,
      RationalQuadraticSpaceMatrix.CliffordGeneralSpinIntrinsicPoint.ofScalar_similitude,
      hzsq, inv_mul_cancel]
  have hyker : y ∈
      (RationalQuadraticSpaceMatrix.CliffordGeneralSpinIntrinsicPoint.similitudeGroupHom
        V ℝ).ker := by
    exact hysim
  rw [← V.range_cliffordSpinCandidateToCliffordGeneralSpinHom_eq_ker ℝ] at hyker
  obtain ⟨s, hs⟩ := hyker
  have hzso :
      RationalQuadraticSpaceMatrix.CliffordGeneralSpinIntrinsicPoint.toSpecialOrthogonalGroupHom
          V ℝ
          (RationalQuadraticSpaceMatrix.CliffordGeneralSpinIntrinsicPoint.ofScalar
            V ℝ z) = 1 := by
    exact RationalQuadraticSpaceMatrix.CliffordGeneralSpinIntrinsicPoint.ofScalar_matrixGroup
      V ℝ z
  refine ⟨s, ?_⟩
  calc
    V.realCliffordSpinCandidateToSpecialOrthogonalHom s =
        RationalQuadraticSpaceMatrix.CliffordGeneralSpinIntrinsicPoint.toSpecialOrthogonalGroupHom
          V ℝ
            (V.cliffordSpinCandidateToCliffordGeneralSpinHom ℝ s) := rfl
    _ = RationalQuadraticSpaceMatrix.CliffordGeneralSpinIntrinsicPoint.toSpecialOrthogonalGroupHom
          V ℝ y := by rw [hs]
    _ = RationalQuadraticSpaceMatrix.CliffordGeneralSpinIntrinsicPoint.toSpecialOrthogonalGroupHom
          V ℝ
            (RationalQuadraticSpaceMatrix.CliffordGeneralSpinIntrinsicPoint.ofScalar
              V ℝ z) *
        RationalQuadraticSpaceMatrix.CliffordGeneralSpinIntrinsicPoint.toSpecialOrthogonalGroupHom
          V ℝ x := by
            exact map_mul
              (RationalQuadraticSpaceMatrix.CliffordGeneralSpinIntrinsicPoint.toSpecialOrthogonalGroupHom
                V ℝ) _ _
    _ = 1 * g := by rw [hzso, hx]
    _ = g := one_mul g

/-- Set-valued form used to remove the real range restriction from the
finite-cutoff comparison measures. -/
theorem range_realCliffordSpinCandidateToSpecialOrthogonalHom_eq_univ
    (L : PositiveDefiniteIntegralLattice n) :
    Set.range
        L.rationalQuadraticSpaceMatrix.realCliffordSpinCandidateToSpecialOrthogonalHom =
      Set.univ :=
  Set.range_eq_univ.mpr
    (realCliffordSpinCandidateToSpecialOrthogonalHom_surjective L)

/-- Subgroup-valued form used by the literal local pushforward measures. -/
theorem realCliffordSpinCandidateToSpecialOrthogonalHom_range_eq_top
    (L : PositiveDefiniteIntegralLattice n) :
    L.rationalQuadraticSpaceMatrix.realCliffordSpinCandidateToSpecialOrthogonalHom.range =
      ⊤ :=
  MonoidHom.range_eq_top.mpr
    (realCliffordSpinCandidateToSpecialOrthogonalHom_surjective L)

end PositiveDefiniteIntegralLattice
