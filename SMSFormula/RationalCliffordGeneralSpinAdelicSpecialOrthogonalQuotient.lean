import SMSFormula.RationalCliffordSpinCandidateRawGeneralSpinQuotientPushforward
import SMSFormula.RationalCliffordGeneralSpinFieldSurjectivity

/-!
# The horizontal general-Spin map on rational adelic quotients

The intrinsic projection `GSpin(A) -> SO(A)` descends to rational left
quotients.  Its fibers are described directly by central adelic scalars:
two represented general-Spin quotient points have the same `SO` image if and
only if one is represented by a central scalar times the other.  Rational
general-Spin factors are already removed by the source quotient.

This is the carrier-level horizontal row of the crossed comparison.  No
measure, cutoff, or Tamagawa assertion is introduced here.
-/

noncomputable section

open PositiveDefiniteIntegralLattice

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

set_option synthInstance.maxHeartbeats 200000

/-- The intrinsic general-Spin projection on rational full-adelic left
quotients. -/
def fullAdelicCliffordGeneralSpinLeftQuotientToSpecialOrthogonal :
    V.FullAdelicCliffordGeneralSpinLeftQuotient →
      V.FullAdelicSpecialOrthogonalLeftQuotient :=
  Quot.lift
    (fun x => V.fullAdelicSpecialOrthogonalLeftQuotientMap
      (V.fullAdelicCliffordGeneralSpinToSpecialOrthogonalHom x)) (by
        intro x y hxy
        rcases hxy with ⟨gamma, rfl⟩
        rcases gamma.2 with ⟨q, hq⟩
        have hgamma :
            (gamma : V.FullAdelicCliffordGeneralSpinGroup) =
              V.rationalCliffordGeneralSpinFullAdelicDiagonalHom q :=
          hq.symm
        change V.fullAdelicSpecialOrthogonalLeftQuotientMap
            (V.fullAdelicCliffordGeneralSpinToSpecialOrthogonalHom x) =
          V.fullAdelicSpecialOrthogonalLeftQuotientMap
            (V.fullAdelicCliffordGeneralSpinToSpecialOrthogonalHom
              ((gamma : V.FullAdelicCliffordGeneralSpinGroup) * x))
        rw [map_mul, hgamma,
          V.rational_fullAdelic_diagonal_generalSpinToSpecialOrthogonal]
        exact (leftCosetMap_gamma_mul
          V.rationalSpecialOrthogonalFullAdelicDiagonalSubgroup
          ⟨V.rationalSpecialOrthogonalFullAdelicDiagonalHom
              (CliffordGeneralSpinIntrinsicPoint.toSpecialOrthogonalGroupHom
                V ℚ q),
            ⟨CliffordGeneralSpinIntrinsicPoint.toSpecialOrthogonalGroupHom
                V ℚ q, rfl⟩⟩
          (V.fullAdelicCliffordGeneralSpinToSpecialOrthogonalHom x)).symm)

@[simp]
theorem fullAdelicCliffordGeneralSpinLeftQuotientToSpecialOrthogonal_mk
    (x : V.FullAdelicCliffordGeneralSpinGroup) :
    V.fullAdelicCliffordGeneralSpinLeftQuotientToSpecialOrthogonal
        (V.fullAdelicCliffordGeneralSpinLeftQuotientMap x) =
      V.fullAdelicSpecialOrthogonalLeftQuotientMap
        (V.fullAdelicCliffordGeneralSpinToSpecialOrthogonalHom x) :=
  rfl

/-- The horizontal quotient map is measurable for the existing map-generated
quotient measurable structures. -/
theorem fullAdelicCliffordGeneralSpinLeftQuotientToSpecialOrthogonal_measurable :
    Measurable
      V.fullAdelicCliffordGeneralSpinLeftQuotientToSpecialOrthogonal := by
  rw [measurable_iff_comap_le]
  refine MeasurableSpace.comap_le_iff_le_map.mp ?_
  have hrep : Measurable
      (fun x : V.FullAdelicCliffordGeneralSpinGroup =>
        V.fullAdelicSpecialOrthogonalLeftQuotientMap
          (V.fullAdelicCliffordGeneralSpinToSpecialOrthogonalHom x)) :=
    V.fullAdelicSpecialOrthogonalLeftQuotientMap_measurable.comp
      V.continuous_fullAdelicCliffordGeneralSpinToSpecialOrthogonalHom.measurable
  simpa [fullAdelicCliffordGeneralSpinLeftQuotientToSpecialOrthogonal,
    Function.comp_def] using measurable_iff_comap_le.mp hrep

/-- Representative-level horizontal fiber exactness.  Equality after
projection to the rational `SO` quotient is exactly equality, in the
rational general-Spin quotient, after multiplication by an adelic central
scalar. -/
theorem fullAdelicCliffordGeneralSpinLeftQuotient_image_eq_iff_scalar
    (x y : V.FullAdelicCliffordGeneralSpinGroup) :
    V.fullAdelicCliffordGeneralSpinLeftQuotientToSpecialOrthogonal
        (V.fullAdelicCliffordGeneralSpinLeftQuotientMap x) =
      V.fullAdelicCliffordGeneralSpinLeftQuotientToSpecialOrthogonal
        (V.fullAdelicCliffordGeneralSpinLeftQuotientMap y) ↔
      ∃ a : RationalAdeleˣ,
        V.fullAdelicCliffordGeneralSpinLeftQuotientMap y =
          V.fullAdelicCliffordGeneralSpinLeftQuotientMap
            (CliffordGeneralSpinIntrinsicPoint.scalarGroupHom
              V RationalAdele a * x) := by
  constructor
  · intro hxy
    rw [V.fullAdelicCliffordGeneralSpinLeftQuotientToSpecialOrthogonal_mk,
      V.fullAdelicCliffordGeneralSpinLeftQuotientToSpecialOrthogonal_mk]
        at hxy
    have hrel := (leftCoset_mk_eq_iff
      V.rationalSpecialOrthogonalFullAdelicDiagonalSubgroup _ _).1 hxy
    rcases hrel with ⟨qA, hqA⟩
    rcases qA.2 with ⟨q, hq⟩
    obtain ⟨gamma, hgamma⟩ :=
      CliffordGeneralSpinIntrinsicPoint.toSpecialOrthogonalGroupHom_surjective
        V ℚ q
    let gammaA : V.FullAdelicCliffordGeneralSpinGroup :=
      V.rationalCliffordGeneralSpinFullAdelicDiagonalHom gamma
    let k : V.FullAdelicCliffordGeneralSpinGroup := gammaA⁻¹ * y * x⁻¹
    have hk : k ∈
        (CliffordGeneralSpinIntrinsicPoint.toSpecialOrthogonalGroupHom
          V RationalAdele).ker := by
      change V.fullAdelicCliffordGeneralSpinToSpecialOrthogonalHom k = 1
      dsimp [k, gammaA]
      have hq' :
          V.specialOrthogonalMatrixGroupMap (Algebra.ofId ℚ RationalAdele) q =
            (qA : V.FullAdelicSpecialOrthogonalGroup) := hq
      rw [map_mul, map_mul, map_inv, map_inv,
        V.rational_fullAdelic_diagonal_generalSpinToSpecialOrthogonal,
        hgamma, hq']
      rw [hqA]
      simp
    rw [← CliffordGeneralSpinIntrinsicPoint.range_scalarGroupHom_eq_ker_toSpecialOrthogonalGroupHom
      V RationalAdele] at hk
    rcases hk with ⟨a, ha⟩
    refine ⟨a, ?_⟩
    have hy :
        y = gammaA *
          (CliffordGeneralSpinIntrinsicPoint.scalarGroupHom
            V RationalAdele a * x) := by
      rw [ha]
      dsimp [k]
      simp [mul_assoc]
    rw [hy]
    exact (leftCosetMap_gamma_mul
      V.rationalCliffordGeneralSpinFullAdelicDiagonalSubgroup
      ⟨gammaA, ⟨gamma, rfl⟩⟩
      (CliffordGeneralSpinIntrinsicPoint.scalarGroupHom
        V RationalAdele a * x))
  · rintro ⟨a, hxy⟩
    rw [hxy,
      V.fullAdelicCliffordGeneralSpinLeftQuotientToSpecialOrthogonal_mk,
      V.fullAdelicCliffordGeneralSpinLeftQuotientToSpecialOrthogonal_mk]
    rw [map_mul]
    have haKer : CliffordGeneralSpinIntrinsicPoint.scalarGroupHom
        V RationalAdele a ∈
          (CliffordGeneralSpinIntrinsicPoint.toSpecialOrthogonalGroupHom
            V RationalAdele).ker := by
      rw [← CliffordGeneralSpinIntrinsicPoint.range_scalarGroupHom_eq_ker_toSpecialOrthogonalGroupHom
        V RationalAdele]
      exact ⟨a, rfl⟩
    change V.fullAdelicCliffordGeneralSpinToSpecialOrthogonalHom
        (CliffordGeneralSpinIntrinsicPoint.scalarGroupHom
          V RationalAdele a) = 1 at haKer
    rw [haKer, one_mul]

end RationalQuadraticSpaceMatrix
