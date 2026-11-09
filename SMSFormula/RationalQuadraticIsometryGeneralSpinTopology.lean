import SMSFormula.RationalQuadraticIsometryGeneralSpinAdelicQuotient
import SMSFormula.RationalQuadraticSpaceAnisotropicPresentationTopology
import SMSFormula.RationalCliffordGeneralSpinPointTopology
import SMSFormula.RationalCliffordGeneralSpinAdelicHorizontalBorel

/-!
# Native topology on intrinsic general-Spin presentation equivalences

The intrinsic `GSpin` equivalence attached to a supplied anisotropic-
complement presentation is a homeomorphism for the repository's existing
finite-coordinate topologies.  The full-adelic specialization descends to a
homeomorphism of the existing rational left quotients and is measurable for
their certified Borel structures.

Continuity is proved directly from finite Clifford-coordinate expansion and
the native continuous block-to-ambient linear isometry.  No topology or Haar
measure is transported through the presentation.
-/

noncomputable section

open PositiveDefiniteIntegralLattice
open scoped Matrix

namespace RationalQuadraticSpaceMatrix
namespace AnisotropicComplementPresentation

variable {n m : ℕ}
variable {V : RationalQuadraticSpaceMatrix n} {x : Fin n → ℚ}
variable (P : V.AnisotropicComplementPresentation x m)

private theorem continuous_conjugatedMatrixCoordinate
    {r s : ℕ} {A X : Type*}
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [TopologicalSpace X]
    (E : (Fin r → A) ≃ₗ[A] (Fin s → A))
    (hE : Continuous E)
    (M : X → Matrix (Fin r) (Fin r) A)
    (hM : ∀ i j, Continuous (fun z ↦ M z i j))
    (i j : Fin s) :
    Continuous (fun z ↦
      E (Matrix.mulVec (M z) (E.symm (Pi.single j 1))) i) := by
  apply (continuous_apply i).comp
  apply hE.comp
  apply continuous_pi
  intro k
  change Continuous (fun z ↦
    ∑ l, M z k l * E.symm (Pi.single j 1) l)
  apply continuous_finset_sum
  intro l _
  exact (hM k l).mul continuous_const

/-- The forward presentation map on intrinsic general-Spin points is
continuous for every native topological rational algebra. -/
theorem continuous_blockToAmbientGeneralSpinIntrinsicPoint
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    (A : Type*) [CommRing A] [Algebra ℚ A]
    [TopologicalSpace A] [IsTopologicalRing A] :
    Continuous (P.blockToAmbientGeneralSpinIntrinsicPoint A hx) := by
  let E := P.blockToAmbientBaseChangeIsometryEquiv hx A
  let Φ := P.blockToAmbientCliffordBaseChangeAlgEquiv hx A
  have hmatrix (i j : Fin n) : Continuous (fun z :
      (P.blockSpace hx).CliffordGeneralSpinIntrinsicPoint A ↦
      (P.blockToAmbientGeneralSpinIntrinsicPoint A hx z).matrixPoint.1 i j) := by
    let b : Fin n → A := Pi.single j 1
    let v : Fin (m + 1) → A := E.symm b
    have hcont : Continuous (fun z :
        (P.blockSpace hx).CliffordGeneralSpinIntrinsicPoint A ↦
        E (Matrix.mulVec z.matrixPoint.1 v) i) := by
      simpa only [v] using
        (continuous_conjugatedMatrixCoordinate E
          (P.continuous_blockToAmbientBaseChangeIsometryEquiv hx A)
          (fun z :
            (P.blockSpace hx).CliffordGeneralSpinIntrinsicPoint A ↦
              z.matrixPoint.1)
          (fun k l ↦
            (P.blockSpace hx).continuous_cliffordGeneralSpinMatrixCoordinate
              A k l) i j)
    rw [show (fun z :
        (P.blockSpace hx).CliffordGeneralSpinIntrinsicPoint A ↦
        (P.blockToAmbientGeneralSpinIntrinsicPoint A hx z).matrixPoint.1 i j) =
        fun z ↦ E (Matrix.mulVec z.matrixPoint.1 v) i by
      funext z
      change (P.blockToAmbientSpecialOrthogonalMatrixPoint A hx
          z.matrixPoint).1 i j = _
      have hcol :
          (P.blockToAmbientSpecialOrthogonalMatrixPoint A hx
            z.matrixPoint).1 i j =
            Matrix.mulVec
              (P.blockToAmbientSpecialOrthogonalMatrixPoint A hx
                z.matrixPoint).1 b i := by
        simp [b, Matrix.mulVec, dotProduct, Pi.single_apply]
      rw [hcol,
        P.blockToAmbientSpecialOrthogonalMatrixPoint_mulVec A hx]
      rfl]
    exact hcont
  apply continuous_induced_rng.mpr
  apply Continuous.prodMk
  · apply Continuous.prodMk
    · apply continuous_pi
      intro u
      rw [show (fun z :
          (P.blockSpace hx).CliffordGeneralSpinIntrinsicPoint A ↦
          (V.cliffordCoordinateBaseChangeBasis A).repr
            ((P.blockToAmbientGeneralSpinIntrinsicPoint A hx z).cliffordUnit :
              V.cliffordCoordinateBaseChangeAlgebra A) u) =
          fun z ↦ ∑ s,
            ((P.blockSpace hx).cliffordCoordinateBaseChangeBasis A).repr
                (z.cliffordUnit :
                  (P.blockSpace hx).cliffordCoordinateBaseChangeAlgebra A) s *
              (V.cliffordCoordinateBaseChangeBasis A).repr
                (Φ ((P.blockSpace hx).cliffordCoordinateBaseChangeBasis A s)) u by
        funext z
        change (V.cliffordCoordinateBaseChangeBasis A).repr
            (Φ (z.cliffordUnit :
              (P.blockSpace hx).cliffordCoordinateBaseChangeAlgebra A)) u = _
        conv_lhs =>
          rw [← ((P.blockSpace hx).cliffordCoordinateBaseChangeBasis A).sum_repr
            (z.cliffordUnit :
              (P.blockSpace hx).cliffordCoordinateBaseChangeAlgebra A)]
        simp only [map_sum, map_smul, Finsupp.coe_finset_sum,
          Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul]]
      apply continuous_finset_sum
      intro s _
      exact ((P.blockSpace hx).continuous_cliffordGeneralSpinCliffordCoordinate
        A s).mul continuous_const
    · simpa using
        (P.blockSpace hx).continuous_cliffordGeneralSpinSimilitude A
  · apply Continuous.prodMk
    · apply continuous_pi
      intro i
      apply continuous_pi
      intro j
      exact hmatrix i j
    · apply continuous_pi
      intro i
      apply continuous_pi
      intro j
      rw [show (fun z :
          (P.blockSpace hx).CliffordGeneralSpinIntrinsicPoint A ↦
          (P.blockToAmbientGeneralSpinIntrinsicPoint A hx z).matrixGroup⁻¹.1.1.1
            i j) =
          fun z ↦
            (P.blockToAmbientGeneralSpinIntrinsicPoint A hx z⁻¹).matrixPoint.1
              i j by
        funext z
        calc
          (P.blockToAmbientGeneralSpinIntrinsicPoint A hx z).matrixGroup⁻¹.1.1.1
                i j =
              ((P.blockToAmbientGeneralSpinIntrinsicPoint A hx z)⁻¹).matrixPoint.1
                i j := by
                  rw [← CliffordGeneralSpinIntrinsicPoint.matrixGroup_coe,
                    CliffordGeneralSpinIntrinsicPoint.inv_matrixGroup]
          _ = (P.blockToAmbientGeneralSpinIntrinsicPoint A hx z⁻¹).matrixPoint.1
                i j := by
                  exact congrArg
                    (fun w : V.CliffordGeneralSpinIntrinsicPoint A ↦
                      w.matrixPoint.1 i j)
                    (map_inv (P.blockToAmbientGeneralSpinMulEquiv A hx) z).symm]
      exact
        (hmatrix i j).comp
          ((P.blockSpace hx).continuous_inv_cliffordGeneralSpinIntrinsicPoint A)

/-- The inverse presentation map on intrinsic general-Spin points is
continuous for the same native topologies. -/
theorem continuous_ambientToBlockGeneralSpinIntrinsicPoint
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    (A : Type*) [CommRing A] [Algebra ℚ A]
    [TopologicalSpace A] [IsTopologicalRing A] :
    Continuous (P.ambientToBlockGeneralSpinIntrinsicPoint A hx) := by
  let E := P.blockToAmbientBaseChangeIsometryEquiv hx A
  let Φ := P.blockToAmbientCliffordBaseChangeAlgEquiv hx A
  have hmatrix (i j : Fin (m + 1)) : Continuous (fun z :
      V.CliffordGeneralSpinIntrinsicPoint A ↦
      (P.ambientToBlockGeneralSpinIntrinsicPoint A hx z).matrixPoint.1 i j) := by
    let b : Fin (m + 1) → A := Pi.single j 1
    let v : Fin n → A := E b
    have hcont : Continuous (fun z : V.CliffordGeneralSpinIntrinsicPoint A ↦
        E.symm (Matrix.mulVec z.matrixPoint.1 v) i) := by
      simpa only [v] using
        (continuous_conjugatedMatrixCoordinate E.symm
          (P.continuous_blockToAmbientBaseChangeIsometryEquiv_symm hx A)
          (fun z : V.CliffordGeneralSpinIntrinsicPoint A ↦ z.matrixPoint.1)
          (fun k l ↦ V.continuous_cliffordGeneralSpinMatrixCoordinate A k l)
          i j)
    rw [show (fun z : V.CliffordGeneralSpinIntrinsicPoint A ↦
        (P.ambientToBlockGeneralSpinIntrinsicPoint A hx z).matrixPoint.1 i j) =
        fun z ↦ E.symm (Matrix.mulVec z.matrixPoint.1 v) i by
      funext z
      change (P.ambientToBlockSpecialOrthogonalMatrixPoint A hx
          z.matrixPoint).1 i j = _
      have hcol :
          (P.ambientToBlockSpecialOrthogonalMatrixPoint A hx
            z.matrixPoint).1 i j =
            Matrix.mulVec
              (P.ambientToBlockSpecialOrthogonalMatrixPoint A hx
                z.matrixPoint).1 b i := by
        simp [b, Matrix.mulVec, dotProduct, Pi.single_apply]
      rw [hcol,
        P.ambientToBlockSpecialOrthogonalMatrixPoint_mulVec A hx]
      rfl]
    exact hcont
  apply continuous_induced_rng.mpr
  apply Continuous.prodMk
  · apply Continuous.prodMk
    · apply continuous_pi
      intro u
      rw [show (fun z : V.CliffordGeneralSpinIntrinsicPoint A ↦
          ((P.blockSpace hx).cliffordCoordinateBaseChangeBasis A).repr
            ((P.ambientToBlockGeneralSpinIntrinsicPoint A hx z).cliffordUnit :
              (P.blockSpace hx).cliffordCoordinateBaseChangeAlgebra A) u) =
          fun z ↦ ∑ s,
            (V.cliffordCoordinateBaseChangeBasis A).repr
                (z.cliffordUnit : V.cliffordCoordinateBaseChangeAlgebra A) s *
              ((P.blockSpace hx).cliffordCoordinateBaseChangeBasis A).repr
                (Φ.symm (V.cliffordCoordinateBaseChangeBasis A s)) u by
        funext z
        change ((P.blockSpace hx).cliffordCoordinateBaseChangeBasis A).repr
            (Φ.symm (z.cliffordUnit :
              V.cliffordCoordinateBaseChangeAlgebra A)) u = _
        conv_lhs =>
          rw [← (V.cliffordCoordinateBaseChangeBasis A).sum_repr
            (z.cliffordUnit : V.cliffordCoordinateBaseChangeAlgebra A)]
        simp only [map_sum, map_smul, Finsupp.coe_finset_sum,
          Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul]]
      apply continuous_finset_sum
      intro s _
      exact (V.continuous_cliffordGeneralSpinCliffordCoordinate A s).mul
        continuous_const
    · simpa using V.continuous_cliffordGeneralSpinSimilitude A
  · apply Continuous.prodMk
    · apply continuous_pi
      intro i
      apply continuous_pi
      intro j
      exact hmatrix i j
    · apply continuous_pi
      intro i
      apply continuous_pi
      intro j
      rw [show (fun z : V.CliffordGeneralSpinIntrinsicPoint A ↦
          (P.ambientToBlockGeneralSpinIntrinsicPoint A hx z).matrixGroup⁻¹.1.1.1
            i j) =
          fun z ↦
            (P.ambientToBlockGeneralSpinIntrinsicPoint A hx z⁻¹).matrixPoint.1
              i j by
        funext z
        calc
          (P.ambientToBlockGeneralSpinIntrinsicPoint A hx z).matrixGroup⁻¹.1.1.1
                i j =
              ((P.ambientToBlockGeneralSpinIntrinsicPoint A hx z)⁻¹).matrixPoint.1
                i j := by
                  rw [← CliffordGeneralSpinIntrinsicPoint.matrixGroup_coe,
                    CliffordGeneralSpinIntrinsicPoint.inv_matrixGroup]
          _ = (P.ambientToBlockGeneralSpinIntrinsicPoint A hx z⁻¹).matrixPoint.1
                i j := by
                  exact congrArg
                    (fun w :
                      (P.blockSpace hx).CliffordGeneralSpinIntrinsicPoint A ↦
                        w.matrixPoint.1 i j)
                    (map_inv
                      (P.blockToAmbientGeneralSpinMulEquiv A hx).symm z).symm]
      exact
        (hmatrix i j).comp
          (V.continuous_inv_cliffordGeneralSpinIntrinsicPoint A)

/-- The algebraic presentation equivalence is a continuous multiplicative
equivalence on every native topological rational algebra. -/
def blockToAmbientGeneralSpinContinuousMulEquiv
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    (A : Type*) [CommRing A] [Algebra ℚ A]
    [TopologicalSpace A] [IsTopologicalRing A] :
    (P.blockSpace hx).CliffordGeneralSpinIntrinsicPoint A ≃ₜ*
      V.CliffordGeneralSpinIntrinsicPoint A :=
  ContinuousMulEquiv.mk'
    { toEquiv := (P.blockToAmbientGeneralSpinMulEquiv A hx).toEquiv
      continuous_toFun :=
        P.continuous_blockToAmbientGeneralSpinIntrinsicPoint hx A
      continuous_invFun :=
        P.continuous_ambientToBlockGeneralSpinIntrinsicPoint hx A }
    (P.blockToAmbientGeneralSpinMulEquiv A hx).map_mul

@[simp]
theorem blockToAmbientGeneralSpinContinuousMulEquiv_toMulEquiv
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    (A : Type*) [CommRing A] [Algebra ℚ A]
    [TopologicalSpace A] [IsTopologicalRing A] :
    (P.blockToAmbientGeneralSpinContinuousMulEquiv hx A).toMulEquiv =
      P.blockToAmbientGeneralSpinMulEquiv A hx := by
  rfl

/-- The native full-adelic specialization of the presentation homeomorphism. -/
abbrev blockToAmbientFullAdelicGeneralSpinContinuousMulEquiv
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    (P.blockSpace hx).FullAdelicCliffordGeneralSpinGroup ≃ₜ*
      V.FullAdelicCliffordGeneralSpinGroup :=
  P.blockToAmbientGeneralSpinContinuousMulEquiv hx RationalAdele

/-- The full-adelic group presentation equivalence is measurable for the
existing Borel structures. -/
theorem measurable_blockToAmbientFullAdelicGeneralSpinContinuousMulEquiv
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    Measurable (P.blockToAmbientFullAdelicGeneralSpinContinuousMulEquiv hx) :=
  (P.blockToAmbientFullAdelicGeneralSpinContinuousMulEquiv hx).continuous.measurable

/-- The inverse full-adelic group presentation equivalence is measurable for
the existing Borel structures. -/
theorem measurable_blockToAmbientFullAdelicGeneralSpinContinuousMulEquiv_symm
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    Measurable
      (P.blockToAmbientFullAdelicGeneralSpinContinuousMulEquiv hx).symm :=
  (P.blockToAmbientFullAdelicGeneralSpinContinuousMulEquiv hx).symm.continuous.measurable

/-- The algebraic full-adelic left-quotient equivalence is a homeomorphism for
the existing quotient topologies. -/
def blockToAmbientGeneralSpinFullAdelicLeftQuotientHomeomorph
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    (P.blockSpace hx).FullAdelicCliffordGeneralSpinLeftQuotient ≃ₜ
      V.FullAdelicCliffordGeneralSpinLeftQuotient where
  toEquiv := P.blockToAmbientGeneralSpinFullAdelicLeftQuotientEquiv hx
  continuous_toFun := by
    apply Continuous.quotient_lift
    simpa only [Function.comp_apply,
      P.blockToAmbientGeneralSpinFullAdelicLeftQuotientEquiv_mk hx] using
      V.fullAdelicCliffordGeneralSpinLeftQuotientMap_isQuotientMap.continuous.comp
        (P.blockToAmbientFullAdelicGeneralSpinContinuousMulEquiv hx).continuous
  continuous_invFun := by
    apply Continuous.quotient_lift
    simpa only [Function.comp_apply,
      P.blockToAmbientGeneralSpinFullAdelicLeftQuotientEquiv_symm_mk hx] using
      (P.blockSpace hx).fullAdelicCliffordGeneralSpinLeftQuotientMap_isQuotientMap.continuous.comp
        (P.blockToAmbientFullAdelicGeneralSpinContinuousMulEquiv hx).symm.continuous

@[simp]
theorem blockToAmbientGeneralSpinFullAdelicLeftQuotientHomeomorph_toEquiv
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    (P.blockToAmbientGeneralSpinFullAdelicLeftQuotientHomeomorph hx).toEquiv =
      P.blockToAmbientGeneralSpinFullAdelicLeftQuotientEquiv hx := by
  rfl

/-- The descended quotient homeomorphism is measurable for the certified
Borel quotient structures. -/
theorem measurable_blockToAmbientGeneralSpinFullAdelicLeftQuotientHomeomorph
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    Measurable
      (P.blockToAmbientGeneralSpinFullAdelicLeftQuotientHomeomorph hx) :=
  (P.blockToAmbientGeneralSpinFullAdelicLeftQuotientHomeomorph hx).continuous.measurable

/-- The inverse quotient homeomorphism is measurable for the same certified
Borel structures. -/
theorem measurable_blockToAmbientGeneralSpinFullAdelicLeftQuotientHomeomorph_symm
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    Measurable
      (P.blockToAmbientGeneralSpinFullAdelicLeftQuotientHomeomorph hx).symm :=
  (P.blockToAmbientGeneralSpinFullAdelicLeftQuotientHomeomorph hx).symm.continuous.measurable

end AnisotropicComplementPresentation
end RationalQuadraticSpaceMatrix
