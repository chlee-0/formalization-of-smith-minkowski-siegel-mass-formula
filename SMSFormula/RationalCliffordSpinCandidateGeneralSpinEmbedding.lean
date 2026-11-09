import SMSFormula.RationalCliffordGeneralSpinVerticalExactness
import SMSFormula.RationalCliffordGeneralSpinPointTopology
import SMSFormula.RationalCliffordSpinCandidateTopologicalGroup

/-!
# The represented Spin candidate inside intrinsic general Spin

The represented finite-coordinate Spin carrier maps to intrinsic `GSpin` by
the already constructed all-algebra point recognition followed by the
literal inclusion of reverse-norm-one Clifford points.  Its image is exactly
the kernel of similitude, and the construction commutes with arbitrary
rational-algebra scalar extension.
-/

noncomputable section

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)
variable (A : Type*) [CommRing A] [Algebra ℚ A]

/-- The represented intrinsic Spin carrier embedded in intrinsic `GSpin`. -/
def cliffordSpinCandidateToCliffordGeneralSpinHom :
    V.CliffordSpinCandidateGroup A →*
      V.CliffordGeneralSpinIntrinsicPoint A :=
  (CliffordGeneralSpinIntrinsicPoint.ofSpinGroupHom V A).comp
    (V.cliffordSpinCandidateCoordinateAlgHomMulEquivPointData A).toMonoidHom

@[simp]
theorem cliffordSpinCandidateToCliffordGeneralSpinHom_apply_similitude
    (x : V.CliffordSpinCandidateGroup A) :
    (V.cliffordSpinCandidateToCliffordGeneralSpinHom A x).similitude = 1 :=
  rfl

/-- The represented Spin image is literally the kernel of the intrinsic
general-Spin similitude. -/
theorem range_cliffordSpinCandidateToCliffordGeneralSpinHom_eq_ker :
    (V.cliffordSpinCandidateToCliffordGeneralSpinHom A).range =
      (CliffordGeneralSpinIntrinsicPoint.similitudeGroupHom V A).ker := by
  rw [← CliffordGeneralSpinIntrinsicPoint.range_ofSpinGroupHom_eq_ker_similitudeGroupHom
    V A]
  ext x
  constructor
  · rintro ⟨F, rfl⟩
    exact ⟨V.cliffordSpinCandidateCoordinateAlgHomMulEquivPointData A F, rfl⟩
  · rintro ⟨d, rfl⟩
    refine ⟨(V.cliffordSpinCandidateCoordinateAlgHomMulEquivPointData A).symm d, ?_⟩
    change CliffordGeneralSpinIntrinsicPoint.ofSpinGroupHom V A
        (V.cliffordSpinCandidateCoordinateAlgHomMulEquivPointData A
          ((V.cliffordSpinCandidateCoordinateAlgHomMulEquivPointData A).symm d)) = _
    rw [MulEquiv.apply_symm_apply]

/-- The represented Spin inclusion commutes with coefficientwise scalar
extension. -/
theorem cliffordSpinCandidateToCliffordGeneralSpinHom_naturality
    {B : Type*} [CommRing B] [Algebra ℚ B]
    (f : A →ₐ[ℚ] B) (x : V.CliffordSpinCandidateGroup A) :
    CliffordGeneralSpinIntrinsicPoint.mapGroupHom V f
        (V.cliffordSpinCandidateToCliffordGeneralSpinHom A x) =
      V.cliffordSpinCandidateToCliffordGeneralSpinHom B
        (V.cliffordSpinCandidateGroupMap f x) := by
  apply CliffordGeneralSpinIntrinsicPoint.ext_cliffordUnit V B
  apply Units.ext
  change V.cliffordCoordinateBaseChangeMap f
      (V.cliffordSpinCandidateCoordinateAlgHomMulEquivIntrinsicPoint A x).1 =
    (V.cliffordSpinCandidateCoordinateAlgHomMulEquivIntrinsicPoint B
      (V.cliffordSpinCandidateGroupMap f x)).1
  simpa only [V.cliffordSpinIntrinsicPointMap_coe] using
    congrArg (fun y : V.CliffordSpinIntrinsicPoint B => y.1)
      (V.cliffordSpinCandidateIntrinsicRecognition_naturality f x).symm

/-- Naturality as an equality of group homomorphisms. -/
theorem cliffordSpinCandidateToCliffordGeneralSpinHom_naturality_hom
    {B : Type*} [CommRing B] [Algebra ℚ B]
    (f : A →ₐ[ℚ] B) :
    (CliffordGeneralSpinIntrinsicPoint.mapGroupHom V f).comp
        (V.cliffordSpinCandidateToCliffordGeneralSpinHom A) =
      (V.cliffordSpinCandidateToCliffordGeneralSpinHom B).comp
        (V.cliffordSpinCandidateGroupMap f) := by
  apply MonoidHom.ext
  intro x
  exact V.cliffordSpinCandidateToCliffordGeneralSpinHom_naturality A f x

/-- The represented Spin inclusion is continuous for the literal finite-
coordinate topologies. -/
theorem continuous_cliffordSpinCandidateToCliffordGeneralSpinHom
    [TopologicalSpace A] [IsTopologicalRing A] :
    Continuous (V.cliffordSpinCandidateToCliffordGeneralSpinHom A) := by
  apply continuous_induced_rng.mpr
  apply Continuous.prodMk
  · apply Continuous.prodMk
    · apply continuous_pi
      intro u
      simpa [cliffordSpinCandidateToCliffordGeneralSpinHom,
        CliffordGeneralSpinIntrinsicPoint.ofSpinGroupHom,
        CliffordGeneralSpinIntrinsicPoint.ofSpin] using
        V.continuous_cliffordSpinCandidateCliffordCoordinate A u
    · exact continuous_const
  · apply Continuous.prodMk
    · apply continuous_pi
      intro i
      apply continuous_pi
      intro j
      simpa [cliffordSpinCandidateToCliffordGeneralSpinHom,
        CliffordGeneralSpinIntrinsicPoint.ofSpinGroupHom,
        CliffordGeneralSpinIntrinsicPoint.ofSpin,
        cliffordSpinCandidateMatrixOfCoordinateAlgHom] using
        V.continuous_cliffordSpinCandidateMatrixCoordinate A i j
    · apply continuous_pi
      intro i
      apply continuous_pi
      intro j
      have h := (V.continuous_cliffordSpinCandidateMatrixCoordinate A i j).comp
        (V.continuous_inv_cliffordSpinCandidateGroup A)
      refine h.congr ?_
      intro x
      change x⁻¹ (V.cliffordSpinCandidateMatrixCoordinate i j) = _
      rw [← V.cliffordSpinCandidatePointDataOfCoordinateAlgHom_matrix_apply]
      change
        (V.cliffordSpinCandidatePointDataOfCoordinateAlgHom A x⁻¹).matrixPoint.1 i j =
          (V.cliffordSpinCandidatePointDataOfCoordinateAlgHom A x).matrixGroup⁻¹.1.1.1 i j
      have hx := map_inv
        (V.cliffordSpinCandidateCoordinateAlgHomMulEquivPointData A) x
      change V.cliffordSpinCandidatePointDataOfCoordinateAlgHom A x⁻¹ =
        (V.cliffordSpinCandidatePointDataOfCoordinateAlgHom A x)⁻¹ at hx
      rw [hx]
      change
        ((V.cliffordSpinCandidatePointDataOfCoordinateAlgHom A x)⁻¹).matrixGroup.1.1.1 i j =
          (V.cliffordSpinCandidatePointDataOfCoordinateAlgHom A x).matrixGroup⁻¹.1.1.1 i j
      rw [CliffordSpinCandidatePointData.inv_matrixGroup]

end RationalQuadraticSpaceMatrix
