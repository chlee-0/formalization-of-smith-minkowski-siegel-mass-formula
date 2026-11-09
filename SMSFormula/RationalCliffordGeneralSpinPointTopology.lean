import SMSFormula.RationalCliffordGeneralSpinNaturality
import SMSFormula.RationalCliffordSpinCandidatePointTopology

/-!
# Finite-coordinate topology on intrinsic general-Spin points

For a topological commutative rational algebra, an intrinsic `GSpin` point is
embedded into its finite Clifford coefficients, scalar similitude, and
special-orthogonal matrix entries.  The induced topology makes multiplication
and inversion continuous.  This is the carrier-specific topological group
needed by the crossed-integral comparison; it introduces no general
algebraic-group interface.
-/

noncomputable section

open scoped Matrix

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

/-- The finite coordinates of an intrinsic general-Spin point. -/
def cliffordGeneralSpinPointCoordinateMap
    (A : Type*) [CommRing A] [Algebra ℚ A] :
    V.CliffordGeneralSpinIntrinsicPoint A →
      ((Finset (Fin n) → A) × Aˣ) ×
        (Matrix (Fin n) (Fin n) A × Matrix (Fin n) (Fin n) A) :=
  fun x =>
    (((V.cliffordCoordinateBaseChangeBasis A).repr
        (x.cliffordUnit : V.cliffordCoordinateBaseChangeAlgebra A),
      x.similitude),
    (x.matrixPoint.1, x.matrixGroup⁻¹.1.1.1))

@[simp]
theorem cliffordGeneralSpinPointCoordinateMap_clifford
    (A : Type*) [CommRing A] [Algebra ℚ A]
    (x : V.CliffordGeneralSpinIntrinsicPoint A) (u : Finset (Fin n)) :
    (V.cliffordGeneralSpinPointCoordinateMap A x).1.1 u =
      (V.cliffordCoordinateBaseChangeBasis A).repr
        (x.cliffordUnit : V.cliffordCoordinateBaseChangeAlgebra A) u :=
  rfl

@[simp]
theorem cliffordGeneralSpinPointCoordinateMap_similitude
    (A : Type*) [CommRing A] [Algebra ℚ A]
    (x : V.CliffordGeneralSpinIntrinsicPoint A) :
    (V.cliffordGeneralSpinPointCoordinateMap A x).1.2 = x.similitude :=
  rfl

@[simp]
theorem cliffordGeneralSpinPointCoordinateMap_matrix
    (A : Type*) [CommRing A] [Algebra ℚ A]
    (x : V.CliffordGeneralSpinIntrinsicPoint A) (i j : Fin n) :
    (V.cliffordGeneralSpinPointCoordinateMap A x).2.1 i j =
      x.matrixPoint.1 i j :=
  rfl

@[simp]
theorem cliffordGeneralSpinPointCoordinateMap_invMatrix
    (A : Type*) [CommRing A] [Algebra ℚ A]
    (x : V.CliffordGeneralSpinIntrinsicPoint A) (i j : Fin n) :
    (V.cliffordGeneralSpinPointCoordinateMap A x).2.2 i j =
      x.matrixGroup⁻¹.1.1.1 i j :=
  rfl

/-- The Clifford coordinates alone determine an intrinsic general-Spin
point, hence the displayed simultaneous coordinate map is injective. -/
theorem cliffordGeneralSpinPointCoordinateMap_injective
    (A : Type*) [CommRing A] [Algebra ℚ A] :
    Function.Injective (V.cliffordGeneralSpinPointCoordinateMap A) := by
  intro x y hxy
  apply CliffordGeneralSpinIntrinsicPoint.ext_cliffordUnit V A
  apply Units.ext
  apply (V.cliffordCoordinateBaseChangeBasis A).repr.injective
  ext u
  simpa only [cliffordGeneralSpinPointCoordinateMap] using
    congrArg (fun z => z.1.1 u) hxy

/-- The natural topology on intrinsic general-Spin points is induced by the
finite Clifford, similitude, and matrix coordinates. -/
noncomputable instance cliffordGeneralSpinIntrinsicPointTopologicalSpace
    (A : Type*) [CommRing A] [Algebra ℚ A] [TopologicalSpace A] :
    TopologicalSpace (V.CliffordGeneralSpinIntrinsicPoint A) :=
  TopologicalSpace.induced
    (V.cliffordGeneralSpinPointCoordinateMap A) inferInstance

theorem cliffordGeneralSpinPointCoordinateMap_isEmbedding
    (A : Type*) [CommRing A] [Algebra ℚ A] [TopologicalSpace A] :
    Topology.IsEmbedding (V.cliffordGeneralSpinPointCoordinateMap A) :=
  (V.cliffordGeneralSpinPointCoordinateMap_injective A).isEmbedding_induced

theorem continuous_cliffordGeneralSpinPointCoordinateMap
    (A : Type*) [CommRing A] [Algebra ℚ A] [TopologicalSpace A] :
    Continuous (V.cliffordGeneralSpinPointCoordinateMap A) :=
  (V.cliffordGeneralSpinPointCoordinateMap_isEmbedding A).continuous

theorem continuous_cliffordGeneralSpinCliffordCoordinate
    (A : Type*) [CommRing A] [Algebra ℚ A] [TopologicalSpace A]
    (u : Finset (Fin n)) :
    Continuous (fun x : V.CliffordGeneralSpinIntrinsicPoint A =>
      (V.cliffordCoordinateBaseChangeBasis A).repr
        (x.cliffordUnit : V.cliffordCoordinateBaseChangeAlgebra A) u) := by
  exact ((continuous_apply u).comp (continuous_fst.comp continuous_fst)).comp
    (V.continuous_cliffordGeneralSpinPointCoordinateMap A)

theorem continuous_cliffordGeneralSpinSimilitude
    (A : Type*) [CommRing A] [Algebra ℚ A] [TopologicalSpace A] :
    Continuous (fun x : V.CliffordGeneralSpinIntrinsicPoint A =>
      x.similitude) := by
  exact (continuous_snd.comp continuous_fst).comp
    (V.continuous_cliffordGeneralSpinPointCoordinateMap A)

theorem continuous_cliffordGeneralSpinMatrixCoordinate
    (A : Type*) [CommRing A] [Algebra ℚ A] [TopologicalSpace A]
    (i j : Fin n) :
    Continuous (fun x : V.CliffordGeneralSpinIntrinsicPoint A =>
      x.matrixPoint.1 i j) := by
  exact ((continuous_apply j).comp ((continuous_apply i).comp
    (continuous_fst.comp continuous_snd))).comp
      (V.continuous_cliffordGeneralSpinPointCoordinateMap A)

theorem continuous_cliffordGeneralSpinInvMatrixCoordinate
    (A : Type*) [CommRing A] [Algebra ℚ A] [TopologicalSpace A]
    (i j : Fin n) :
    Continuous (fun x : V.CliffordGeneralSpinIntrinsicPoint A =>
      x.matrixGroup⁻¹.1.1.1 i j) := by
  exact ((continuous_apply j).comp ((continuous_apply i).comp
    (continuous_snd.comp continuous_snd))).comp
      (V.continuous_cliffordGeneralSpinPointCoordinateMap A)

noncomputable instance cliffordGeneralSpinIntrinsicPointT2Space
    (A : Type*) [CommRing A] [Algebra ℚ A]
    [TopologicalSpace A] [T2Space A] :
    T2Space (V.CliffordGeneralSpinIntrinsicPoint A) :=
  (V.cliffordGeneralSpinPointCoordinateMap_isEmbedding A).t2Space

theorem cliffordGeneralSpinPointCoordinateMap_mul_clifford
    (A : Type*) [CommRing A] [Algebra ℚ A]
    (x y : V.CliffordGeneralSpinIntrinsicPoint A) (u : Finset (Fin n)) :
    (V.cliffordGeneralSpinPointCoordinateMap A (x * y)).1.1 u =
      ∑ s, ∑ t,
        (V.cliffordGeneralSpinPointCoordinateMap A x).1.1 s *
          (V.cliffordGeneralSpinPointCoordinateMap A y).1.1 t *
          algebraMap ℚ A (V.cliffordMulStructureConstant s t u) := by
  change (V.cliffordCoordinateBaseChangeBasis A).repr
      (((x * y).cliffordUnit :
        (V.cliffordCoordinateBaseChangeAlgebra A)ˣ) :
        V.cliffordCoordinateBaseChangeAlgebra A) u = _
  rw [CliffordGeneralSpinIntrinsicPoint.mul_cliffordUnit]
  exact V.cliffordCoordinateBaseChangeBasis_repr_mul A _ _ u

theorem cliffordGeneralSpinPointCoordinateMap_mul_matrix
    (A : Type*) [CommRing A] [Algebra ℚ A]
    (x y : V.CliffordGeneralSpinIntrinsicPoint A) (i j : Fin n) :
    (V.cliffordGeneralSpinPointCoordinateMap A (x * y)).2.1 i j =
      ∑ k,
        (V.cliffordGeneralSpinPointCoordinateMap A x).2.1 i k *
          (V.cliffordGeneralSpinPointCoordinateMap A y).2.1 k j := by
  exact CliffordGeneralSpinIntrinsicPoint.matrixPointMul_apply V A x y i j

theorem cliffordGeneralSpinPointCoordinateMap_mul_invMatrix
    (A : Type*) [CommRing A] [Algebra ℚ A]
    (x y : V.CliffordGeneralSpinIntrinsicPoint A) (i j : Fin n) :
    (V.cliffordGeneralSpinPointCoordinateMap A (x * y)).2.2 i j =
      ∑ k,
        (V.cliffordGeneralSpinPointCoordinateMap A y).2.2 i k *
          (V.cliffordGeneralSpinPointCoordinateMap A x).2.2 k j := by
  simp only [cliffordGeneralSpinPointCoordinateMap,
    CliffordGeneralSpinIntrinsicPoint.mul_matrixGroup]
  rw [mul_inv_rev]
  exact Matrix.mul_apply

theorem continuous_mul_cliffordGeneralSpinIntrinsicPoint
    (A : Type*) [CommRing A] [Algebra ℚ A]
    [TopologicalSpace A] [IsTopologicalRing A] :
    Continuous (fun z : V.CliffordGeneralSpinIntrinsicPoint A ×
      V.CliffordGeneralSpinIntrinsicPoint A => z.1 * z.2) := by
  apply continuous_induced_rng.mpr
  apply Continuous.prodMk
  · apply Continuous.prodMk
    · apply continuous_pi
      intro u
      change Continuous (fun z : V.CliffordGeneralSpinIntrinsicPoint A ×
        V.CliffordGeneralSpinIntrinsicPoint A =>
          (V.cliffordGeneralSpinPointCoordinateMap A (z.1 * z.2)).1.1 u)
      simp_rw [V.cliffordGeneralSpinPointCoordinateMap_mul_clifford A]
      apply continuous_finset_sum
      intro s _
      apply continuous_finset_sum
      intro t _
      exact (((V.continuous_cliffordGeneralSpinCliffordCoordinate A s).comp
        continuous_fst).mul
          ((V.continuous_cliffordGeneralSpinCliffordCoordinate A t).comp
            continuous_snd)).mul continuous_const
    · exact ((V.continuous_cliffordGeneralSpinSimilitude A).comp
        continuous_fst).mul
          ((V.continuous_cliffordGeneralSpinSimilitude A).comp continuous_snd)
  · apply Continuous.prodMk
    · apply continuous_pi
      intro i
      apply continuous_pi
      intro j
      change Continuous (fun z : V.CliffordGeneralSpinIntrinsicPoint A ×
        V.CliffordGeneralSpinIntrinsicPoint A =>
          (V.cliffordGeneralSpinPointCoordinateMap A (z.1 * z.2)).2.1 i j)
      simp_rw [V.cliffordGeneralSpinPointCoordinateMap_mul_matrix A]
      apply continuous_finset_sum
      intro k _
      exact ((V.continuous_cliffordGeneralSpinMatrixCoordinate A i k).comp
        continuous_fst).mul
          ((V.continuous_cliffordGeneralSpinMatrixCoordinate A k j).comp
            continuous_snd)
    · apply continuous_pi
      intro i
      apply continuous_pi
      intro j
      change Continuous (fun z : V.CliffordGeneralSpinIntrinsicPoint A ×
        V.CliffordGeneralSpinIntrinsicPoint A =>
          (V.cliffordGeneralSpinPointCoordinateMap A (z.1 * z.2)).2.2 i j)
      simp_rw [V.cliffordGeneralSpinPointCoordinateMap_mul_invMatrix A]
      apply continuous_finset_sum
      intro k _
      exact ((V.continuous_cliffordGeneralSpinInvMatrixCoordinate A i k).comp
        continuous_snd).mul
          ((V.continuous_cliffordGeneralSpinInvMatrixCoordinate A k j).comp
            continuous_fst)

noncomputable instance cliffordGeneralSpinIntrinsicPointContinuousMul
    (A : Type*) [CommRing A] [Algebra ℚ A]
    [TopologicalSpace A] [IsTopologicalRing A] :
    ContinuousMul (V.CliffordGeneralSpinIntrinsicPoint A) where
  continuous_mul := V.continuous_mul_cliffordGeneralSpinIntrinsicPoint A

/-- The inverse Clifford unit is the reversed unit multiplied by the inverse
similitude. -/
theorem coe_inv_cliffordUnit_eq_inv_similitude_mul_reverse
    (A : Type*) [CommRing A] [Algebra ℚ A]
    (x : V.CliffordGeneralSpinIntrinsicPoint A) :
    ((x.cliffordUnit⁻¹ :
        (V.cliffordCoordinateBaseChangeAlgebra A)ˣ) :
      V.cliffordCoordinateBaseChangeAlgebra A) =
        algebraMap A (V.cliffordCoordinateBaseChangeAlgebra A)
            (x.similitude⁻¹ : Aˣ) *
          V.cliffordCoordinateBaseChangeReverse A
            (x.cliffordUnit : V.cliffordCoordinateBaseChangeAlgebra A) := by
  apply x.cliffordUnit.isUnit.mul_right_cancel
  rw [mul_assoc, CliffordGeneralSpinIntrinsicPoint.reverse_mul_eq]
  rw [← map_mul]
  have hnu : ((x.similitude⁻¹ : Aˣ) : A) * (x.similitude : A) = 1 := by
    exact congrArg Units.val (inv_mul_cancel x.similitude)
  rw [hnu, map_one]
  exact congrArg Units.val (inv_mul_cancel x.cliffordUnit)

theorem cliffordGeneralSpinPointCoordinateMap_inv_clifford
    (A : Type*) [CommRing A] [Algebra ℚ A]
    (x : V.CliffordGeneralSpinIntrinsicPoint A) (u : Finset (Fin n)) :
    (V.cliffordGeneralSpinPointCoordinateMap A x⁻¹).1.1 u =
      (x.similitude⁻¹ : Aˣ) *
        ∑ s, (V.cliffordGeneralSpinPointCoordinateMap A x).1.1 s *
          algebraMap ℚ A (V.cliffordReverseStructureConstant s u) := by
  change (V.cliffordCoordinateBaseChangeBasis A).repr
      (((x⁻¹).cliffordUnit :
        (V.cliffordCoordinateBaseChangeAlgebra A)ˣ) :
        V.cliffordCoordinateBaseChangeAlgebra A) u = _
  rw [CliffordGeneralSpinIntrinsicPoint.inv_cliffordUnit,
    V.coe_inv_cliffordUnit_eq_inv_similitude_mul_reverse A]
  rw [← Algebra.smul_def, map_smul, Finsupp.smul_apply,
    V.cliffordCoordinateBaseChangeBasis_repr_reverse]
  rfl

theorem continuous_inv_cliffordGeneralSpinIntrinsicPoint
    (A : Type*) [CommRing A] [Algebra ℚ A]
    [TopologicalSpace A] [IsTopologicalRing A] :
    Continuous (fun x : V.CliffordGeneralSpinIntrinsicPoint A => x⁻¹) := by
  apply continuous_induced_rng.mpr
  apply Continuous.prodMk
  · apply Continuous.prodMk
    · apply continuous_pi
      intro u
      change Continuous (fun x : V.CliffordGeneralSpinIntrinsicPoint A =>
        (V.cliffordGeneralSpinPointCoordinateMap A x⁻¹).1.1 u)
      simp_rw [V.cliffordGeneralSpinPointCoordinateMap_inv_clifford A]
      exact (Units.continuous_val.comp
        (continuous_inv.comp (V.continuous_cliffordGeneralSpinSimilitude A))).mul
          (continuous_finset_sum _ fun s _ =>
            (V.continuous_cliffordGeneralSpinCliffordCoordinate A s).mul
              continuous_const)
    · exact continuous_inv.comp
        (V.continuous_cliffordGeneralSpinSimilitude A)
  · apply Continuous.prodMk
    · apply continuous_pi
      intro i
      apply continuous_pi
      intro j
      change Continuous (fun x : V.CliffordGeneralSpinIntrinsicPoint A =>
        x⁻¹.matrixPoint.1 i j)
      rw [show (fun x : V.CliffordGeneralSpinIntrinsicPoint A =>
          x⁻¹.matrixPoint.1 i j) =
        fun x => x.matrixGroup⁻¹.1.1.1 i j by
          funext x
          rw [← CliffordGeneralSpinIntrinsicPoint.inv_matrixGroup]
          rfl]
      exact V.continuous_cliffordGeneralSpinInvMatrixCoordinate A i j
    · apply continuous_pi
      intro i
      apply continuous_pi
      intro j
      change Continuous (fun x : V.CliffordGeneralSpinIntrinsicPoint A =>
        x⁻¹.matrixGroup⁻¹.1.1.1 i j)
      rw [show (fun x : V.CliffordGeneralSpinIntrinsicPoint A =>
          x⁻¹.matrixGroup⁻¹.1.1.1 i j) =
        fun x => x.matrixPoint.1 i j by
          funext x
          rw [CliffordGeneralSpinIntrinsicPoint.inv_matrixGroup, inv_inv,
            CliffordGeneralSpinIntrinsicPoint.matrixGroup_coe]]
      exact V.continuous_cliffordGeneralSpinMatrixCoordinate A i j

noncomputable instance cliffordGeneralSpinIntrinsicPointIsTopologicalGroup
    (A : Type*) [CommRing A] [Algebra ℚ A]
    [TopologicalSpace A] [IsTopologicalRing A] :
    IsTopologicalGroup (V.CliffordGeneralSpinIntrinsicPoint A) where
  continuous_mul := V.continuous_mul_cliffordGeneralSpinIntrinsicPoint A
  continuous_inv := V.continuous_inv_cliffordGeneralSpinIntrinsicPoint A

/-- The intrinsic similitude character is continuous. -/
theorem continuous_cliffordGeneralSpinSimilitudeGroupHom
    (A : Type*) [CommRing A] [Algebra ℚ A]
    [TopologicalSpace A] [IsTopologicalRing A] :
    Continuous
      (CliffordGeneralSpinIntrinsicPoint.similitudeGroupHom V A) :=
  V.continuous_cliffordGeneralSpinSimilitude A

/-- The intrinsic projection to the existing special-orthogonal topological
group is continuous. -/
theorem continuous_cliffordGeneralSpinToSpecialOrthogonalGroupHom
    (A : Type*) [CommRing A] [Algebra ℚ A]
    [TopologicalSpace A] [IsTopologicalRing A] :
    Continuous
      (CliffordGeneralSpinIntrinsicPoint.toSpecialOrthogonalGroupHom V A) := by
  apply continuous_induced_rng.mpr
  apply continuous_induced_rng.mpr
  apply Units.continuous_iff.mpr
  constructor
  · apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    exact V.continuous_cliffordGeneralSpinMatrixCoordinate A i j
  · apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    exact V.continuous_cliffordGeneralSpinInvMatrixCoordinate A i j

/-- Clifford scalar extension applies the scalar homomorphism coefficient by
coefficient in the fixed rational Clifford basis. -/
theorem cliffordCoordinateBaseChangeBasis_repr_map
    {A B : Type*} [CommRing A] [CommRing B]
    [Algebra ℚ A] [Algebra ℚ B]
    (f : A →ₐ[ℚ] B)
    (x : V.cliffordCoordinateBaseChangeAlgebra A)
    (u : Finset (Fin n)) :
    (V.cliffordCoordinateBaseChangeBasis B).repr
        (V.cliffordCoordinateBaseChangeMap f x) u =
      f ((V.cliffordCoordinateBaseChangeBasis A).repr x u) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy =>
      simp only [map_add, Finsupp.add_apply, hx, hy]
  | tmul a x =>
      simp [V.cliffordCoordinateBaseChangeMap_tmul,
        cliffordCoordinateBaseChangeBasis,
        Module.Basis.baseChange_repr_tmul]

/-- Scalar extension is continuous for the finite-coordinate intrinsic
general-Spin topologies whenever the scalar homomorphism is continuous. -/
theorem continuous_cliffordGeneralSpinMapGroupHom
    {A B : Type*} [CommRing A] [CommRing B]
    [Algebra ℚ A] [Algebra ℚ B]
    [TopologicalSpace A] [TopologicalSpace B]
    [IsTopologicalRing A] [IsTopologicalRing B]
    (f : A →ₐ[ℚ] B) (hf : Continuous f) :
    Continuous (CliffordGeneralSpinIntrinsicPoint.mapGroupHom V f) := by
  have hunits : Continuous (Units.map f.toMonoidHom) :=
    hf.units_map f.toMonoidHom
  apply continuous_induced_rng.mpr
  apply Continuous.prodMk
  · apply Continuous.prodMk
    · apply continuous_pi
      intro u
      change Continuous (fun x : V.CliffordGeneralSpinIntrinsicPoint A =>
        (V.cliffordCoordinateBaseChangeBasis B).repr
          ((CliffordGeneralSpinIntrinsicPoint.map V f x).cliffordUnit :
            V.cliffordCoordinateBaseChangeAlgebra B) u)
      simp_rw [CliffordGeneralSpinIntrinsicPoint.map_cliffordUnit_coe,
        V.cliffordCoordinateBaseChangeBasis_repr_map f]
      exact hf.comp (V.continuous_cliffordGeneralSpinCliffordCoordinate A u)
    · exact hunits.comp (V.continuous_cliffordGeneralSpinSimilitude A)
  · apply Continuous.prodMk
    · apply continuous_pi
      intro i
      apply continuous_pi
      intro j
      change Continuous (fun x : V.CliffordGeneralSpinIntrinsicPoint A =>
        f (x.matrixPoint.1 i j))
      exact hf.comp (V.continuous_cliffordGeneralSpinMatrixCoordinate A i j)
    · apply continuous_pi
      intro i
      apply continuous_pi
      intro j
      change Continuous (fun x : V.CliffordGeneralSpinIntrinsicPoint A =>
        ((CliffordGeneralSpinIntrinsicPoint.map V f x).matrixGroup⁻¹.1.1.1 i j))
      rw [show (fun x : V.CliffordGeneralSpinIntrinsicPoint A =>
          ((CliffordGeneralSpinIntrinsicPoint.map V f x).matrixGroup⁻¹.1.1.1 i j)) =
        fun x => f (x.matrixGroup⁻¹.1.1.1 i j) by
          funext x
          have hmap := DFunLike.congr_fun
            (CliffordGeneralSpinIntrinsicPoint.toSpecialOrthogonal_naturality
              V f) x
          change V.specialOrthogonalMatrixGroupMap f x.matrixGroup =
            (CliffordGeneralSpinIntrinsicPoint.map V f x).matrixGroup at hmap
          rw [← hmap, ← map_inv]
          rfl]
      exact hf.comp
        (V.continuous_cliffordGeneralSpinInvMatrixCoordinate A i j)

/-- Clifford coordinates of the central scalar copy are scalar multiples of
the rational Clifford identity coordinates. -/
theorem cliffordCoordinateBaseChangeBasis_repr_algebraMap
    (A : Type*) [CommRing A] [Algebra ℚ A]
    (a : A) (u : Finset (Fin n)) :
    (V.cliffordCoordinateBaseChangeBasis A).repr
        (algebraMap A (V.cliffordCoordinateBaseChangeAlgebra A) a) u =
      a * algebraMap ℚ A (V.cliffordCoordinateBasis.repr 1 u) := by
  rw [Algebra.TensorProduct.algebraMap_apply]
  simp [cliffordCoordinateBaseChangeBasis,
    Module.Basis.baseChange_repr_tmul, Algebra.smul_def, mul_comm]

@[simp]
theorem cliffordGeneralSpin_ofScalar_matrixGroup
    (A : Type*) [CommRing A] [Algebra ℚ A] (z : Aˣ) :
    (CliffordGeneralSpinIntrinsicPoint.ofScalar V A z).matrixGroup = 1 := by
  exact (V.specialOrthogonalMatrixPointEquivGroup A).apply_symm_apply 1

/-- The central scalar inclusion `G_m → GSpin` is continuous. -/
theorem continuous_cliffordGeneralSpinScalarGroupHom
    (A : Type*) [CommRing A] [Algebra ℚ A]
    [TopologicalSpace A] [IsTopologicalRing A] :
    Continuous (CliffordGeneralSpinIntrinsicPoint.scalarGroupHom V A) := by
  apply continuous_induced_rng.mpr
  apply Continuous.prodMk
  · apply Continuous.prodMk
    · apply continuous_pi
      intro u
      change Continuous (fun z : Aˣ =>
        (V.cliffordCoordinateBaseChangeBasis A).repr
          (algebraMap A (V.cliffordCoordinateBaseChangeAlgebra A) (z : A)) u)
      simp_rw [V.cliffordCoordinateBaseChangeBasis_repr_algebraMap A]
      exact Units.continuous_val.mul continuous_const
    · change Continuous (fun z : Aˣ => z ^ 2)
      fun_prop
  · apply Continuous.prodMk
    · change Continuous (fun _ : Aˣ =>
        (V.cliffordSpinCandidateMatrixPointOne A).1)
      exact continuous_const
    · rw [show (fun z : Aˣ =>
          ((CliffordGeneralSpinIntrinsicPoint.scalarGroupHom V A z).matrixGroup⁻¹
            : V.specialOrthogonalMatrixGroup A).1.1.1) =
        fun _ : Aˣ => ((1 : V.specialOrthogonalMatrixGroup A)⁻¹).1.1.1 by
          funext z
          change ((CliffordGeneralSpinIntrinsicPoint.ofScalar V A z).matrixGroup⁻¹
            : V.specialOrthogonalMatrixGroup A).1.1.1 = _
          rw [V.cliffordGeneralSpin_ofScalar_matrixGroup]]
      exact continuous_const

end RationalQuadraticSpaceMatrix
