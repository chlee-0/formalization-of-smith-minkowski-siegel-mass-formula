import SMSFormula.RationalCliffordSpinCandidateCanonicalTensorWitness

/-!
# Trace descent for the Spin-candidate involution

The nontrivial scalar kernel point acts by negation on every Clifford
coordinate and fixes every special-orthogonal matrix coordinate. This file
packages its fixed elements as an `O(SO)`-subalgebra and proves that the
involution trace always lands there.

The existence of the linear trace descent required for rank-two
faithful flatness is proved equivalent to surjectivity of the
canonical map from `O(SO)` onto this fixed subalgebra. Thus
effectivity reduces to an invariant-ring equality; it is not an implicit
consequence of scheme surjectivity or the split torsor canonical map.
-/
noncomputable section

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000

open RationalTamagawa

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

theorem negOneKernelPoint_pointData :
    V.cliffordSpinCandidatePointDataOfCoordinateAlgHom
        V.cliffordSpinCandidateCoordinateRing
        V.cliffordSpinCandidateNegOneKernelPoint =
      V.cliffordSpinCandidatePointDataOfRootOfUnity
        V.cliffordSpinCandidateCoordinateRing
        (negOneRootOfUnity V.cliffordSpinCandidateCoordinateRing) := by
  have h :=
    (V.cliffordSpinCandidateCoordinateKernelMulEquivPointDataKernel
      V.cliffordSpinCandidateCoordinateRing).apply_symm_apply
        ((V.rootsOfUnityMulEquivCliffordSpinCandidatePointDataKernel
          V.cliffordSpinCandidateCoordinateRing)
            (negOneRootOfUnity V.cliffordSpinCandidateCoordinateRing))
  exact congrArg (fun d => d.1) h

theorem negOneCoordinateEnd_cliffordCoordinate (s : Finset (Fin n)) :
    V.cliffordSpinCandidateNegOneCoordinateEnd
        (V.cliffordSpinCandidateCliffordCoordinate s) =
      -V.cliffordSpinCandidateCliffordCoordinate s := by
  letI : Group (V.cliffordSpinCandidateCoordinateRing →ₐ[ℚ]
      V.cliffordSpinCandidateCoordinateRing) :=
    V.cliffordSpinCandidateCoordinateAlgHomGroup
      V.cliffordSpinCandidateCoordinateRing
  letI : Monoid (V.cliffordSpinCandidateCoordinateRing →ₐ[ℚ]
      V.cliffordSpinCandidateCoordinateRing) :=
    (V.cliffordSpinCandidateCoordinateAlgHomGroup
      V.cliffordSpinCandidateCoordinateRing).toMonoid
  have hmul :
      V.cliffordSpinCandidateCoordinateAlgHomMulEquivPointData
          V.cliffordSpinCandidateCoordinateRing
          V.cliffordSpinCandidateNegOneCoordinateEnd =
        V.cliffordSpinCandidateCoordinateAlgHomMulEquivPointData
            V.cliffordSpinCandidateCoordinateRing
            (AlgHom.id ℚ V.cliffordSpinCandidateCoordinateRing) *
          V.cliffordSpinCandidateCoordinateAlgHomMulEquivPointData
            V.cliffordSpinCandidateCoordinateRing
            V.cliffordSpinCandidateNegOneKernelPoint := by
    rw [show V.cliffordSpinCandidateNegOneCoordinateEnd =
      (V.cliffordSpinCandidateCoordinateAlgHomGroup
        V.cliffordSpinCandidateCoordinateRing).mul
          (AlgHom.id ℚ V.cliffordSpinCandidateCoordinateRing)
          V.cliffordSpinCandidateNegOneKernelPoint by rfl]
    exact (V.cliffordSpinCandidateCoordinateAlgHomMulEquivPointData
      V.cliffordSpinCandidateCoordinateRing).map_mul _ _
  rw [← V.cliffordSpinCandidatePointDataOfCoordinateAlgHom_clifford_repr]
  rw [show V.cliffordSpinCandidatePointDataOfCoordinateAlgHom
      V.cliffordSpinCandidateCoordinateRing
      V.cliffordSpinCandidateNegOneCoordinateEnd =
      V.cliffordSpinCandidatePointDataOfCoordinateAlgHom
          V.cliffordSpinCandidateCoordinateRing
          (AlgHom.id ℚ V.cliffordSpinCandidateCoordinateRing) *
        V.cliffordSpinCandidatePointDataOfCoordinateAlgHom
          V.cliffordSpinCandidateCoordinateRing
          V.cliffordSpinCandidateNegOneKernelPoint by exact hmul]
  rw [CliffordSpinCandidatePointData.mul_clifford]
  rw [V.negOneKernelPoint_pointData]
  change (V.cliffordCoordinateBaseChangeBasis
      V.cliffordSpinCandidateCoordinateRing).repr
      ((V.cliffordSpinCandidatePointDataOfCoordinateAlgHom
        V.cliffordSpinCandidateCoordinateRing
        (AlgHom.id ℚ V.cliffordSpinCandidateCoordinateRing)).clifford *
        algebraMap V.cliffordSpinCandidateCoordinateRing
          (V.cliffordCoordinateBaseChangeAlgebra
            V.cliffordSpinCandidateCoordinateRing) (-1)) s = _
  rw [← Algebra.commutes (-1), ← Algebra.smul_def, map_smul]
  simp only [neg_smul, one_smul]
  change -((V.cliffordCoordinateBaseChangeBasis
      V.cliffordSpinCandidateCoordinateRing).repr
        (V.cliffordSpinCandidatePointDataOfCoordinateAlgHom
          V.cliffordSpinCandidateCoordinateRing
          (AlgHom.id ℚ V.cliffordSpinCandidateCoordinateRing)).clifford s) = _
  rw [V.cliffordSpinCandidatePointDataOfCoordinateAlgHom_clifford_repr]
  rfl

theorem negOneCoordinateEnd_matrixCoordinate (i j : Fin n) :
    V.cliffordSpinCandidateNegOneCoordinateEnd
        (V.cliffordSpinCandidateMatrixCoordinate i j) =
      V.cliffordSpinCandidateMatrixCoordinate i j := by
  letI : Group (V.cliffordSpinCandidateCoordinateRing →ₐ[ℚ]
      V.cliffordSpinCandidateCoordinateRing) :=
    V.cliffordSpinCandidateCoordinateAlgHomGroup
      V.cliffordSpinCandidateCoordinateRing
  letI : Monoid (V.cliffordSpinCandidateCoordinateRing →ₐ[ℚ]
      V.cliffordSpinCandidateCoordinateRing) :=
    (V.cliffordSpinCandidateCoordinateAlgHomGroup
      V.cliffordSpinCandidateCoordinateRing).toMonoid
  have hmul :
      V.cliffordSpinCandidateCoordinateAlgHomMulEquivPointData
          V.cliffordSpinCandidateCoordinateRing
          V.cliffordSpinCandidateNegOneCoordinateEnd =
        V.cliffordSpinCandidateCoordinateAlgHomMulEquivPointData
            V.cliffordSpinCandidateCoordinateRing
            (AlgHom.id ℚ V.cliffordSpinCandidateCoordinateRing) *
          V.cliffordSpinCandidateCoordinateAlgHomMulEquivPointData
            V.cliffordSpinCandidateCoordinateRing
            V.cliffordSpinCandidateNegOneKernelPoint := by
    rw [show V.cliffordSpinCandidateNegOneCoordinateEnd =
      (V.cliffordSpinCandidateCoordinateAlgHomGroup
        V.cliffordSpinCandidateCoordinateRing).mul
          (AlgHom.id ℚ V.cliffordSpinCandidateCoordinateRing)
          V.cliffordSpinCandidateNegOneKernelPoint by rfl]
    exact (V.cliffordSpinCandidateCoordinateAlgHomMulEquivPointData
      V.cliffordSpinCandidateCoordinateRing).map_mul _ _
  rw [← V.cliffordSpinCandidatePointDataOfCoordinateAlgHom_matrix_apply]
  rw [show V.cliffordSpinCandidatePointDataOfCoordinateAlgHom
      V.cliffordSpinCandidateCoordinateRing
      V.cliffordSpinCandidateNegOneCoordinateEnd =
      V.cliffordSpinCandidatePointDataOfCoordinateAlgHom
          V.cliffordSpinCandidateCoordinateRing
          (AlgHom.id ℚ V.cliffordSpinCandidateCoordinateRing) *
        V.cliffordSpinCandidatePointDataOfCoordinateAlgHom
          V.cliffordSpinCandidateCoordinateRing
          V.cliffordSpinCandidateNegOneKernelPoint by exact hmul]
  rw [CliffordSpinCandidatePointData.mul_matrixPoint]
  rw [V.negOneKernelPoint_pointData]
  let d := V.cliffordSpinCandidatePointDataOfCoordinateAlgHom
    V.cliffordSpinCandidateCoordinateRing
    (AlgHom.id ℚ V.cliffordSpinCandidateCoordinateRing)
  let k := V.cliffordSpinCandidatePointDataOfRootOfUnity
    V.cliffordSpinCandidateCoordinateRing
    (negOneRootOfUnity V.cliffordSpinCandidateCoordinateRing)
  calc
    (V.cliffordSpinCandidateMatrixPointMul
        V.cliffordSpinCandidateCoordinateRing d k).1 i j =
        (d.matrixGroup * k.matrixGroup).1.1.1 i j := rfl
    _ = d.matrixGroup.1.1.1 i j := by rw [V.cliffordSpinCandidatePointDataOfRootOfUnity_matrixGroup, mul_one]
    _ = d.matrixPoint.1 i j := by rw [CliffordSpinCandidatePointData.matrixGroup_coe]
    _ = V.cliffordSpinCandidateMatrixCoordinate i j := by
      exact V.cliffordSpinCandidatePointDataOfCoordinateAlgHom_matrix_apply
        V.cliffordSpinCandidateCoordinateRing
        (AlgHom.id ℚ V.cliffordSpinCandidateCoordinateRing) i j

def negOneInvariantSubalgebra : Subalgebra
    V.specialOrthogonalCoordinateRing
    V.cliffordSpinCandidateCoordinateRing where
  carrier := {b | V.cliffordSpinCandidateNegOneCoordinateAlgEquiv b = b}
  mul_mem' := by
    intro x y hx hy
    change V.cliffordSpinCandidateNegOneCoordinateAlgEquiv (x * y) = x * y
    rw [map_mul, hx, hy]
  one_mem' := map_one _
  add_mem' := by
    intro x y hx hy
    change V.cliffordSpinCandidateNegOneCoordinateAlgEquiv (x + y) = x + y
    rw [map_add, hx, hy]
  zero_mem' := map_zero _
  algebraMap_mem' := by
    intro a
    exact V.cliffordSpinCandidateNegOneCoordinateAlgEquiv.commutes a

theorem negOne_trace_invariant (b : V.cliffordSpinCandidateCoordinateRing) :
    V.cliffordSpinCandidateNegOneCoordinateAlgEquiv
        (b + V.cliffordSpinCandidateNegOneCoordinateAlgEquiv b) =
      b + V.cliffordSpinCandidateNegOneCoordinateAlgEquiv b := by
  rw [map_add]
  have hself := DFunLike.congr_fun
    V.cliffordSpinCandidateNegOneCoordinateAlgHom_comp_self b
  change V.cliffordSpinCandidateNegOneCoordinateAlgEquiv
      (V.cliffordSpinCandidateNegOneCoordinateAlgEquiv b) = b at hself
  change V.cliffordSpinCandidateNegOneCoordinateAlgEquiv b +
      V.cliffordSpinCandidateNegOneCoordinateAlgEquiv
        (V.cliffordSpinCandidateNegOneCoordinateAlgEquiv b) = _
  rw [hself]
  exact add_comm _ _

def negOneTraceToInvariantLinearMap :
    V.cliffordSpinCandidateCoordinateRing →ₗ[
      V.specialOrthogonalCoordinateRing] V.negOneInvariantSubalgebra :=
  (((LinearMap.id : V.cliffordSpinCandidateCoordinateRing →ₗ[
      V.specialOrthogonalCoordinateRing]
      V.cliffordSpinCandidateCoordinateRing) +
      V.cliffordSpinCandidateNegOneCoordinateAlgEquiv.toLinearMap).codRestrict
    V.negOneInvariantSubalgebra.toSubmodule
    (fun b => V.negOne_trace_invariant b))

@[simp] theorem negOneTraceToInvariantLinearMap_apply
    (b : V.cliffordSpinCandidateCoordinateRing) :
    (V.negOneTraceToInvariantLinearMap b).1 =
      b + V.cliffordSpinCandidateNegOneCoordinateAlgEquiv b := by rfl

def specialOrthogonalToNegOneInvariantAlgHom :
    V.specialOrthogonalCoordinateRing →ₐ[
      V.specialOrthogonalCoordinateRing] V.negOneInvariantSubalgebra where
  toFun a := ⟨algebraMap V.specialOrthogonalCoordinateRing
    V.cliffordSpinCandidateCoordinateRing a,
      V.cliffordSpinCandidateNegOneCoordinateAlgEquiv.commutes a⟩
  map_one' := by ext; simp
  map_mul' := by intro x y; ext; simp
  map_zero' := by ext; simp
  map_add' := by intro x y; ext; simp
  commutes' := by intro a; rfl

theorem specialOrthogonalToNegOneInvariantAlgHom_injective :
    Function.Injective V.specialOrthogonalToNegOneInvariantAlgHom := by
  intro a b hab
  apply V.specialOrthogonalToCliffordSpinCandidateCoordinateRingHom_injective
  exact congrArg Subtype.val hab

noncomputable def negOneInvariantToSpecialOrthogonalLinearMap
    (h : Function.Surjective V.specialOrthogonalToNegOneInvariantAlgHom) :
    V.negOneInvariantSubalgebra →ₗ[
      V.specialOrthogonalCoordinateRing] V.specialOrthogonalCoordinateRing :=
  (LinearEquiv.ofBijective
    V.specialOrthogonalToNegOneInvariantAlgHom.toLinearMap
    ⟨V.specialOrthogonalToNegOneInvariantAlgHom_injective, h⟩).symm.toLinearMap

noncomputable def rankTwoTraceDescentDataOfInvariantSurjective
    (h : Function.Surjective V.specialOrthogonalToNegOneInvariantAlgHom) :
    V.CliffordSpinCandidateRankTwoTraceDescentData where
  trace := (V.negOneInvariantToSpecialOrthogonalLinearMap h).comp
    V.negOneTraceToInvariantLinearMap
  trace_spec b := by
    let e := LinearEquiv.ofBijective
      V.specialOrthogonalToNegOneInvariantAlgHom.toLinearMap
      ⟨V.specialOrthogonalToNegOneInvariantAlgHom_injective, h⟩
    have he := e.apply_symm_apply (V.negOneTraceToInvariantLinearMap b)
    exact (congrArg Subtype.val he).trans
      (V.negOneTraceToInvariantLinearMap_apply b)

theorem specialOrthogonalToNegOneInvariantAlgHom_surjective_of_traceDescentData
    (D : V.CliffordSpinCandidateRankTwoTraceDescentData) :
    Function.Surjective V.specialOrthogonalToNegOneInvariantAlgHom := by
  intro b
  let x : V.cliffordSpinCandidateCoordinateRing := (2 : ℚ)⁻¹ • (b :
    V.cliffordSpinCandidateCoordinateRing)
  refine ⟨D.trace x, ?_⟩
  apply Subtype.ext
  change algebraMap V.specialOrthogonalCoordinateRing
      V.cliffordSpinCandidateCoordinateRing (D.trace x) = b.1
  rw [D.trace_spec]
  change (2 : ℚ)⁻¹ • b.1 +
      V.cliffordSpinCandidateNegOneCoordinateAlgEquiv ((2 : ℚ)⁻¹ • b.1) = b.1
  have hs : V.cliffordSpinCandidateNegOneCoordinateAlgEquiv
      ((2 : ℚ)⁻¹ • b.1) =
      (2 : ℚ)⁻¹ •
        V.cliffordSpinCandidateNegOneCoordinateAlgEquiv b.1 := by
    change V.cliffordSpinCandidateNegOneCoordinateEnd ((2 : ℚ)⁻¹ • b.1) = _
    exact map_smul V.cliffordSpinCandidateNegOneCoordinateEnd _ _
  rw [hs, b.2, ← add_smul]
  norm_num

theorem nonempty_rankTwoTraceDescentData_iff_invariant_surjective :
    Nonempty V.CliffordSpinCandidateRankTwoTraceDescentData ↔
      Function.Surjective V.specialOrthogonalToNegOneInvariantAlgHom := by
  constructor
  · rintro ⟨D⟩
    exact V.specialOrthogonalToNegOneInvariantAlgHom_surjective_of_traceDescentData D
  · intro h
    exact ⟨V.rankTwoTraceDescentDataOfInvariantSurjective h⟩

theorem faithfullyFlat_of_negOneInvariant_surjective
    (h : Function.Surjective V.specialOrthogonalToNegOneInvariantAlgHom) :
    V.specialOrthogonalToCliffordSpinCandidateCoordinateAlgHom.toRingHom.FaithfullyFlat :=
  V.faithfullyFlat_of_rankTwoTraceDescentData
    (V.rankTwoTraceDescentDataOfInvariantSurjective h)

end RationalQuadraticSpaceMatrix
