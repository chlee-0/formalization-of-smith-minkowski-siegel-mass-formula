import SMSFormula.CliffordEvenCentralizer
import SMSFormula.ExteriorAlgebraJointContractionKernel
import SMSFormula.CliffordSpinAction
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import SMSFormula.RationalCliffordSpinMatrixAction
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# The rational Spin kernel as an even Clifford centralizer

This file identifies the kernel of the rational Spin-to-special-orthogonal
representation. Membership in the matrix-representation kernel is first
proved equivalent to either of the following intrinsic conditions:

* the Spin element commutes with every Clifford vector;
* every left contraction of the Spin element vanishes.

The second equivalence uses nonsingularity of the rational form matrix to make
the associated bilinear form an equivalence with the linear dual. The Euler-
operator theorem in `ExteriorAlgebraJointContractionKernel` then proves that
the joint kernel consists of scalars. In positive rank the negative scalar is
constructed as an actual Spin element, giving a multiplicative equivalence
between rational square roots of one and the kernel.
-/

noncomputable section

open CliffordAlgebra MulAction
open scoped Matrix

namespace spinGroup

variable {R M : Type*} [CommRing R]
variable [AddCommGroup M] [Module R M]
variable {Q : QuadraticForm R M}

/-- If the quadratic form represents a unit, then the scalar `-1` belongs to
the Spin group.  Indeed, for a unit vector `m`, both `ι(m)` and `ι(-m)`
are Lipschitz generators, and their quotient is `-1`. -/
theorem neg_one_mem_of_exists_isUnit
    (hQ : ∃ m : M, IsUnit (Q m)) :
    (-1 : CliffordAlgebra Q) ∈ spinGroup Q := by
  obtain ⟨m, hm⟩ := hQ
  obtain ⟨u, hu⟩ := CliffordAlgebra.isUnit_ι_of_isUnit Q hm
  have hu_gen :
      u ∈ ((↑) ⁻¹' Set.range (CliffordAlgebra.ι Q) :
        Set (CliffordAlgebra Q)ˣ) := by
    exact ⟨m, hu.symm⟩
  have hneg_gen :
      -u ∈ ((↑) ⁻¹' Set.range (CliffordAlgebra.ι Q) :
        Set (CliffordAlgebra Q)ˣ) := by
    refine ⟨-m, ?_⟩
    simp only [map_neg]
    rw [← hu]
    rfl
  have hu_lip : u ∈ lipschitzGroup Q := Subgroup.subset_closure hu_gen
  have hneg_lip : -u ∈ lipschitzGroup Q := Subgroup.subset_closure hneg_gen
  have hminus_lip : (-1 : (CliffordAlgebra Q)ˣ) ∈ lipschitzGroup Q := by
    have hprod := mul_mem hneg_lip (inv_mem hu_lip)
    simpa using hprod
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · exact lipschitzGroup.coe_mem_iff_mem.mpr hminus_lip
  · constructor <;> simp
  · simp

end spinGroup

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

/-- Nonsingularity of the stored form matrix makes the associated bilinear
form of `V.quadraticForm` nondegenerate. -/
theorem quadraticForm_associated_nondegenerate
    (V : RationalQuadraticSpaceMatrix n) :
    V.quadraticForm.associated.Nondegenerate := by
  apply LinearMap.BilinForm.nondegenerate_toMatrix'_iff.mp
  change V.quadraticForm.toMatrix'.Nondegenerate
  rw [V.quadraticForm_toMatrix']
  exact Matrix.nondegenerate_iff_det_ne_zero.mpr V.form_det_ne_zero

/-- In positive rank, a nonsingular rational quadratic form represents a
nonzero rational number, hence a unit. -/
theorem exists_isUnit_quadraticForm [NeZero n]
    (V : RationalQuadraticSpaceMatrix n) :
    ∃ m : Fin n → ℚ, IsUnit (V.quadraticForm m) := by
  have hBne : V.quadraticForm.associated ≠ 0 :=
    LinearMap.BilinForm.Nondegenerate.ne_zero
      V.quadraticForm_associated_nondegenerate
  obtain ⟨m, hm⟩ := LinearMap.BilinForm.exists_bilinForm_self_ne_zero
    hBne (V.quadraticForm.associated_isSymm (S := ℕ))
  refine ⟨m, (isUnit_iff_ne_zero.mpr ?_)⟩
  rwa [← V.quadraticForm.associated_eq_self_apply ℕ m]

/-- The negative scalar is an actual rational Spin element in positive
rank. -/
theorem neg_one_mem_spinGroup [NeZero n]
    (V : RationalQuadraticSpaceMatrix n) :
    (-1 : CliffordAlgebra V.quadraticForm) ∈ spinGroup V.quadraticForm :=
  spinGroup.neg_one_mem_of_exists_isUnit V.exists_isUnit_quadraticForm

/-- Every rational square root of one maps to a Spin scalar in positive
rank. -/
theorem algebraMap_mem_spinGroup_of_mem_rootsOfUnity_two [NeZero n]
    (V : RationalQuadraticSpaceMatrix n) (z : rootsOfUnity 2 ℚ) :
    algebraMap ℚ (CliffordAlgebra V.quadraticForm) ((z : ℚˣ) : ℚ) ∈
      spinGroup V.quadraticForm := by
  have hz : (((z : ℚˣ) : ℚ) ^ 2) = 1 :=
    (mem_rootsOfUnity' 2 (z : ℚˣ)).mp z.property
  rcases sq_eq_one_iff.mp hz with hz | hz
  · simp [hz]
  · simpa [hz] using V.neg_one_mem_spinGroup

/-- Scalar inclusion of rational `μ₂` into the Spin group. -/
def rationalMuTwoToSpin [NeZero n]
    (V : RationalQuadraticSpaceMatrix n) :
    rootsOfUnity 2 ℚ →* spinGroup V.quadraticForm where
  toFun z := ⟨algebraMap ℚ (CliffordAlgebra V.quadraticForm) ((z : ℚˣ) : ℚ),
    V.algebraMap_mem_spinGroup_of_mem_rootsOfUnity_two z⟩
  map_one' := by
    apply Subtype.ext
    simp
  map_mul' z w := by
    apply Subtype.ext
    simp

/-- The coefficient of a scalar Spin element has square one. -/
theorem sq_eq_one_of_spin_eq_algebraMap
    (V : RationalQuadraticSpaceMatrix n)
    (x : spinGroup V.quadraticForm) (r : ℚ)
    (hx : (x : CliffordAlgebra V.quadraticForm) =
      algebraMap ℚ (CliffordAlgebra V.quadraticForm) r) :
    r ^ 2 = 1 := by
  apply (algebraMap ℚ (CliffordAlgebra V.quadraticForm)).injective
  rw [map_pow, map_one, pow_two]
  calc
    algebraMap ℚ (CliffordAlgebra V.quadraticForm) r *
          algebraMap ℚ (CliffordAlgebra V.quadraticForm) r =
        star (x : CliffordAlgebra V.quadraticForm) *
          (x : CliffordAlgebra V.quadraticForm) := by
            rw [hx, CliffordAlgebra.star_algebraMap]
    _ = 1 := spinGroup.star_mul_self_of_mem x.property

/-- Scalar Spin elements have coefficient `1` or `-1`. -/
theorem eq_one_or_neg_one_of_spin_eq_algebraMap
    (V : RationalQuadraticSpaceMatrix n)
    (x : spinGroup V.quadraticForm) (r : ℚ)
    (hx : (x : CliffordAlgebra V.quadraticForm) =
      algebraMap ℚ (CliffordAlgebra V.quadraticForm) r) :
    r = 1 ∨ r = -1 :=
  sq_eq_one_iff.mp (V.sq_eq_one_of_spin_eq_algebraMap x r hx)

end RationalQuadraticSpaceMatrix
