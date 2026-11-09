import Mathlib.LinearAlgebra.CliffordAlgebra.SpinGroup
import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
import Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv

/-!
# The Clifford conjugation action of the Spin group

Mathlib defines `spinGroup Q` and proves that Clifford conjugation preserves
the range of the canonical vector map `CliffordAlgebra.ι Q`, but it does not
package the induced action on the original quadratic module.  This file builds
that first layer of the central Spin cover.

When two is invertible, the module equivalence between a Clifford algebra and
the exterior algebra proves that `CliffordAlgebra.ι Q` is injective.  We use
the resulting equivalence with its range to transport Clifford conjugation
back to the quadratic module.  The Clifford relation

```text
ι(m)^2 = Q(m)
```

then proves that every transported automorphism preserves `Q`.  Finally, the
construction is packaged both as a `QuadraticMap.IsometryEquiv` for each Spin
element and as a multiplicative linear representation.

This is only the action layer.  Determinant one, the central `mu_2` kernel,
surjectivity onto the special orthogonal group, and scalar base change are
handled in separate modules.
-/

noncomputable section

open CliffordAlgebra MulAction

namespace CliffordAlgebra

variable {R M : Type*} [CommRing R]
variable [AddCommGroup M] [Module R M]
variable (Q : QuadraticForm R M) [Invertible (2 : R)]

/-- In characteristic different from two, the canonical vector map into the
Clifford algebra is injective. -/
theorem ι_injective_of_invertible_two : Function.Injective (ι Q) := by
  intro x y hxy
  have h := congrArg (equivExterior Q) hxy
  have h' : ExteriorAlgebra.ι R x = ExteriorAlgebra.ι R y := by
    simpa [equivExterior] using h
  exact (ExteriorAlgebra.ι_inj R x y).mp h'

/-- The canonical vector map as a linear equivalence onto its range. -/
noncomputable def ιEquivRange : M ≃ₗ[R] LinearMap.range (ι Q) :=
  LinearEquiv.ofInjective (ι Q) (ι_injective_of_invertible_two Q)

end CliffordAlgebra

namespace spinGroup

variable {R M : Type*} [Field R]
variable [AddCommGroup M] [Module R M]
variable (Q : QuadraticForm R M) [Invertible (2 : R)]

/-- Clifford conjugation restricted to the vector range. -/
noncomputable def conjugationRangeLinearEquiv (x : spinGroup Q) :
    LinearMap.range (CliffordAlgebra.ι Q) ≃ₗ[R]
      LinearMap.range (CliffordAlgebra.ι Q) where
  toFun z :=
    ⟨ConjAct.toConjAct (toUnits x) • (z : CliffordAlgebra Q), by
      obtain ⟨m, hm⟩ := z.property
      rw [← hm]
      apply conjAct_smul_ι_mem_range_ι
      change (x : CliffordAlgebra Q) ∈ spinGroup Q
      exact x.property⟩
  invFun z :=
    ⟨ConjAct.toConjAct (toUnits x⁻¹) • (z : CliffordAlgebra Q), by
      obtain ⟨m, hm⟩ := z.property
      rw [← hm]
      apply conjAct_smul_ι_mem_range_ι
      change ((x⁻¹ : spinGroup Q) : CliffordAlgebra Q) ∈ spinGroup Q
      exact (x⁻¹).property⟩
  left_inv z := by
    apply Subtype.ext
    change ConjAct.toConjAct (toUnits x⁻¹) •
      (ConjAct.toConjAct (toUnits x) • (z : CliffordAlgebra Q)) = z
    rw [← mul_smul, ← map_mul]
    simp
  right_inv z := by
    apply Subtype.ext
    change ConjAct.toConjAct (toUnits x) •
      (ConjAct.toConjAct (toUnits x⁻¹) • (z : CliffordAlgebra Q)) = z
    rw [← mul_smul, ← map_mul]
    simp
  map_add' z w := by
    apply Subtype.ext
    exact smul_add _ _ _
  map_smul' r z := by
    apply Subtype.ext
    exact smul_comm _ _ _

/-- The linear automorphism of the quadratic module induced by a Spin
element. -/
noncomputable def conjugationLinearEquiv (x : spinGroup Q) : M ≃ₗ[R] M :=
  (CliffordAlgebra.ιEquivRange Q).trans
    ((conjugationRangeLinearEquiv Q x).trans
      (CliffordAlgebra.ιEquivRange Q).symm)

/-- Characterization of the transported action by Clifford conjugation. -/
theorem ι_conjugationLinearEquiv (x : spinGroup Q) (m : M) :
    CliffordAlgebra.ι Q (conjugationLinearEquiv Q x m) =
      ConjAct.toConjAct (toUnits x) • CliffordAlgebra.ι Q m := by
  change ((CliffordAlgebra.ιEquivRange Q) (conjugationLinearEquiv Q x m) :
      CliffordAlgebra Q) = _
  simp only [conjugationLinearEquiv, LinearEquiv.trans_apply,
    LinearEquiv.apply_symm_apply]
  rfl

/-- Clifford conjugation by a Spin element preserves the quadratic form. -/
theorem conjugationLinearEquiv_map_app (x : spinGroup Q) (m : M) :
    Q (conjugationLinearEquiv Q x m) = Q m := by
  apply (algebraMap R (CliffordAlgebra Q)).injective
  rw [← CliffordAlgebra.ι_sq_scalar, ← CliffordAlgebra.ι_sq_scalar,
    ι_conjugationLinearEquiv]
  rw [ConjAct.units_smul_def, ConjAct.ofConjAct_toConjAct]
  have hinv : ((↑(toUnits x)⁻¹ : CliffordAlgebra Q) *
      (↑(toUnits x) : CliffordAlgebra Q)) = 1 := by
    change (↑(x⁻¹) : CliffordAlgebra Q) * (x : CliffordAlgebra Q) = 1
    exact coe_star_mul_self x
  have hmul : ((↑(toUnits x) : CliffordAlgebra Q) *
      (↑(toUnits x)⁻¹ : CliffordAlgebra Q)) = 1 := by
    change (x : CliffordAlgebra Q) * (↑(x⁻¹) : CliffordAlgebra Q) = 1
    exact coe_mul_star_self x
  simp only [mul_assoc]
  rw [← mul_assoc (↑(toUnits x)⁻¹ : CliffordAlgebra Q)
    (↑(toUnits x) : CliffordAlgebra Q), hinv, one_mul]
  rw [← mul_assoc (CliffordAlgebra.ι Q m) (CliffordAlgebra.ι Q m),
    CliffordAlgebra.ι_sq_scalar]
  rw [Algebra.commutes]
  rw [← mul_assoc, hmul, one_mul]

/-- Each Spin element induces an isometric equivalence of the quadratic
module. -/
noncomputable def conjugationIsometryEquiv (x : spinGroup Q) :
    Q.IsometryEquiv Q where
  toLinearEquiv := conjugationLinearEquiv Q x
  map_app' := conjugationLinearEquiv_map_app Q x

/-- The transported Spin action is multiplicative. -/
noncomputable def conjugationRepresentation :
    spinGroup Q →* (M ≃ₗ[R] M) where
  toFun := conjugationLinearEquiv Q
  map_one' := by
    apply LinearEquiv.ext
    intro m
    apply CliffordAlgebra.ι_injective_of_invertible_two Q
    rw [ι_conjugationLinearEquiv]
    simp
  map_mul' x y := by
    apply LinearEquiv.ext
    intro m
    apply CliffordAlgebra.ι_injective_of_invertible_two Q
    change CliffordAlgebra.ι Q (conjugationLinearEquiv Q (x * y) m) =
      CliffordAlgebra.ι Q (conjugationLinearEquiv Q x
        (conjugationLinearEquiv Q y m))
    rw [ι_conjugationLinearEquiv, ι_conjugationLinearEquiv,
      ι_conjugationLinearEquiv]
    simp only [map_mul, mul_smul]

@[simp]
theorem conjugationRepresentation_apply (x : spinGroup Q) (m : M) :
    conjugationRepresentation Q x m = conjugationLinearEquiv Q x m :=
  rfl

/-- Every value of the Spin representation preserves the quadratic form. -/
theorem conjugationRepresentation_map_app (x : spinGroup Q) (m : M) :
    Q (conjugationRepresentation Q x m) = Q m :=
  conjugationLinearEquiv_map_app Q x m

end spinGroup
