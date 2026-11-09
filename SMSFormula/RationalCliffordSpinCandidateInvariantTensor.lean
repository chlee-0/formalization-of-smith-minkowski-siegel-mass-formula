import SMSFormula.RationalCliffordSpinCandidateInvariantHopfPrecursor

/-!
# Reynolds identification of tensor invariants

For the nontrivial central scalar involution `sigma` on the Spin-candidate
coordinate ring `B`, write `C = B^sigma`.  Over `Q`, averaging defines the
Reynolds retraction

```text
r(b) = (b + sigma(b)) / 2 : B -> C.
```

Tensoring this retraction in both factors identifies `C tensor_Q C` with the
subalgebra of `B tensor_Q B` fixed separately under `sigma tensor id` and
`id tensor sigma`.  The restricted candidate comultiplication is then
transported to an algebra map `C -> C tensor_Q C`, with literal compatibility
with the candidate comultiplication.  The bialgebra and antipode axioms remain
the next packaging step; no quotient-effectivity or flatness theorem is used.
-/

noncomputable section

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 800000

open RationalTamagawa

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

private abbrev B := V.cliffordSpinCandidateCoordinateRing
private abbrev C := V.negOneInvariantSubalgebra
private abbrev BB := TensorProduct ℚ V.B V.B
private abbrev CC := TensorProduct ℚ V.C V.C

local instance invariantTensorRatTower :
    IsScalarTower ℚ V.specialOrthogonalCoordinateRing V.C :=
  IsScalarTower.of_algebraMap_eq' (R := ℚ)
    (S := V.specialOrthogonalCoordinateRing) (A := V.C) rfl

/-- Coercion of rational scalar multiplication on the fixed subalgebra. -/
@[simp] theorem coe_smul_negOneInvariantSubalgebra (q : ℚ) (c : V.C) :
    ((q • c : V.C) : V.B) = q • c.1 := by
  calc
    ((q • c : V.C) : V.B) =
        ((algebraMap ℚ V.C q : V.C) : V.B) * (c : V.B) := rfl
    _ = algebraMap ℚ V.B q * (c : V.B) := by
      rw [V.coe_algebraMap_negOneInvariantSubalgebra]
    _ = q • (c : V.B) := (Algebra.smul_def q (c : V.B)).symm

/-- Averaging with the nontrivial scalar translate, valued in the fixed ring. -/
def negOneReynoldsLinearMap : V.B →ₗ[ℚ] V.C where
  toFun b := ⟨(2 : ℚ)⁻¹ •
      (b + V.cliffordSpinCandidateNegOneCoordinateEnd b), by
    change V.cliffordSpinCandidateNegOneCoordinateEnd
        ((2 : ℚ)⁻¹ • (b + V.cliffordSpinCandidateNegOneCoordinateEnd b)) =
      (2 : ℚ)⁻¹ • (b + V.cliffordSpinCandidateNegOneCoordinateEnd b)
    rw [map_smul, map_add]
    have hself := DFunLike.congr_fun
      V.cliffordSpinCandidateNegOneCoordinateAlgHom_comp_self b
    change V.cliffordSpinCandidateNegOneCoordinateEnd
        (V.cliffordSpinCandidateNegOneCoordinateEnd b) = b at hself
    rw [hself, add_comm]⟩
  map_add' x y := by
    apply Subtype.ext
    change (2 : ℚ)⁻¹ •
        (x + y + V.cliffordSpinCandidateNegOneCoordinateEnd (x + y)) =
      (2 : ℚ)⁻¹ • (x + V.cliffordSpinCandidateNegOneCoordinateEnd x) +
        (2 : ℚ)⁻¹ • (y + V.cliffordSpinCandidateNegOneCoordinateEnd y)
    rw [map_add]
    module
  map_smul' q b := by
    apply Subtype.ext
    rw [V.coe_smul_negOneInvariantSubalgebra]
    change (2 : ℚ)⁻¹ •
        (q • b + V.cliffordSpinCandidateNegOneCoordinateEnd (q • b)) =
      q • ((2 : ℚ)⁻¹ •
        (b + V.cliffordSpinCandidateNegOneCoordinateEnd b))
    rw [map_smul]
    module

/-- The Reynolds map has its literal averaging formula after coercion to `B`. -/
@[simp] theorem negOneReynoldsLinearMap_coe (b : V.B) :
    (V.negOneReynoldsLinearMap b : V.B) =
      (2 : ℚ)⁻¹ • (b + V.cliffordSpinCandidateNegOneCoordinateEnd b) := rfl

/-- The rational algebra inclusion of the fixed subalgebra into `B`. -/
def negOneInvariantInclusionAlgHom : V.C →ₐ[ℚ] V.B :=
  V.C.val.restrictScalars ℚ

/-- Reynolds averaging is a retraction of the fixed-subalgebra inclusion. -/
theorem negOneReynoldsLinearMap_inclusion (c : V.C) :
    V.negOneReynoldsLinearMap (V.negOneInvariantInclusionAlgHom c) = c := by
  apply Subtype.ext
  calc
    (V.negOneReynoldsLinearMap (V.negOneInvariantInclusionAlgHom c) : V.B) =
        (2 : ℚ)⁻¹ • (c.1 +
          V.cliffordSpinCandidateNegOneCoordinateEnd c.1) := by rfl
    _ = (2 : ℚ)⁻¹ • (c.1 + c.1) := by
      have hc : V.cliffordSpinCandidateNegOneCoordinateEnd c.1 = c.1 := c.2
      rw [hc]
    _ = c.1 := by module

/-- Tensor square of the fixed-subalgebra inclusion. -/
def negOneInvariantTensorInclusion : V.CC →ₐ[ℚ] V.BB :=
  Algebra.TensorProduct.map V.negOneInvariantInclusionAlgHom
    V.negOneInvariantInclusionAlgHom

/-- Tensor square of the Reynolds retraction. -/
def negOneReynoldsTensorLinearMap : V.BB →ₗ[ℚ] V.CC :=
  TensorProduct.map V.negOneReynoldsLinearMap V.negOneReynoldsLinearMap

/-- The tensor Reynolds map retracts the tensor inclusion. -/
theorem negOneReynoldsTensor_inclusion (z : V.CC) :
    V.negOneReynoldsTensorLinearMap (V.negOneInvariantTensorInclusion z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul x y =>
      simp [negOneReynoldsTensorLinearMap, negOneInvariantTensorInclusion,
        V.negOneReynoldsLinearMap_inclusion]

/-- Averaging translation in the left tensor factor. -/
def negOneLeftReynoldsTensorLinearMap : V.BB →ₗ[ℚ] V.BB :=
  (2 : ℚ)⁻¹ •
    (LinearMap.id + V.negOneTensorLeft.toLinearMap)

/-- Averaging translation in the right tensor factor. -/
def negOneRightReynoldsTensorLinearMap : V.BB →ₗ[ℚ] V.BB :=
  (2 : ℚ)⁻¹ •
    (LinearMap.id + V.negOneTensorRight.toLinearMap)

/-- Left averaging fixes every left-invariant tensor. -/
theorem negOneLeftReynoldsTensor_eq_of_invariant (z : V.BB)
    (hz : V.negOneTensorLeft z = z) :
    V.negOneLeftReynoldsTensorLinearMap z = z := by
  simp [negOneLeftReynoldsTensorLinearMap, hz]
  module

/-- Right averaging fixes every right-invariant tensor. -/
theorem negOneRightReynoldsTensor_eq_of_invariant (z : V.BB)
    (hz : V.negOneTensorRight z = z) :
    V.negOneRightReynoldsTensorLinearMap z = z := by
  simp [negOneRightReynoldsTensorLinearMap, hz]
  module

/-- Inclusion after tensor Reynolds averaging is successive averaging in the
right and left tensor factors. -/
theorem negOneInvariantTensorInclusion_reynolds (z : V.BB) :
    V.negOneInvariantTensorInclusion
        (V.negOneReynoldsTensorLinearMap z) =
      V.negOneLeftReynoldsTensorLinearMap
        (V.negOneRightReynoldsTensorLinearMap z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul x y =>
      simp [negOneInvariantTensorInclusion, negOneReynoldsTensorLinearMap,
        negOneLeftReynoldsTensorLinearMap, negOneRightReynoldsTensorLinearMap,
        negOneTensorLeft, negOneTensorRight,
        negOneInvariantInclusionAlgHom]
      rw [TensorProduct.add_tmul, TensorProduct.tmul_add,
        TensorProduct.tmul_add]
      simp only [TensorProduct.smul_tmul', TensorProduct.tmul_smul]

/-- Inclusion after tensor Reynolds averaging fixes every separately
bi-invariant tensor. -/
theorem negOneInvariantTensorInclusion_reynolds_of_biInvariant
    (z : V.negOneBiInvariantTensorSubalgebra) :
    V.negOneInvariantTensorInclusion
        (V.negOneReynoldsTensorLinearMap z.1) = z.1 := by
  rw [V.negOneInvariantTensorInclusion_reynolds]
  rw [V.negOneRightReynoldsTensor_eq_of_invariant z.1 z.2.2]
  exact V.negOneLeftReynoldsTensor_eq_of_invariant z.1 z.2.1

/-- Every tensor of fixed-ring elements is separately bi-invariant. -/
theorem negOneInvariantTensorInclusion_biInvariant (z : V.CC) :
    V.negOneTensorLeft (V.negOneInvariantTensorInclusion z) =
        V.negOneInvariantTensorInclusion z ∧
      V.negOneTensorRight (V.negOneInvariantTensorInclusion z) =
        V.negOneInvariantTensorInclusion z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy =>
      exact ⟨by simp only [map_add, hx.1, hy.1],
        by simp only [map_add, hx.2, hy.2]⟩
  | tmul x y =>
      have hx : V.cliffordSpinCandidateNegOneCoordinateEnd x.1 = x.1 := x.2
      have hy : V.cliffordSpinCandidateNegOneCoordinateEnd y.1 = y.1 := y.2
      simp [negOneInvariantTensorInclusion, negOneTensorLeft,
        negOneTensorRight, negOneInvariantInclusionAlgHom, hx, hy]

/-- The tensor inclusion with codomain restricted to bi-invariants. -/
def negOneInvariantTensorAlgHom :
    V.CC →ₐ[ℚ] V.negOneBiInvariantTensorSubalgebra where
  toFun z := ⟨V.negOneInvariantTensorInclusion z,
    V.negOneInvariantTensorInclusion_biInvariant z⟩
  map_one' := by
    apply Subtype.ext
    change V.negOneInvariantTensorInclusion (1 : V.CC) = (1 : V.BB)
    exact V.negOneInvariantTensorInclusion.map_one
  map_mul' x y := by ext; exact map_mul _ x y
  map_zero' := by ext; exact map_zero _
  map_add' x y := by ext; exact map_add _ x y
  commutes' q := by ext; exact V.negOneInvariantTensorInclusion.commutes q

/-- Tensor inclusion is injective, witnessed by tensor Reynolds averaging. -/
theorem negOneInvariantTensorAlgHom_injective :
    Function.Injective V.negOneInvariantTensorAlgHom := by
  intro x y h
  have hcoe : V.negOneInvariantTensorInclusion x =
      V.negOneInvariantTensorInclusion y := congrArg Subtype.val h
  have hr := congrArg V.negOneReynoldsTensorLinearMap hcoe
  simpa [V.negOneReynoldsTensor_inclusion] using hr

/-- Every separately bi-invariant tensor comes from the fixed tensor square. -/
theorem negOneInvariantTensorAlgHom_surjective :
    Function.Surjective V.negOneInvariantTensorAlgHom := by
  intro z
  refine ⟨V.negOneReynoldsTensorLinearMap z.1, ?_⟩
  apply Subtype.ext
  exact V.negOneInvariantTensorInclusion_reynolds_of_biInvariant z

/-- The fixed tensor square is the separately bi-invariant tensor subalgebra. -/
def negOneInvariantTensorAlgEquiv :
    V.CC ≃ₐ[ℚ] V.negOneBiInvariantTensorSubalgebra :=
  AlgEquiv.ofBijective V.negOneInvariantTensorAlgHom
    ⟨V.negOneInvariantTensorAlgHom_injective,
      V.negOneInvariantTensorAlgHom_surjective⟩

/-- Comultiplication on the fixed ring, transported through the Reynolds tensor
equivalence. -/
def negOneInvariantComul : V.C →ₐ[ℚ] V.CC :=
  V.negOneInvariantTensorAlgEquiv.symm.toAlgHom.comp
    V.negOneInvariantComulToBiInvariant

/-- The transported fixed-ring comultiplication is literally compatible with
the candidate comultiplication under tensor inclusion. -/
theorem negOneInvariantTensorInclusion_comp_comul :
    V.negOneInvariantTensorInclusion.comp V.negOneInvariantComul =
      V.cliffordSpinCandidateCoordinateComul.comp
        V.negOneInvariantInclusionAlgHom := by
  ext c
  have h := V.negOneInvariantTensorAlgEquiv.apply_symm_apply
    (V.negOneInvariantComulToBiInvariant c)
  exact congrArg Subtype.val h

/-- The restricted counit is compatible with fixed-ring inclusion. -/
theorem negOneInvariantCounit_comp_inclusion :
    V.negOneInvariantCounit =
      V.cliffordSpinCandidateCoordinateCounit.comp
        V.negOneInvariantInclusionAlgHom := rfl

/-- The restricted antipode is compatible with fixed-ring inclusion. -/
theorem negOneInvariantInclusion_comp_antipode :
    V.negOneInvariantInclusionAlgHom.comp V.negOneInvariantAntipode =
      V.cliffordSpinCandidateCoordinateAntipode.comp
        V.negOneInvariantInclusionAlgHom := by
  rfl

end RationalQuadraticSpaceMatrix
