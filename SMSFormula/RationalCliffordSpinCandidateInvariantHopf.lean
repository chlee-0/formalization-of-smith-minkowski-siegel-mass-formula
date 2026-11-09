import SMSFormula.RationalCliffordSpinCandidateInvariantTensor
import Mathlib.RingTheory.Bialgebra.Hom

/-!
# Hopf algebra on the literal Spin invariant quotient

Write `B` for the Spin-candidate coordinate ring and `C = B^sigma` for the
fixed ring under translation by the nontrivial central scalar.  Reynolds
averaging already identifies `C tensor_Q C` with the separately invariant
part of `B tensor_Q B` and transports the candidate comultiplication to `C`.

This file reflects coassociativity, both counit laws, and both antipode laws
through the fixed-ring inclusions.  It installs a genuine `HopfAlgebra Q C`
instance and packages the injective comparison `O(SO) -> C` as a `BialgHom`.
No quotient effectivity, flatness over `O(SO)`, or rational-point
surjectivity is inferred.
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
private abbrev BBB := TensorProduct ℚ V.B V.BB
private abbrev CCC := TensorProduct ℚ V.C V.CC

local instance invariantHopfTensorRatTower :
    IsScalarTower ℚ V.specialOrthogonalCoordinateRing V.C :=
  IsScalarTower.of_algebraMap_eq' (R := ℚ)
    (S := V.specialOrthogonalCoordinateRing) (A := V.C) rfl

local instance invariantHopfTensorCommSemiring : CommSemiring V.BB :=
  Algebra.TensorProduct.instCommSemiring

local instance invariantHopfTensorAlgebra : Algebra ℚ V.BB :=
  Algebra.TensorProduct.instAlgebra

local instance invariantHopfTripleCommRing : CommRing V.BBB :=
  Algebra.TensorProduct.instCommRing (R := ℚ) (A := V.B) (B := V.BB)

local instance invariantHopfTripleAlgebra : Algebra ℚ V.BBB :=
  Algebra.TensorProduct.instAlgebra (R := ℚ) (A := V.B) (B := V.BB)

local instance invariantHopfInvariantTripleCommRing : CommRing V.CCC :=
  Algebra.TensorProduct.instCommRing (R := ℚ) (A := V.C) (B := V.CC)

local instance invariantHopfInvariantTripleAlgebra : Algebra ℚ V.CCC :=
  Algebra.TensorProduct.instAlgebra (R := ℚ) (A := V.C) (B := V.CC)

example : (invariantHopfTensorCommSemiring V).toSemiring =
    Algebra.TensorProduct.instSemiring (R := ℚ) (A := V.B) (B := V.B) := rfl

example : invariantHopfTensorAlgebra V =
    Algebra.TensorProduct.leftAlgebra (R := ℚ) (S := ℚ)
      (A := V.B) (B := V.B) := rfl

example : (invariantHopfTripleCommRing V).toCommSemiring.toSemiring =
    Algebra.TensorProduct.instSemiring (R := ℚ) (A := V.B) (B := V.BB) := rfl

example : invariantHopfTripleAlgebra V =
    Algebra.TensorProduct.leftAlgebra (R := ℚ) (S := ℚ)
      (A := V.B) (B := V.BB) := rfl

example : (invariantHopfInvariantTripleCommRing V).toCommSemiring.toSemiring =
    Algebra.TensorProduct.instSemiring (R := ℚ) (A := V.C) (B := V.CC) := rfl

example : invariantHopfInvariantTripleAlgebra V =
    Algebra.TensorProduct.leftAlgebra (R := ℚ) (S := ℚ)
      (A := V.C) (B := V.CC) := rfl

/-- Fixed-ring inclusion is the subtype coercion on elements. -/
@[simp] theorem negOneInvariantInclusionAlgHom_apply (c : V.C) :
    V.negOneInvariantInclusionAlgHom c = c.1 := rfl

/-- The fixed tensor inclusion sends a pure tensor to the corresponding pure
tensor in candidate coordinates. -/
@[simp] theorem negOneInvariantTensorInclusion_tmul (x y : V.C) :
    V.negOneInvariantTensorInclusion (x ⊗ₜ[ℚ] y) =
      (x.1 ⊗ₜ[ℚ] y.1 : V.BB) := by
  simp [negOneInvariantTensorInclusion, negOneInvariantInclusionAlgHom]

/-- Inclusion from the right-associated triple tensor of fixed elements into
the corresponding triple tensor of candidate coordinates. -/
def negOneInvariantTripleTensorInclusion : V.CCC →ₐ[ℚ] V.BBB :=
  Algebra.TensorProduct.map V.negOneInvariantInclusionAlgHom
    V.negOneInvariantTensorInclusion

/-- Tensor product of the Reynolds retractions on the first and last two
tensor factors. -/
def negOneReynoldsTripleTensorLinearMap : V.BBB →ₗ[ℚ] V.CCC :=
  TensorProduct.map V.negOneReynoldsLinearMap
    V.negOneReynoldsTensorLinearMap

/-- The triple fixed-tensor inclusion sends pure tensors to pure tensors. -/
@[simp] theorem negOneInvariantTripleTensorInclusion_tmul
    (x : V.C) (z : V.CC) :
    V.negOneInvariantTripleTensorInclusion (x ⊗ₜ[ℚ] z) =
      (x.1 ⊗ₜ[ℚ] V.negOneInvariantTensorInclusion z : V.BBB) := by
  simp [negOneInvariantTripleTensorInclusion,
    negOneInvariantInclusionAlgHom]

/-- Triple Reynolds averaging retracts the triple fixed-tensor inclusion. -/
theorem negOneReynoldsTripleTensorLinearMap_inclusion (z : V.CCC) :
    V.negOneReynoldsTripleTensorLinearMap (V.negOneInvariantTripleTensorInclusion z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul x y =>
      change V.negOneReynoldsLinearMap x.1 ⊗ₜ[ℚ]
          V.negOneReynoldsTensorLinearMap
            (V.negOneInvariantTensorInclusion y) = x ⊗ₜ[ℚ] y
      rw [show x.1 = V.negOneInvariantInclusionAlgHom x from rfl,
        V.negOneReynoldsLinearMap_inclusion,
        V.negOneReynoldsTensor_inclusion]

/-- The triple fixed-tensor inclusion is injective. -/
theorem negOneInvariantTripleTensorInclusion_injective :
    Function.Injective V.negOneInvariantTripleTensorInclusion := by
  intro x y h
  have hr := congrArg V.negOneReynoldsTripleTensorLinearMap h
  simpa [V.negOneReynoldsTripleTensorLinearMap_inclusion] using hr

/-- The triple inclusion commutes with reassociation on a tensor whose first
factor is itself a fixed tensor. -/
theorem negOneInvariantTripleTensorInclusion_assoc_tmul (z : V.CC) (c : V.C) :
    V.negOneInvariantTripleTensorInclusion
        ((Algebra.TensorProduct.assoc ℚ ℚ ℚ V.C V.C V.C)
          (z ⊗ₜ[ℚ] c)) =
      (Algebra.TensorProduct.assoc ℚ ℚ ℚ V.B V.B V.B)
        (V.negOneInvariantTensorInclusion z ⊗ₜ[ℚ]
          V.negOneInvariantInclusionAlgHom c) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [TensorProduct.add_tmul, map_add, hx, hy]
  | tmul x y =>
      simp [negOneInvariantTripleTensorInclusion,
        negOneInvariantTensorInclusion, negOneInvariantInclusionAlgHom]

/-- Naturality of the left comultiplication branch and tensor associator under
the fixed-ring inclusion. -/
theorem negOneInvariantAssocNaturality :
    V.negOneInvariantTripleTensorInclusion.comp
        ((Algebra.TensorProduct.assoc ℚ ℚ ℚ V.C V.C V.C).toAlgHom.comp
          (Algebra.TensorProduct.map V.negOneInvariantComul
            (AlgHom.id ℚ V.C))) =
      (Algebra.TensorProduct.assoc ℚ ℚ ℚ V.B V.B V.B).toAlgHom.comp
        ((Algebra.TensorProduct.map
          V.cliffordSpinCandidateCoordinateComul (AlgHom.id ℚ V.B)).comp
            V.negOneInvariantTensorInclusion) := by
  apply AlgHom.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul x y =>
      simp only [AlgHom.comp_apply, Algebra.TensorProduct.map_tmul,
        AlgHom.id_apply, V.negOneInvariantTensorInclusion_tmul]
      calc
        V.negOneInvariantTripleTensorInclusion
            ((Algebra.TensorProduct.assoc ℚ ℚ ℚ V.C V.C V.C)
              (V.negOneInvariantComul x ⊗ₜ[ℚ] y)) =
          (Algebra.TensorProduct.assoc ℚ ℚ ℚ V.B V.B V.B)
            (V.negOneInvariantTensorInclusion (V.negOneInvariantComul x) ⊗ₜ[ℚ]
              y.1) :=
            V.negOneInvariantTripleTensorInclusion_assoc_tmul
              (V.negOneInvariantComul x) y
        _ = (Algebra.TensorProduct.assoc ℚ ℚ ℚ V.B V.B V.B)
            (V.cliffordSpinCandidateCoordinateComul x.1 ⊗ₜ[ℚ] y.1) := by
              rw [show V.negOneInvariantTensorInclusion
                (V.negOneInvariantComul x) =
                  V.cliffordSpinCandidateCoordinateComul x.1 from
                DFunLike.congr_fun
                  V.negOneInvariantTensorInclusion_comp_comul x]

/-- Naturality of the right comultiplication branch under the fixed-ring
inclusion. -/
theorem negOneInvariantRightNaturality :
    V.negOneInvariantTripleTensorInclusion.comp
        (Algebra.TensorProduct.map (AlgHom.id ℚ V.C)
          V.negOneInvariantComul) =
      (Algebra.TensorProduct.map (AlgHom.id ℚ V.B)
        V.cliffordSpinCandidateCoordinateComul).comp
          V.negOneInvariantTensorInclusion := by
  apply AlgHom.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul x y =>
      simp only [AlgHom.comp_apply, Algebra.TensorProduct.map_tmul,
        AlgHom.id_apply, V.negOneInvariantTensorInclusion_tmul,
        V.negOneInvariantTripleTensorInclusion_tmul]
      rw [show V.negOneInvariantTensorInclusion (V.negOneInvariantComul y) =
        V.cliffordSpinCandidateCoordinateComul y.1 from
        DFunLike.congr_fun V.negOneInvariantTensorInclusion_comp_comul y]

/-- The transported invariant comultiplication is coassociative. -/
theorem negOneInvariantComul_coassoc :
    (Algebra.TensorProduct.assoc ℚ ℚ ℚ V.C V.C V.C).toAlgHom.comp
        ((Algebra.TensorProduct.map V.negOneInvariantComul
          (AlgHom.id ℚ V.C)).comp V.negOneInvariantComul) =
      (Algebra.TensorProduct.map (AlgHom.id ℚ V.C)
        V.negOneInvariantComul).comp V.negOneInvariantComul := by
  ext c
  apply V.negOneInvariantTripleTensorInclusion_injective
  calc
    V.negOneInvariantTripleTensorInclusion
        ((Algebra.TensorProduct.assoc ℚ ℚ ℚ V.C V.C V.C)
          ((Algebra.TensorProduct.map V.negOneInvariantComul
            (AlgHom.id ℚ V.C)) (V.negOneInvariantComul c))) =
      (Algebra.TensorProduct.assoc ℚ ℚ ℚ V.B V.B V.B)
        ((Algebra.TensorProduct.map
          V.cliffordSpinCandidateCoordinateComul (AlgHom.id ℚ V.B))
            (V.negOneInvariantTensorInclusion
              (V.negOneInvariantComul c))) := by
        exact DFunLike.congr_fun V.negOneInvariantAssocNaturality
          (V.negOneInvariantComul c)
    _ = (Algebra.TensorProduct.assoc ℚ ℚ ℚ V.B V.B V.B)
        ((Algebra.TensorProduct.map
          V.cliffordSpinCandidateCoordinateComul (AlgHom.id ℚ V.B))
            (V.cliffordSpinCandidateCoordinateComul
              (V.negOneInvariantInclusionAlgHom c))) := by
        rw [show V.negOneInvariantTensorInclusion (V.negOneInvariantComul c) =
          V.cliffordSpinCandidateCoordinateComul
            (V.negOneInvariantInclusionAlgHom c) from
          DFunLike.congr_fun V.negOneInvariantTensorInclusion_comp_comul c]
    _ = (Algebra.TensorProduct.map (AlgHom.id ℚ V.B)
        V.cliffordSpinCandidateCoordinateComul)
          (V.cliffordSpinCandidateCoordinateComul
            (V.negOneInvariantInclusionAlgHom c)) := by
        exact DFunLike.congr_fun
          V.cliffordSpinCandidateAffinePointGroupData.comul_coassoc
          (V.negOneInvariantInclusionAlgHom c)
    _ = (Algebra.TensorProduct.map (AlgHom.id ℚ V.B)
        V.cliffordSpinCandidateCoordinateComul)
          (V.negOneInvariantTensorInclusion (V.negOneInvariantComul c)) := by
        rw [show V.negOneInvariantTensorInclusion (V.negOneInvariantComul c) =
          V.cliffordSpinCandidateCoordinateComul
            (V.negOneInvariantInclusionAlgHom c) from
          DFunLike.congr_fun V.negOneInvariantTensorInclusion_comp_comul c]
    _ = V.negOneInvariantTripleTensorInclusion
        ((Algebra.TensorProduct.map (AlgHom.id ℚ V.C)
          V.negOneInvariantComul) (V.negOneInvariantComul c)) := by
        exact (DFunLike.congr_fun V.negOneInvariantRightNaturality
          (V.negOneInvariantComul c)).symm

/-- Naturality of left tensor contraction by the invariant counit. -/
theorem negOneInvariantLidCounitNaturality :
    V.negOneInvariantInclusionAlgHom.comp
        ((Algebra.TensorProduct.lid ℚ V.C).toAlgHom.comp
          (Algebra.TensorProduct.map V.negOneInvariantCounit
            (AlgHom.id ℚ V.C))) =
      (Algebra.TensorProduct.lid ℚ V.B).toAlgHom.comp
        ((Algebra.TensorProduct.map
          V.cliffordSpinCandidateCoordinateCounit (AlgHom.id ℚ V.B)).comp
            V.negOneInvariantTensorInclusion) := by
  apply AlgHom.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul x y =>
      simp [negOneInvariantCounit,
        V.negOneInvariantTensorInclusion_tmul]

/-- Naturality of right tensor contraction by the invariant counit. -/
theorem negOneInvariantRidCounitNaturality :
    V.negOneInvariantInclusionAlgHom.comp
        ((Algebra.TensorProduct.rid ℚ ℚ V.C).toAlgHom.comp
          (Algebra.TensorProduct.map (AlgHom.id ℚ V.C)
            V.negOneInvariantCounit)) =
      (Algebra.TensorProduct.rid ℚ ℚ V.B).toAlgHom.comp
        ((Algebra.TensorProduct.map (AlgHom.id ℚ V.B)
          V.cliffordSpinCandidateCoordinateCounit).comp
            V.negOneInvariantTensorInclusion) := by
  apply AlgHom.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul x y =>
      simp [negOneInvariantCounit,
        V.negOneInvariantTensorInclusion_tmul]

/-- The transported invariant comultiplication satisfies the right tensor
counit law. -/
theorem negOneInvariantComul_rTensor_counit :
    (Algebra.TensorProduct.map V.negOneInvariantCounit
      (AlgHom.id ℚ V.C)).comp V.negOneInvariantComul =
        (Algebra.TensorProduct.lid ℚ V.C).symm := by
  ext c
  apply (Algebra.TensorProduct.lid ℚ V.C).injective
  apply Subtype.ext
  calc
    ((V.negOneInvariantInclusionAlgHom.comp
      ((Algebra.TensorProduct.lid ℚ V.C).toAlgHom.comp
        (Algebra.TensorProduct.map V.negOneInvariantCounit
          (AlgHom.id ℚ V.C)))) (V.negOneInvariantComul c)) =
      (Algebra.TensorProduct.lid ℚ V.B)
        ((Algebra.TensorProduct.map
          V.cliffordSpinCandidateCoordinateCounit (AlgHom.id ℚ V.B))
            (V.negOneInvariantTensorInclusion
              (V.negOneInvariantComul c))) := by
        exact DFunLike.congr_fun V.negOneInvariantLidCounitNaturality
          (V.negOneInvariantComul c)
    _ = (Algebra.TensorProduct.lid ℚ V.B)
        ((Algebra.TensorProduct.map
          V.cliffordSpinCandidateCoordinateCounit (AlgHom.id ℚ V.B))
            (V.cliffordSpinCandidateCoordinateComul
              (V.negOneInvariantInclusionAlgHom c))) := by
        rw [show V.negOneInvariantTensorInclusion (V.negOneInvariantComul c) =
          V.cliffordSpinCandidateCoordinateComul
            (V.negOneInvariantInclusionAlgHom c) from
          DFunLike.congr_fun V.negOneInvariantTensorInclusion_comp_comul c]
    _ = V.negOneInvariantInclusionAlgHom c := by
        have h := DFunLike.congr_fun
          V.cliffordSpinCandidateAffinePointGroupData.comul_rTensor_counit
          (V.negOneInvariantInclusionAlgHom c)
        rw [show (Algebra.TensorProduct.map
            V.cliffordSpinCandidateCoordinateCounit (AlgHom.id ℚ V.B))
              (V.cliffordSpinCandidateCoordinateComul
                (V.negOneInvariantInclusionAlgHom c)) =
            (Algebra.TensorProduct.lid ℚ V.B).symm
              (V.negOneInvariantInclusionAlgHom c) from h]
        exact (Algebra.TensorProduct.lid ℚ V.B).apply_symm_apply _
    _ = (((Algebra.TensorProduct.lid ℚ V.C)
        ((Algebra.TensorProduct.lid ℚ V.C).symm c) : V.C) : V.B) := by
      exact congrArg Subtype.val
        ((Algebra.TensorProduct.lid ℚ V.C).apply_symm_apply c).symm

/-- The transported invariant comultiplication satisfies the left tensor
counit law. -/
theorem negOneInvariantComul_lTensor_counit :
    (Algebra.TensorProduct.map (AlgHom.id ℚ V.C)
      V.negOneInvariantCounit).comp V.negOneInvariantComul =
        (Algebra.TensorProduct.rid ℚ ℚ V.C).symm := by
  ext c
  apply (Algebra.TensorProduct.rid ℚ ℚ V.C).injective
  apply Subtype.ext
  calc
    ((V.negOneInvariantInclusionAlgHom.comp
      ((Algebra.TensorProduct.rid ℚ ℚ V.C).toAlgHom.comp
        (Algebra.TensorProduct.map (AlgHom.id ℚ V.C)
          V.negOneInvariantCounit))) (V.negOneInvariantComul c)) =
      (Algebra.TensorProduct.rid ℚ ℚ V.B)
        ((Algebra.TensorProduct.map (AlgHom.id ℚ V.B)
          V.cliffordSpinCandidateCoordinateCounit)
            (V.negOneInvariantTensorInclusion
              (V.negOneInvariantComul c))) := by
        exact DFunLike.congr_fun V.negOneInvariantRidCounitNaturality
          (V.negOneInvariantComul c)
    _ = (Algebra.TensorProduct.rid ℚ ℚ V.B)
        ((Algebra.TensorProduct.map (AlgHom.id ℚ V.B)
          V.cliffordSpinCandidateCoordinateCounit)
            (V.cliffordSpinCandidateCoordinateComul
              (V.negOneInvariantInclusionAlgHom c))) := by
        rw [show V.negOneInvariantTensorInclusion (V.negOneInvariantComul c) =
          V.cliffordSpinCandidateCoordinateComul
            (V.negOneInvariantInclusionAlgHom c) from
          DFunLike.congr_fun V.negOneInvariantTensorInclusion_comp_comul c]
    _ = V.negOneInvariantInclusionAlgHom c := by
        have h := DFunLike.congr_fun
          V.cliffordSpinCandidateAffinePointGroupData.comul_lTensor_counit
          (V.negOneInvariantInclusionAlgHom c)
        rw [show (Algebra.TensorProduct.map (AlgHom.id ℚ V.B)
            V.cliffordSpinCandidateCoordinateCounit)
              (V.cliffordSpinCandidateCoordinateComul
                (V.negOneInvariantInclusionAlgHom c)) =
            (Algebra.TensorProduct.rid ℚ ℚ V.B).symm
              (V.negOneInvariantInclusionAlgHom c) from h]
        exact (Algebra.TensorProduct.rid ℚ ℚ V.B).apply_symm_apply _
    _ = (((Algebra.TensorProduct.rid ℚ ℚ V.C)
        ((Algebra.TensorProduct.rid ℚ ℚ V.C).symm c) : V.C) : V.B) := by
      exact congrArg Subtype.val
        ((Algebra.TensorProduct.rid ℚ ℚ V.C).apply_symm_apply c).symm

/-- The bialgebra structure on the literal invariant coordinate ring. -/
noncomputable instance negOneInvariantBialgebra : Bialgebra ℚ V.C :=
  Bialgebra.ofAlgHom V.negOneInvariantComul V.negOneInvariantCounit
    V.negOneInvariantComul_coassoc V.negOneInvariantComul_rTensor_counit V.negOneInvariantComul_lTensor_counit

/-- The bundled invariant comultiplication is the transported algebra map. -/
theorem negOneInvariant_comulAlgHom :
    Bialgebra.comulAlgHom ℚ V.C = V.negOneInvariantComul := rfl

/-- The bundled invariant counit is the restricted candidate counit. -/
theorem negOneInvariant_counitAlgHom :
    Bialgebra.counitAlgHom ℚ V.C = V.negOneInvariantCounit := rfl

/-- Naturality of applying the invariant antipode in the first tensor
factor. -/
theorem negOneInvariantAntipodeRightNaturality :
    V.negOneInvariantTensorInclusion.comp
        (Algebra.TensorProduct.map V.negOneInvariantAntipode
          (AlgHom.id ℚ V.C)) =
      (Algebra.TensorProduct.map
        V.cliffordSpinCandidateCoordinateAntipode (AlgHom.id ℚ V.B)).comp
          V.negOneInvariantTensorInclusion := by
  apply AlgHom.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul x y =>
      simp only [AlgHom.comp_apply, Algebra.TensorProduct.map_tmul,
        AlgHom.id_apply, V.negOneInvariantTensorInclusion_tmul]
      rw [show (V.negOneInvariantAntipode x).1 =
        V.cliffordSpinCandidateCoordinateAntipode x.1 from
        DFunLike.congr_fun V.negOneInvariantInclusion_comp_antipode x]

/-- Naturality of applying the invariant antipode in the second tensor
factor. -/
theorem negOneInvariantAntipodeLeftNaturality :
    V.negOneInvariantTensorInclusion.comp
        (Algebra.TensorProduct.map (AlgHom.id ℚ V.C)
          V.negOneInvariantAntipode) =
      (Algebra.TensorProduct.map (AlgHom.id ℚ V.B)
        V.cliffordSpinCandidateCoordinateAntipode).comp
          V.negOneInvariantTensorInclusion := by
  apply AlgHom.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul x y =>
      simp only [AlgHom.comp_apply, Algebra.TensorProduct.map_tmul,
        AlgHom.id_apply, V.negOneInvariantTensorInclusion_tmul]
      rw [show (V.negOneInvariantAntipode y).1 =
        V.cliffordSpinCandidateCoordinateAntipode y.1 from
        DFunLike.congr_fun V.negOneInvariantInclusion_comp_antipode y]

/-- Multiplication commutes with inclusion from the fixed tensor square. -/
theorem negOneInvariantMulNaturality :
    V.negOneInvariantInclusionAlgHom.comp
        (AffinePointGroupData.mulAlgHom (R := ℚ) (A := V.C)) =
      (AffinePointGroupData.mulAlgHom (R := ℚ) (A := V.B)).comp
        V.negOneInvariantTensorInclusion := by
  apply AlgHom.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul x y =>
      simp [AffinePointGroupData.mulAlgHom,
        V.negOneInvariantTensorInclusion_tmul]

/-- The algebra unit commutes with the fixed-ring inclusion. -/
theorem negOneInvariantUnitNaturality :
    V.negOneInvariantInclusionAlgHom.comp
        (AffinePointGroupData.unitAlgHom (R := ℚ) (A := V.C)) =
      (AffinePointGroupData.unitAlgHom (R := ℚ) (A := V.B)) := by
  ext

/-- The restricted antipode satisfies the right tensor antipode identity. -/
theorem negOneInvariantAntipode_rTensor :
    (AffinePointGroupData.mulAlgHom (R := ℚ) (A := V.C)).comp
      ((Algebra.TensorProduct.map V.negOneInvariantAntipode
        (AlgHom.id ℚ V.C)).comp V.negOneInvariantComul) =
      (AffinePointGroupData.unitAlgHom (R := ℚ) (A := V.C)).comp
        V.negOneInvariantCounit := by
  ext c
  calc
    V.negOneInvariantInclusionAlgHom
        ((AffinePointGroupData.mulAlgHom (R := ℚ) (A := V.C))
          ((Algebra.TensorProduct.map V.negOneInvariantAntipode
            (AlgHom.id ℚ V.C)) (V.negOneInvariantComul c))) =
      (AffinePointGroupData.mulAlgHom (R := ℚ) (A := V.B))
        (V.negOneInvariantTensorInclusion
          ((Algebra.TensorProduct.map V.negOneInvariantAntipode
            (AlgHom.id ℚ V.C)) (V.negOneInvariantComul c))) := by
        exact DFunLike.congr_fun V.negOneInvariantMulNaturality _
    _ = (AffinePointGroupData.mulAlgHom (R := ℚ) (A := V.B))
        ((Algebra.TensorProduct.map
          V.cliffordSpinCandidateCoordinateAntipode (AlgHom.id ℚ V.B))
            (V.negOneInvariantTensorInclusion
              (V.negOneInvariantComul c))) := by
        rw [show V.negOneInvariantTensorInclusion
            ((Algebra.TensorProduct.map V.negOneInvariantAntipode
              (AlgHom.id ℚ V.C)) (V.negOneInvariantComul c)) =
          (Algebra.TensorProduct.map
            V.cliffordSpinCandidateCoordinateAntipode (AlgHom.id ℚ V.B))
              (V.negOneInvariantTensorInclusion (V.negOneInvariantComul c)) from
          DFunLike.congr_fun V.negOneInvariantAntipodeRightNaturality
            (V.negOneInvariantComul c)]
    _ = (AffinePointGroupData.mulAlgHom (R := ℚ) (A := V.B))
        ((Algebra.TensorProduct.map
          V.cliffordSpinCandidateCoordinateAntipode (AlgHom.id ℚ V.B))
            (V.cliffordSpinCandidateCoordinateComul
              (V.negOneInvariantInclusionAlgHom c))) := by
        rw [show V.negOneInvariantTensorInclusion (V.negOneInvariantComul c) =
          V.cliffordSpinCandidateCoordinateComul
            (V.negOneInvariantInclusionAlgHom c) from
          DFunLike.congr_fun V.negOneInvariantTensorInclusion_comp_comul c]
    _ = (AffinePointGroupData.unitAlgHom (R := ℚ) (A := V.B))
        (V.cliffordSpinCandidateCoordinateCounit
          (V.negOneInvariantInclusionAlgHom c)) := by
        exact DFunLike.congr_fun
          V.cliffordSpinCandidateAffinePointGroupData.antipode_rTensor
          (V.negOneInvariantInclusionAlgHom c)
    _ = (AffinePointGroupData.unitAlgHom (R := ℚ) (A := V.B))
        (V.negOneInvariantCounit c) := by
        exact congrArg
          (AffinePointGroupData.unitAlgHom (R := ℚ) (A := V.B))
          (DFunLike.congr_fun V.negOneInvariantCounit_comp_inclusion c).symm
    _ = V.negOneInvariantInclusionAlgHom
        ((AffinePointGroupData.unitAlgHom (R := ℚ) (A := V.C))
          (V.negOneInvariantCounit c)) := by
        exact (DFunLike.congr_fun V.negOneInvariantUnitNaturality
          (V.negOneInvariantCounit c)).symm

/-- The restricted antipode satisfies the left tensor antipode identity. -/
theorem negOneInvariantAntipode_lTensor :
    (AffinePointGroupData.mulAlgHom (R := ℚ) (A := V.C)).comp
      ((Algebra.TensorProduct.map (AlgHom.id ℚ V.C)
        V.negOneInvariantAntipode).comp V.negOneInvariantComul) =
      (AffinePointGroupData.unitAlgHom (R := ℚ) (A := V.C)).comp
        V.negOneInvariantCounit := by
  ext c
  calc
    V.negOneInvariantInclusionAlgHom
        ((AffinePointGroupData.mulAlgHom (R := ℚ) (A := V.C))
          ((Algebra.TensorProduct.map (AlgHom.id ℚ V.C)
            V.negOneInvariantAntipode) (V.negOneInvariantComul c))) =
      (AffinePointGroupData.mulAlgHom (R := ℚ) (A := V.B))
        (V.negOneInvariantTensorInclusion
          ((Algebra.TensorProduct.map (AlgHom.id ℚ V.C)
            V.negOneInvariantAntipode) (V.negOneInvariantComul c))) := by
        exact DFunLike.congr_fun V.negOneInvariantMulNaturality _
    _ = (AffinePointGroupData.mulAlgHom (R := ℚ) (A := V.B))
        ((Algebra.TensorProduct.map (AlgHom.id ℚ V.B)
          V.cliffordSpinCandidateCoordinateAntipode)
            (V.negOneInvariantTensorInclusion
              (V.negOneInvariantComul c))) := by
        rw [show V.negOneInvariantTensorInclusion
            ((Algebra.TensorProduct.map (AlgHom.id ℚ V.C)
              V.negOneInvariantAntipode) (V.negOneInvariantComul c)) =
          (Algebra.TensorProduct.map (AlgHom.id ℚ V.B)
            V.cliffordSpinCandidateCoordinateAntipode)
              (V.negOneInvariantTensorInclusion (V.negOneInvariantComul c)) from
          DFunLike.congr_fun V.negOneInvariantAntipodeLeftNaturality
            (V.negOneInvariantComul c)]
    _ = (AffinePointGroupData.mulAlgHom (R := ℚ) (A := V.B))
        ((Algebra.TensorProduct.map (AlgHom.id ℚ V.B)
          V.cliffordSpinCandidateCoordinateAntipode)
            (V.cliffordSpinCandidateCoordinateComul
              (V.negOneInvariantInclusionAlgHom c))) := by
        rw [show V.negOneInvariantTensorInclusion (V.negOneInvariantComul c) =
          V.cliffordSpinCandidateCoordinateComul
            (V.negOneInvariantInclusionAlgHom c) from
          DFunLike.congr_fun V.negOneInvariantTensorInclusion_comp_comul c]
    _ = (AffinePointGroupData.unitAlgHom (R := ℚ) (A := V.B))
        (V.cliffordSpinCandidateCoordinateCounit
          (V.negOneInvariantInclusionAlgHom c)) := by
        exact DFunLike.congr_fun
          V.cliffordSpinCandidateAffinePointGroupData.antipode_lTensor
          (V.negOneInvariantInclusionAlgHom c)
    _ = (AffinePointGroupData.unitAlgHom (R := ℚ) (A := V.B))
        (V.negOneInvariantCounit c) := by
        exact congrArg
          (AffinePointGroupData.unitAlgHom (R := ℚ) (A := V.B))
          (DFunLike.congr_fun V.negOneInvariantCounit_comp_inclusion c).symm
    _ = V.negOneInvariantInclusionAlgHom
        ((AffinePointGroupData.unitAlgHom (R := ℚ) (A := V.C))
          (V.negOneInvariantCounit c)) := by
        exact (DFunLike.congr_fun V.negOneInvariantUnitNaturality
          (V.negOneInvariantCounit c)).symm

/-- The Hopf-algebra structure on the literal invariant coordinate ring. -/
noncomputable instance negOneInvariantHopfAlgebra : HopfAlgebra ℚ V.C := by
  letI : HopfAlgebraStruct ℚ V.C :=
    { antipode := V.negOneInvariantAntipode.toLinearMap }
  refine
    { mul_antipode_rTensor_comul := ?_
      mul_antipode_lTensor_comul := ?_ }
  · apply LinearMap.ext
    intro c
    have h := congrArg (fun F : V.C →ₐ[ℚ] V.C => F c)
      V.negOneInvariantAntipode_rTensor
    simpa [AffinePointGroupData.mulAlgHom,
      AffinePointGroupData.unitAlgHom] using h
  · apply LinearMap.ext
    intro c
    have h := congrArg (fun F : V.C →ₐ[ℚ] V.C => F c)
      V.negOneInvariantAntipode_lTensor
    simpa [AffinePointGroupData.mulAlgHom,
      AffinePointGroupData.unitAlgHom] using h

/-- The rational algebra map from the implemented `SO` coordinate ring to the
literal invariant coordinate ring. -/
def specialOrthogonalToNegOneInvariantRatAlgHom :
    V.specialOrthogonalCoordinateRing →ₐ[ℚ] V.C :=
  V.specialOrthogonalToNegOneInvariantAlgHom.restrictScalars ℚ

/-- Including the invariant comparison into candidate coordinates recovers
the original Spin-cover coordinate map. -/
theorem negOneInvariantInclusion_comp_specialOrthogonal :
    V.negOneInvariantInclusionAlgHom.comp V.specialOrthogonalToNegOneInvariantRatAlgHom =
      V.specialOrthogonalToCliffordSpinCandidateCoordinateAlgHom := by
  rfl

/-- Naturality of the tensor square of the `SO`-to-invariant comparison. -/
theorem negOneInvariantTensor_baseNaturality :
    V.negOneInvariantTensorInclusion.comp
        (Algebra.TensorProduct.map V.specialOrthogonalToNegOneInvariantRatAlgHom V.specialOrthogonalToNegOneInvariantRatAlgHom) =
      Algebra.TensorProduct.map
        V.specialOrthogonalToCliffordSpinCandidateCoordinateAlgHom
        V.specialOrthogonalToCliffordSpinCandidateCoordinateAlgHom := by
  apply AlgHom.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul x y =>
      simp only [AlgHom.comp_apply, Algebra.TensorProduct.map_tmul,
        V.negOneInvariantTensorInclusion_tmul]
      rfl

/-- The injective `SO`-to-invariant comparison as a homomorphism of
bialgebras. -/
def specialOrthogonalToNegOneInvariantBialgHom :
    V.specialOrthogonalCoordinateRing →ₐc[ℚ] V.C :=
  BialgHom.ofAlgHom V.specialOrthogonalToNegOneInvariantRatAlgHom (by
    ext a
    exact DFunLike.congr_fun V.cliffordSpinCandidateCoordinateCounit_comp a) (by
    ext a
    apply V.negOneInvariantTensorAlgHom_injective
    apply Subtype.ext
    calc
      V.negOneInvariantTensorInclusion
          ((Algebra.TensorProduct.map V.specialOrthogonalToNegOneInvariantRatAlgHom V.specialOrthogonalToNegOneInvariantRatAlgHom)
            (V.specialOrthogonalCoordinateComul a)) =
        (Algebra.TensorProduct.map
          V.specialOrthogonalToCliffordSpinCandidateCoordinateAlgHom
          V.specialOrthogonalToCliffordSpinCandidateCoordinateAlgHom)
            (V.specialOrthogonalCoordinateComul a) := by
          exact DFunLike.congr_fun V.negOneInvariantTensor_baseNaturality
            (V.specialOrthogonalCoordinateComul a)
      _ = V.cliffordSpinCandidateCoordinateComul
          (V.specialOrthogonalToCliffordSpinCandidateCoordinateAlgHom a) := by
          exact DFunLike.congr_fun
            V.cliffordSpinCandidateCoordinateComul_comp.symm a
      _ = V.cliffordSpinCandidateCoordinateComul
          (V.negOneInvariantInclusionAlgHom (V.specialOrthogonalToNegOneInvariantRatAlgHom a)) := by rfl
      _ = V.negOneInvariantTensorInclusion
          (V.negOneInvariantComul (V.specialOrthogonalToNegOneInvariantRatAlgHom a)) := by
          exact (DFunLike.congr_fun
            V.negOneInvariantTensorInclusion_comp_comul
            (V.specialOrthogonalToNegOneInvariantRatAlgHom a)).symm)

/-- The coordinate bialgebra map from `SO` to the literal invariant quotient
is injective. -/
theorem specialOrthogonalToNegOneInvariantBialgHom_injective :
    Function.Injective V.specialOrthogonalToNegOneInvariantBialgHom :=
  V.specialOrthogonalToNegOneInvariantAlgHom_injective

/-- The bundled invariant antipode is the restricted candidate antipode. -/
theorem negOneInvariant_antipode :
    HopfAlgebra.antipode ℚ (A := V.C) =
      V.negOneInvariantAntipode.toLinearMap := rfl

end RationalQuadraticSpaceMatrix
