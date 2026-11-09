import SMSFormula.RationalCliffordSpinCandidateTraceDescentPrecursor

/-!
# The Spin-candidate torsor canonical-map isomorphism

The affine canonical map

```text
B tensor_A B -> B tensor_Q Q[ZMod 2]
```

has a right inverse. Naturality of the pointwise torsor inverse proves the
other composite, so this file packages the map as an algebra equivalence.

Evaluation at `+1` and `-1` jointly determines an element of the target tensor
product. This identifies invariance under the nontrivial scalar involution
with triviality of the full `mu_2` coaction, and then with equality of the two
maps `B -> B tensor_A B`. Consequently the rank-two effectivity input is
stated as the affine tensor equalizer condition. No effective-descent or
flatness conclusion is drawn without that condition.
-/
noncomputable section

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000

open RationalTamagawa

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

local instance inverseTensorRationalAlgHomMonoidHomClass :
    MonoidHomClass (V.CT →ₐ[ℚ] V.CS) V.CT V.CS :=
  (AlgHom.algHomClass (R := ℚ) (A := V.CT) (B := V.CS)).toRingHomClass.toMonoidHomClass

theorem canInv_ctRoot :
    restrictRootsOfUnity V.canInv 2 V.ctRoot = V.csTorsorInverse.2 := by
  apply rootsOfUnity.coe_injective
  change V.canInv
      ((Algebra.TensorProduct.includeRight (R := ℚ)
        (A := V.cliffordSpinCandidateCoordinateRing)
        (B := RationalMuTwoCoordinateRing))
          (AddMonoidAlgebra.single (1 : ZMod 2) 1)) = _
  rw [V.canInv_muTwoRight, muTwoPointOfRoot_generator]

theorem canInv_comp_ctActionQ :
    V.canInv.comp V.ctActionQ = V.csRightQ := by
  letI : Group (V.cliffordSpinCandidateCoordinateRing →ₐ[ℚ] V.CT) :=
    V.cliffordSpinCandidateCoordinateAlgHomGroup V.CT
  letI : Group (V.cliffordSpinCandidateCoordinateRing →ₐ[ℚ] V.CS) :=
    V.cliffordSpinCandidateCoordinateAlgHomGroup V.CS
  have h := congrArg
    (fun p : V.cliffordSpinCandidateCoordinateSelfFiber V.CS => p.1.2)
    (V.cliffordSpinCandidateCoordinateTorsorMulEquiv_naturality
      (A := V.CT) (B := V.CS)
      V.canInv
      ((Algebra.TensorProduct.includeLeft (R := ℚ) (S := ℚ)
        (A := V.cliffordSpinCandidateCoordinateRing)
        (B := RationalMuTwoCoordinateRing) :
          V.cliffordSpinCandidateCoordinateRing →ₐ[ℚ] V.CT), V.ctRoot))
  change V.canInv.comp V.ctActionQ =
    (V.cliffordSpinCandidateCoordinateTorsorMulEquiv V.CS
      (V.canInv.comp
        (Algebra.TensorProduct.includeLeft (R := ℚ) (S := ℚ)
          (A := V.cliffordSpinCandidateCoordinateRing)
          (B := RationalMuTwoCoordinateRing)),
        restrictRootsOfUnity V.canInv 2 V.ctRoot)).1.2 at h
  rw [V.canInv_ctRoot] at h
  have hleft : V.canInv.comp
      (Algebra.TensorProduct.includeLeft (R := ℚ) (S := ℚ)
        (A := V.cliffordSpinCandidateCoordinateRing)
        (B := RationalMuTwoCoordinateRing)) = V.csTorsorInverse.1 := by
    apply AlgHom.ext
    intro element
    change V.canInv (V.ctLeft element) = V.csTorsorInverse.1 element
    exact (V.canInv_ctLeft element).trans
      (DFunLike.congr_fun V.csTorsorInverse_fst element).symm
  rw [hleft] at h
  exact h.trans V.csTorsorInverse_snd

theorem canInv_comp_canQ : V.canInv.comp V.canQ = AlgHom.id ℚ V.CS := by
  apply AlgHom.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul x y =>
      change V.canInv
        (V.canQ (x ⊗ₜ[V.specialOrthogonalCoordinateRing] y)) = _
      rw [V.canQ_tmul, map_mul, V.canInv_ctLeft]
      change V.csLeftQ x * ((V.canInv.comp V.ctActionQ) y) = _
      rw [V.canInv_comp_ctActionQ]
      simp [csLeftQ, csRightQ]

def canonicalMapAlgEquiv : V.CS ≃ₐ[ℚ] V.CT :=
  AlgEquiv.ofAlgHom V.canQ V.canInv V.canQ_comp_canInv V.canInv_comp_canQ

def canInvA : V.CT →ₐ[V.specialOrthogonalCoordinateRing] V.CS where
  toFun := V.canInv
  map_one' := V.canInv.map_one'
  map_mul' := V.canInv.map_mul'
  map_zero' := V.canInv.map_zero'
  map_add' := V.canInv.map_add'
  commutes' a := by
    change V.canInv
      (V.ctLeft
        (V.specialOrthogonalToCliffordSpinCandidateCoordinateAlgHom a)) = _
    rw [V.canInv_ctLeft]
    rfl

def canonicalMapAlgEquivOverBase : V.CS ≃ₐ[
    V.specialOrthogonalCoordinateRing] V.CT :=
  AlgEquiv.ofAlgHom V.can V.canInvA
    (by
      apply AlgHom.ext
      intro z
      exact DFunLike.congr_fun V.canQ_comp_canInv z)
    (by
      apply AlgHom.ext
      intro z
      exact DFunLike.congr_fun V.canInv_comp_canQ z)

def ctGenerator : V.CT :=
  (Algebra.TensorProduct.includeRight (R := ℚ)
    (A := V.cliffordSpinCandidateCoordinateRing)
    (B := RationalMuTwoCoordinateRing))
      (AddMonoidAlgebra.single (1 : ZMod 2) 1)

def ctLeftQ : V.cliffordSpinCandidateCoordinateRing →ₐ[ℚ] V.CT :=
  Algebra.TensorProduct.includeLeft

@[simp] theorem ctEval_ctGenerator
    (z : rootsOfUnity 2 V.cliffordSpinCandidateCoordinateRing) :
    V.ctEval z V.ctGenerator = (((z :
      V.cliffordSpinCandidateCoordinateRingˣ) :
        V.cliffordSpinCandidateCoordinateRing)) := by
  simp [ctEval, ctGenerator, muTwoPointOfRoot_generator]

def ctPositiveCoefficientLinearMap : V.CT →ₗ[ℚ]
    V.cliffordSpinCandidateCoordinateRing :=
  (2 : ℚ)⁻¹ •
    ((V.ctEval (1 : rootsOfUnity 2
        V.cliffordSpinCandidateCoordinateRing)).toLinearMap +
      (V.ctEval (negOneRootOfUnity
        V.cliffordSpinCandidateCoordinateRing)).toLinearMap)

def ctNegativeCoefficientLinearMap : V.CT →ₗ[ℚ]
    V.cliffordSpinCandidateCoordinateRing :=
  (2 : ℚ)⁻¹ •
    ((V.ctEval (1 : rootsOfUnity 2
        V.cliffordSpinCandidateCoordinateRing)).toLinearMap -
      (V.ctEval (negOneRootOfUnity
        V.cliffordSpinCandidateCoordinateRing)).toLinearMap)

def ctReconstructionLinearMap : V.CT →ₗ[ℚ] V.CT :=
  V.ctLeftQ.toLinearMap.comp V.ctPositiveCoefficientLinearMap +
    (LinearMap.mulRight ℚ V.ctGenerator).comp
      (V.ctLeftQ.toLinearMap.comp V.ctNegativeCoefficientLinearMap)

@[simp] theorem ctReconstructionLinearMap_apply (z : V.CT) :
    V.ctReconstructionLinearMap z =
      V.ctLeft ((2 : ℚ)⁻¹ •
          (V.ctEval (1 : rootsOfUnity 2
              V.cliffordSpinCandidateCoordinateRing) z +
            V.ctEval (negOneRootOfUnity
              V.cliffordSpinCandidateCoordinateRing) z)) +
        V.ctLeft ((2 : ℚ)⁻¹ •
          (V.ctEval (1 : rootsOfUnity 2
              V.cliffordSpinCandidateCoordinateRing) z -
            V.ctEval (negOneRootOfUnity
              V.cliffordSpinCandidateCoordinateRing) z)) *
          V.ctGenerator := by
  simp [ctReconstructionLinearMap, ctPositiveCoefficientLinearMap,
    ctNegativeCoefficientLinearMap, ctLeftQ, ctLeft]
  rw [smul_mul_assoc]

theorem ct_reconstruction (z : V.CT) :
    z = V.ctLeft ((2 : ℚ)⁻¹ •
          (V.ctEval (1 : rootsOfUnity 2
              V.cliffordSpinCandidateCoordinateRing) z +
            V.ctEval (negOneRootOfUnity
              V.cliffordSpinCandidateCoordinateRing) z)) +
      V.ctLeft ((2 : ℚ)⁻¹ •
          (V.ctEval (1 : rootsOfUnity 2
              V.cliffordSpinCandidateCoordinateRing) z -
            V.ctEval (negOneRootOfUnity
              V.cliffordSpinCandidateCoordinateRing) z)) *
        V.ctGenerator := by
  rw [← V.ctReconstructionLinearMap_apply]
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero]
  | add x y hx hy =>
      rw [map_add]
      exact congrArg₂ (· + ·) hx hy
  | tmul x h =>
      induction h using AddMonoidAlgebra.induction_on with
      | hM m =>
          have hleftzero : V.ctLeft (0 : V.cliffordSpinCandidateCoordinateRing) = 0 :=
            V.ctLeft.map_zero'
          have hhalf : (2 : ℚ)⁻¹ • (x + x) = x := by
            simpa only [two_smul] using
              (inv_smul_smul₀ (show (2 : ℚ) ≠ 0 by decide) x)
          fin_cases m
          · change V.ctLeft x = V.ctReconstructionLinearMap (V.ctLeft x)
            rw [V.ctReconstructionLinearMap_apply, V.ctEval_ctLeft, V.ctEval_ctLeft]
            rw [sub_self, smul_zero, hleftzero, hhalf]
            rw [zero_mul V.ctGenerator, add_zero (V.ctLeft x)]
          · change x ⊗ₜ[ℚ] AddMonoidAlgebra.single (1 : ZMod 2) 1 =
              V.ctReconstructionLinearMap
                (x ⊗ₜ[ℚ] AddMonoidAlgebra.single (1 : ZMod 2) 1)
            have hpositive : V.ctEval (1 : rootsOfUnity 2
                V.cliffordSpinCandidateCoordinateRing)
                (x ⊗ₜ[ℚ] AddMonoidAlgebra.single (1 : ZMod 2) 1) = x := by
              change Algebra.TensorProduct.productMap
                (AlgHom.id ℚ V.cliffordSpinCandidateCoordinateRing)
                (muTwoPointOfRoot (1 : rootsOfUnity 2
                  V.cliffordSpinCandidateCoordinateRing))
                (x ⊗ₜ[ℚ] AddMonoidAlgebra.single (1 : ZMod 2) 1) = x
              rw [Algebra.TensorProduct.productMap_apply_tmul, muTwoPointOfRoot_generator]
              exact mul_one x
            have hnegative : V.ctEval (negOneRootOfUnity
                V.cliffordSpinCandidateCoordinateRing)
                (x ⊗ₜ[ℚ] AddMonoidAlgebra.single (1 : ZMod 2) 1) = -x := by
              change Algebra.TensorProduct.productMap
                (AlgHom.id ℚ V.cliffordSpinCandidateCoordinateRing)
                (muTwoPointOfRoot (negOneRootOfUnity
                  V.cliffordSpinCandidateCoordinateRing))
                (x ⊗ₜ[ℚ] AddMonoidAlgebra.single (1 : ZMod 2) 1) = -x
              rw [Algebra.TensorProduct.productMap_apply_tmul, muTwoPointOfRoot_generator]
              exact mul_neg_one x
            rw [V.ctReconstructionLinearMap_apply, hpositive, hnegative]
            rw [add_neg_cancel, smul_zero, hleftzero, sub_neg_eq_add, hhalf]
            rw [zero_add (V.ctLeft x * V.ctGenerator)]
            change x ⊗ₜ[ℚ] AddMonoidAlgebra.single (1 : ZMod 2) 1 =
              (x ⊗ₜ[ℚ] 1) * (1 ⊗ₜ[ℚ] AddMonoidAlgebra.single (1 : ZMod 2) 1)
            rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      | hadd h k hh hk =>
          rw [TensorProduct.tmul_add, map_add]
          exact congrArg₂ (· + ·) hh hk
      | hsmul q h hh =>
          rw [TensorProduct.tmul_smul, map_smul]
          exact congrArg (q • ·) hh

theorem ctEval_pair_injective :
    Function.Injective (fun z : V.CT =>
      (V.ctEval (1 : rootsOfUnity 2
          V.cliffordSpinCandidateCoordinateRing) z,
        V.ctEval (negOneRootOfUnity
          V.cliffordSpinCandidateCoordinateRing) z)) := by
  intro x y h
  rw [V.ct_reconstruction x, V.ct_reconstruction y]
  have hfst : V.ctEval (1 : rootsOfUnity 2
      V.cliffordSpinCandidateCoordinateRing) x =
      V.ctEval (1 : rootsOfUnity 2
        V.cliffordSpinCandidateCoordinateRing) y := congrArg Prod.fst h
  have hsnd : V.ctEval (negOneRootOfUnity
      V.cliffordSpinCandidateCoordinateRing) x =
      V.ctEval (negOneRootOfUnity
        V.cliffordSpinCandidateCoordinateRing) y := congrArg Prod.snd h
  rw [hfst, hsnd]

theorem ctActionQ_eq_ctLeft_iff (b : V.cliffordSpinCandidateCoordinateRing) :
    V.ctActionQ b = V.ctLeft b ↔
      V.cliffordSpinCandidateNegOneCoordinateAlgEquiv b = b := by
  constructor
  · intro h
    have := congrArg
      (V.ctEval (negOneRootOfUnity
        V.cliffordSpinCandidateCoordinateRing)) h
    rw [V.ctEval_ctLeft] at this
    change (((V.ctEval (negOneRootOfUnity
      V.cliffordSpinCandidateCoordinateRing)).comp V.ctActionQ) b) = b at this
    rw [V.ctEval_negOne_comp_ctActionQ] at this
    exact this
  · intro h
    apply V.ctEval_pair_injective
    apply Prod.ext
    · dsimp only
      rw [V.ctEval_ctLeft]
      change (((V.ctEval (1 : rootsOfUnity 2
          V.cliffordSpinCandidateCoordinateRing)).comp V.ctActionQ) b) = b
      rw [V.ctEval_one_comp_ctActionQ]
      rfl
    · dsimp only
      change (((V.ctEval (negOneRootOfUnity
          V.cliffordSpinCandidateCoordinateRing)).comp V.ctActionQ) b) =
        V.ctEval (negOneRootOfUnity
          V.cliffordSpinCandidateCoordinateRing) (V.ctLeft b)
      rw [V.ctEval_ctLeft]
      rw [V.ctEval_negOne_comp_ctActionQ]
      exact h

theorem csRightQ_eq_csLeftQ_iff_negOne_fixed
    (b : V.cliffordSpinCandidateCoordinateRing) :
    V.csRightQ b = V.csLeftQ b ↔
      V.cliffordSpinCandidateNegOneCoordinateAlgEquiv b = b := by
  rw [← V.ctActionQ_eq_ctLeft_iff]
  constructor
  · intro h
    rw [← V.canQ_csRightQ, ← V.canQ_csLeftQ, h]
  · intro h
    have := congrArg V.canInv h
    rw [V.canInv_ctLeft] at this
    change ((V.canInv.comp V.ctActionQ) b) = V.csLeftQ b at this
    rw [V.canInv_comp_ctActionQ] at this
    exact this

theorem invariant_surjective_iff_tensor_equalizer :
    Function.Surjective V.specialOrthogonalToNegOneInvariantAlgHom ↔
      ∀ b : V.cliffordSpinCandidateCoordinateRing,
        V.csRightQ b = V.csLeftQ b →
          ∃ a : V.specialOrthogonalCoordinateRing,
            V.specialOrthogonalToCliffordSpinCandidateCoordinateAlgHom a = b := by
  constructor
  · intro h b hb
    have hfixed := (V.csRightQ_eq_csLeftQ_iff_negOne_fixed b).mp hb
    obtain ⟨a, ha⟩ := h ⟨b, hfixed⟩
    exact ⟨a, congrArg Subtype.val ha⟩
  · intro h b
    have heq := (V.csRightQ_eq_csLeftQ_iff_negOne_fixed b.1).mpr b.2
    obtain ⟨a, ha⟩ := h b.1 heq
    refine ⟨a, ?_⟩
    apply Subtype.ext
    exact ha

theorem faithfullyFlat_of_tensor_equalizer
    (h : ∀ b : V.cliffordSpinCandidateCoordinateRing,
      V.csRightQ b = V.csLeftQ b →
        ∃ a : V.specialOrthogonalCoordinateRing,
          V.specialOrthogonalToCliffordSpinCandidateCoordinateAlgHom a = b) :
    V.specialOrthogonalToCliffordSpinCandidateCoordinateAlgHom.toRingHom.FaithfullyFlat :=
  V.faithfullyFlat_of_negOneInvariant_surjective
    (V.invariant_surjective_iff_tensor_equalizer.mpr h)

end RationalQuadraticSpaceMatrix
