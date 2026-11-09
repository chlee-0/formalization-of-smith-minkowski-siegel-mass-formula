import SMSFormula.RationalCliffordSpinCandidateInvariantQuotient

/-!
# Comparing the Spin torsor canonical maps over `O(SO)` and its invariants

Write

```text
A = O(SO), B = O(SpinCandidate), C = B^sigma.
```

The completed torsor calculation gives an `A`-canonical-map equivalence

```text
B tensor_A B ~= B tensor_Q Q[ZMod 2].
```

This file constructs the analogous canonical map over the literal invariant
ring `C`.  The nontrivial action is `C`-linear because every element of `C` is
fixed.  The natural tensor quotient

```text
B tensor_A B -> B tensor_C B
```

intertwines the two canonical maps.  It is surjective by tensor induction and
injective because the completed `A`-canonical map is an equivalence.  Hence
both the tensor quotient and the `C`-canonical map are algebra equivalences.

This is the canonical-map comparison needed before faithfully-flat descent.
It does not prove that `A -> C` is an epimorphism or an isomorphism; reflecting
the corresponding tensor-multiplication map along the faithfully flat
extension `C -> B` remains a separate step.
-/

noncomputable section

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000

open RationalTamagawa

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

private abbrev A := V.specialOrthogonalCoordinateRing
private abbrev B := V.cliffordSpinCandidateCoordinateRing
private abbrev C := V.negOneInvariantSubalgebra

/-- The self-tensor of the candidate coordinate ring over its literal fixed
subalgebra. -/
abbrev CSI := TensorProduct V.C V.B V.B

/-- The target of the canonical map as an algebra over the invariant ring,
through the left candidate factor. -/
noncomputable instance ctInvariantAlg : Algebra V.C V.CT :=
  RingHom.toAlgebra (R := V.C) (S := V.CT)
    (V.ctLeftQ.toRingHom.comp (algebraMap V.C V.B))

/-- The left candidate point in the canonical-map target, over `C`. -/
def ctLeftInvariant : V.B →ₐ[V.C] V.CT where
  toFun := V.ctLeftQ
  map_one' := V.ctLeftQ.map_one'
  map_mul' := V.ctLeftQ.map_mul'
  map_zero' := V.ctLeftQ.map_zero'
  map_add' := V.ctLeftQ.map_add'
  commutes' _ := rfl

/-- The universally translated candidate point is `C`-linear because the
elements of `C` are fixed by the nontrivial scalar action. -/
def ctActionInvariant : V.B →ₐ[V.C] V.CT where
  toFun := V.ctActionQ
  map_one' := V.ctActionQ.map_one'
  map_mul' := V.ctActionQ.map_mul'
  map_zero' := V.ctActionQ.map_zero'
  map_add' := V.ctActionQ.map_add'
  commutes' c := by
    change V.ctActionQ (c : V.B) = V.ctLeftQ (c : V.B)
    exact (V.ctActionQ_eq_ctLeft_iff (c : V.B)).mpr c.2

/-- The torsor canonical map over the literal invariant ring. -/
def canInvariant : V.CSI →ₐ[V.C] V.CT := by
  letI : SMul V.C V.CT := V.ctInvariantAlg.toSMul
  letI : IsScalarTower V.C V.C V.CT :=
    IsScalarTower.of_algebraMap_eq' rfl
  exact Algebra.TensorProduct.lift (R := V.C) (S := V.C)
    (A := V.B) (B := V.B) (C := V.CT) V.ctLeftInvariant V.ctActionInvariant
    (fun left right => show V.ctLeftInvariant left * V.ctActionInvariant right =
      V.ctActionInvariant right * V.ctLeftInvariant left from
        mul_comm (V.ctLeftInvariant left : V.CT) (V.ctActionInvariant right : V.CT))

/-- The invariant-base self-tensor as an `O(SO)`-algebra through its left
factor. -/
noncomputable instance csiAAlg : Algebra V.A V.CSI :=
  RingHom.toAlgebra (R := V.A) (S := V.CSI)
    ((Algebra.TensorProduct.includeLeft (R := V.C) (A := V.B) (B := V.B) :
      V.B →ₐ[V.C] V.CSI).toRingHom.comp (algebraMap V.A V.B))

/-- The natural quotient from the self-tensor over `O(SO)` to the self-tensor
over the larger invariant ring. -/
def csToInvariant : V.CS →ₐ[V.A] V.CSI := by
  letI : SMul V.A V.CSI := V.csiAAlg.toSMul
  letI : IsScalarTower V.A V.A V.CSI :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower V.A V.A V.B :=
    IsScalarTower.of_algebraMap_eq' rfl
  let leftA : V.B →ₐ[V.A] V.CSI := {
    toFun := (Algebra.TensorProduct.includeLeft
      (R := V.C) (A := V.B) (B := V.B) : V.B →ₐ[V.C] V.CSI)
    map_one' := (Algebra.TensorProduct.includeLeft
      (R := V.C) (A := V.B) (B := V.B)).map_one'
    map_mul' := (Algebra.TensorProduct.includeLeft
      (R := V.C) (A := V.B) (B := V.B)).map_mul'
    map_zero' := (Algebra.TensorProduct.includeLeft
      (R := V.C) (A := V.B) (B := V.B)).map_zero'
    map_add' := (Algebra.TensorProduct.includeLeft
      (R := V.C) (A := V.B) (B := V.B)).map_add'
    commutes' := fun _ => rfl }
  let rightA : V.B →ₐ[V.A] V.CSI := {
    toFun := (Algebra.TensorProduct.includeRight
      (R := V.C) (A := V.B) (B := V.B) : V.B →ₐ[V.C] V.CSI)
    map_one' := (Algebra.TensorProduct.includeRight
      (R := V.C) (A := V.B) (B := V.B)).map_one'
    map_mul' := (Algebra.TensorProduct.includeRight
      (R := V.C) (A := V.B) (B := V.B)).map_mul'
    map_zero' := (Algebra.TensorProduct.includeRight
      (R := V.C) (A := V.B) (B := V.B)).map_zero'
    map_add' := (Algebra.TensorProduct.includeRight
      (R := V.C) (A := V.B) (B := V.B)).map_add'
    commutes' := fun a => by
      change 1 ⊗ₜ[V.C]
          V.specialOrthogonalToCliffordSpinCandidateCoordinateAlgHom a =
        V.specialOrthogonalToCliffordSpinCandidateCoordinateAlgHom a ⊗ₜ 1
      exact (Algebra.TensorProduct.tmul_one_eq_one_tmul
        (R := V.C) (A := V.B) (B := V.B)
        (V.specialOrthogonalToNegOneInvariantAlgHom a)).symm }
  exact Algebra.TensorProduct.lift
    (R := V.A) (S := V.A) (A := V.B) (B := V.B) (C := V.CSI)
    leftA rightA (fun x y => by
      change leftA x * rightA y = rightA y * leftA x
      exact mul_comm (leftA x : V.CSI) (rightA y : V.CSI))

theorem csToInvariant_tmul (x y : V.B) :
    V.csToInvariant (x ⊗ₜ[V.A] y) = x ⊗ₜ[V.C] y := by
  letI : SMul V.A V.CSI := V.csiAAlg.toSMul
  letI : IsScalarTower V.A V.A V.CSI :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower V.A V.A V.B :=
    IsScalarTower.of_algebraMap_eq' rfl
  simp [csToInvariant]

theorem csToInvariant_surjective : Function.Surjective V.csToInvariant := by
  intro z
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | add x y hx hy =>
      obtain ⟨x', rfl⟩ := hx
      obtain ⟨y', rfl⟩ := hy
      exact ⟨x' + y', by simp⟩
  | tmul x y => exact ⟨x ⊗ₜ[V.A] y, V.csToInvariant_tmul x y⟩

@[simp] theorem csToInvariant_csLeftQ (b : V.B) :
    V.csToInvariant (V.csLeftQ b) =
      (Algebra.TensorProduct.includeLeft : V.B →ₐ[V.C] V.CSI) b := by
  change V.csToInvariant (b ⊗ₜ[V.A] 1) = b ⊗ₜ[V.C] 1
  exact V.csToInvariant_tmul b 1

@[simp] theorem csToInvariant_csRightQ (b : V.B) :
    V.csToInvariant (V.csRightQ b) =
      (Algebra.TensorProduct.includeRight : V.B →ₐ[V.C] V.CSI) b := by
  change V.csToInvariant (1 ⊗ₜ[V.A] b) = 1 ⊗ₜ[V.C] b
  exact V.csToInvariant_tmul 1 b

/-- The canonical map over `C` after the tensor quotient is literally the
completed canonical map over `A`. -/
theorem canInvariant_csToInvariant (z : V.CS) :
    V.canInvariant (V.csToInvariant z) = V.canQ z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul x y =>
      rw [V.csToInvariant_tmul, V.canQ_tmul]
      simp only [canInvariant, Algebra.TensorProduct.lift_tmul]
      rfl

theorem csToInvariant_injective : Function.Injective V.csToInvariant := by
  intro x y h
  apply V.canonicalMapAlgEquiv.injective
  change V.canQ x = V.canQ y
  rw [← V.canInvariant_csToInvariant x,
    ← V.canInvariant_csToInvariant y, h]

/-- The natural tensor quotient `B tensor_A B -> B tensor_C B` is an
`A`-algebra equivalence. -/
def csToInvariantAlgEquiv : V.CS ≃ₐ[V.A] V.CSI :=
  AlgEquiv.ofBijective V.csToInvariant
    ⟨V.csToInvariant_injective, V.csToInvariant_surjective⟩

/-- An inverse to the invariant-base canonical map, obtained by composing the
completed inverse over `A` with the tensor quotient. -/
def canInvInvariant : V.CT →ₐ[V.C] V.CSI where
  toFun z := V.csToInvariant (V.canInv z)
  map_one' := (congrArg V.csToInvariant V.canInv.map_one').trans V.csToInvariant.map_one'
  map_mul' x y := (congrArg V.csToInvariant (V.canInv.map_mul' x y)).trans
    (V.csToInvariant.map_mul' (V.canInv x) (V.canInv y))
  map_zero' := (congrArg V.csToInvariant V.canInv.map_zero').trans V.csToInvariant.map_zero'
  map_add' x y := (congrArg V.csToInvariant (V.canInv.map_add' x y)).trans
    (V.csToInvariant.map_add' (V.canInv x) (V.canInv y))
  commutes' c := by
    change V.csToInvariant (V.canInv (V.ctLeft (c : V.B))) =
      (Algebra.TensorProduct.includeLeft : V.B →ₐ[V.C] V.CSI) c
    rw [V.canInv_ctLeft, V.csToInvariant_csLeftQ]

theorem canInvariant_comp_canInvInvariant :
    V.canInvariant.comp V.canInvInvariant = AlgHom.id V.C V.CT := by
  apply AlgHom.ext
  intro z
  change V.canInvariant (V.csToInvariant (V.canInv z)) = z
  rw [V.canInvariant_csToInvariant]
  exact DFunLike.congr_fun V.canQ_comp_canInv z

theorem canInvInvariant_comp_canInvariant :
    V.canInvInvariant.comp V.canInvariant = AlgHom.id V.C V.CSI := by
  apply AlgHom.ext
  intro z
  obtain ⟨w, rfl⟩ := V.csToInvariant_surjective z
  change V.csToInvariant
      (V.canInv (V.canInvariant (V.csToInvariant w))) = V.csToInvariant w
  rw [V.canInvariant_csToInvariant]
  exact congrArg V.csToInvariant (DFunLike.congr_fun V.canInv_comp_canQ w)

/-- The torsor canonical map over the literal invariant ring is an algebra
equivalence. -/
def canonicalMapInvariantAlgEquiv : V.CSI ≃ₐ[V.C] V.CT :=
  AlgEquiv.ofAlgHom V.canInvariant V.canInvInvariant
    V.canInvariant_comp_canInvInvariant V.canInvInvariant_comp_canInvariant

end RationalQuadraticSpaceMatrix
