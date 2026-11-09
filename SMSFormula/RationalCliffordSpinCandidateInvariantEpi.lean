import SMSFormula.RationalCliffordSpinCandidateInvariantCanonicalMap

/-!
# The literal Spin invariant quotient is a ring epimorphism over `O(SO)`

Write

```text
A = O(SO), B = O(SpinCandidate), C = B^sigma.
```

The completed comparison gives an isomorphism

```text
B tensor_A B -> B tensor_C B,
```

and `B` is faithfully flat over `C`.  This file descends the comparison twice.
For any `A`-algebra `D`, faithful flatness makes the left base-change map

```text
C tensor_A D -> B tensor_A D
```

injective.  Applying this first with `D=C` and then, after tensor symmetry,
with `D=B` makes the double base-change

```text
C tensor_A C -> B tensor_A B
```

injective.  The canonical tensor quotient sends that double base change to
multiplication in `C`.  Its injectivity therefore proves that multiplication

```text
C tensor_A C -> C
```

is an algebra equivalence.  Equivalently, `A -> C` is a commutative-ring
epimorphism.

This still does not identify `A` and `C`.  An injective finite-presentation
ring epimorphism whose map on spectra is surjective need not be onto in
general; the final comparison must use the algebraic-group structure or an
equivalent stronger quotient theorem.
-/

noncomputable section

set_option maxHeartbeats 5000000
set_option synthInstance.maxHeartbeats 800000

open RationalTamagawa

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

private abbrev A := V.specialOrthogonalCoordinateRing
private abbrev B := V.cliffordSpinCandidateCoordinateRing
private abbrev C := V.negOneInvariantSubalgebra

local instance invariantEpiSelfTower : IsScalarTower V.A V.A V.B :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- The self-tensor of the literal invariant ring over `O(SO)`. -/
abbrev CAC := TensorProduct V.A V.C V.C

/-- The candidate ring tensored with the invariant ring over `O(SO)`. -/
abbrev BAC := TensorProduct V.A V.B V.C

/-- The candidate self-tensor over `O(SO)`. -/
abbrev BAB := TensorProduct V.A V.B V.B

/-- The invariant self-tensor is a `C`-algebra through its left factor. -/
noncomputable instance cacCAlg : Algebra V.C V.CAC :=
  (Algebra.TensorProduct.includeLeft : V.C →ₐ[V.A] V.CAC).toRingHom.toAlgebra

/-- Multiplication on `C tensor_A C`, regarded as a `C`-algebra map through
the left factor. -/
def invariantMultiplication : V.CAC →ₐ[V.C] V.C where
  toFun := Algebra.TensorProduct.productMap
    (AlgHom.id V.A V.C) (AlgHom.id V.A V.C)
  map_one' := map_one _
  map_mul' := map_mul _
  map_zero' := map_zero _
  map_add' := map_add _
  commutes' c := by
    change Algebra.TensorProduct.productMap
      (AlgHom.id V.A V.C) (AlgHom.id V.A V.C)
        (c ⊗ₜ[V.A] (1 : V.C)) = c
    simp

/-- Base change of the left invariant factor along the faithfully flat map
`C -> B`. -/
def leftBaseChange (D : Type*) [CommRing D] [Algebra V.A D] :
    TensorProduct V.A V.C D →ₐ[V.A] TensorProduct V.A V.B D :=
  Algebra.TensorProduct.map (IsScalarTower.toAlgHom V.A V.C V.B)
    (AlgHom.id V.A D)

theorem leftBaseChange_tmul (D : Type*) [CommRing D] [Algebra V.A D]
    (c : V.C) (d : D) :
    V.leftBaseChange D (c ⊗ₜ[V.A] d) = (c : V.B) ⊗ₜ[V.A] d := by
  simp [leftBaseChange]

/-- Faithful flatness of `C -> B` makes left base change injective for every
`A`-algebra. -/
theorem leftBaseChange_injective (D : Type*) [CommRing D] [Algebra V.A D] :
    Function.Injective (V.leftBaseChange D) := by
  letI : Module.FaithfullyFlat V.C V.B :=
    RingHom.faithfullyFlat_algebraMap_iff.mp
      V.negOneInvariantToCliffordSpinCandidateCoordinateRingHom_faithfullyFlat
  let e := Algebra.TensorProduct.cancelBaseChange V.A V.C V.B V.B D
  let j : (TensorProduct V.A V.C D) →ₗ[V.C]
      TensorProduct V.C V.B (TensorProduct V.A V.C D) :=
    TensorProduct.mk V.C V.B (TensorProduct V.A V.C D) 1
  have hj : Function.Injective j :=
    Module.FaithfullyFlat.tensorProduct_mk_injective (A := V.C) (B := V.B)
      (TensorProduct V.A V.C D)
  have he : Function.Injective e := e.injective
  have hej (z : TensorProduct V.A V.C D) :
      e (j z) = V.leftBaseChange D z := by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul c d =>
        simp [e, j, leftBaseChange]
        apply congrArg (fun b : V.B => b ⊗ₜ[V.A] d)
        change algebraMap V.C V.B c * 1 = algebraMap V.C V.B c
        rw [mul_one]
  intro x y h
  apply hj
  apply he
  rw [hej, hej, h]

/-- Base change of the right invariant factor in `B tensor_A C`. -/
def rightBaseChange : V.BAC →ₐ[V.A] V.BAB :=
  Algebra.TensorProduct.map (AlgHom.id V.A V.B)
    (IsScalarTower.toAlgHom V.A V.C V.B)

theorem leftBaseChange_comm_eq_rightBaseChange (z : V.BAC) :
    (TensorProduct.comm V.A V.B V.B)
        (V.leftBaseChange V.B ((TensorProduct.comm V.A V.B V.C) z)) =
      V.rightBaseChange z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul b c => simp [leftBaseChange, rightBaseChange]

/-- Right base change is injective by tensor symmetry and left faithful-flat
base change. -/
theorem rightBaseChange_injective : Function.Injective V.rightBaseChange := by
  intro x y h
  apply (TensorProduct.comm V.A V.B V.C).injective
  apply V.leftBaseChange_injective V.B
  apply (TensorProduct.comm V.A V.B V.B).injective
  rw [V.leftBaseChange_comm_eq_rightBaseChange,
    V.leftBaseChange_comm_eq_rightBaseChange, h]

/-- Simultaneous base change of both invariant factors from `C` to `B`. -/
def doubleBaseChange : V.CAC →ₐ[V.A] V.BAB :=
  Algebra.TensorProduct.map (IsScalarTower.toAlgHom V.A V.C V.B)
    (IsScalarTower.toAlgHom V.A V.C V.B)

theorem rightBaseChange_leftBaseChange (z : V.CAC) :
    V.rightBaseChange (V.leftBaseChange V.C z) = V.doubleBaseChange z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul c d => simp [leftBaseChange, rightBaseChange, doubleBaseChange]

/-- Double base change is injective by two applications of faithful-flat base
change. -/
theorem doubleBaseChange_injective : Function.Injective V.doubleBaseChange := by
  intro x y h
  apply V.leftBaseChange_injective V.C
  apply V.rightBaseChange_injective
  rw [V.rightBaseChange_leftBaseChange,
    V.rightBaseChange_leftBaseChange, h]

/-- After the canonical tensor quotient, double base change is multiplication
in the invariant ring followed by the left candidate inclusion. -/
theorem csToInvariant_doubleBaseChange (z : V.CAC) :
    V.csToInvariant (V.doubleBaseChange z) =
      (Algebra.TensorProduct.includeLeft : V.B →ₐ[V.C] V.CSI)
        (algebraMap V.C V.B (V.invariantMultiplication z)) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul c d =>
      simp only [doubleBaseChange, Algebra.TensorProduct.map_tmul,
        V.csToInvariant_tmul]
      change (c : V.B) ⊗ₜ[V.C] (d : V.B) = ((c * d : V.C) : V.B) ⊗ₜ[V.C] 1
      have hd : (d : V.B) = d • (1 : V.B) := by
        change algebraMap V.C V.B d = algebraMap V.C V.B d * 1
        rw [mul_one]
      have hmul : d • (c : V.B) = ((c * d : V.C) : V.B) := by
        change algebraMap V.C V.B d * algebraMap V.C V.B c =
          algebraMap V.C V.B (c * d)
        rw [map_mul, mul_comm]
      exact (congrArg (fun x : V.B => (c : V.B) ⊗ₜ[V.C] x) hd).trans
        ((TensorProduct.tmul_smul d (c : V.B) (1 : V.B)).trans
          (congrArg (fun x : V.B => x ⊗ₜ[V.C] (1 : V.B)) hmul))

/-- Multiplication `C tensor_A C -> C` is injective. -/
theorem invariantMultiplication_injective :
    Function.Injective V.invariantMultiplication := by
  intro x y h
  apply V.doubleBaseChange_injective
  apply V.csToInvariant_injective
  rw [V.csToInvariant_doubleBaseChange,
    V.csToInvariant_doubleBaseChange, h]

/-- Multiplication `C tensor_A C -> C` is tautologically surjective. -/
theorem invariantMultiplication_surjective :
    Function.Surjective V.invariantMultiplication := by
  intro c
  refine ⟨1 ⊗ₜ[V.A] c, ?_⟩
  simp [invariantMultiplication]

/-- The multiplication map exhibits `C tensor_A C` as `C`. -/
def invariantMultiplicationAlgEquiv : V.CAC ≃ₐ[V.C] V.C :=
  AlgEquiv.ofBijective V.invariantMultiplication
    ⟨V.invariantMultiplication_injective,
      V.invariantMultiplication_surjective⟩

/-- The implemented comparison `O(SO) -> B^sigma` is a commutative-ring
epimorphism. -/
theorem specialOrthogonalToNegOneInvariant_isEpi :
    Algebra.IsEpi V.A V.C := by
  rw [Algebra.isEpi_iff_forall_one_tmul_eq]
  intro c
  apply V.invariantMultiplication_injective
  simp [invariantMultiplication]

end RationalQuadraticSpaceMatrix
