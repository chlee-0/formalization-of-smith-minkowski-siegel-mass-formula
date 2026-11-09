import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.RingTheory.FiniteStability
import Mathlib.Tactic.Trace
import SMSFormula.FiniteTypeAlgClosedPoint
import SMSFormula.PrincipalLocalizationAmbientBaseChange
import SMSFormula.PrincipalOpenPointLift
import SMSFormula.RationalCliffordSpinCandidateInvariantGenericPatch

/-!
# The Spin invariant isomorphism patch over the rational algebraic closure

The generic principal patch for

```text
O(SO_V) -> O(SpinCandidate_V)^sigma
```

is tensored from `Q` to `AlgebraicClosure Q`.  The scalar-extended localized
coordinate rings remain algebra-equivalent.  Faithful flatness of the field
extension also shows that the base-changed principal element is nonnilpotent,
and hence is avoided by some prime of the base-changed `SO` coordinate ring.

This certifies a nonempty geometric isomorphism patch.  It does not choose a
rational point, translate the patch, or prove the global comparison flat.
-/

noncomputable section

open TensorProduct

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

private abbrev A := V.specialOrthogonalCoordinateRing
private abbrev C := V.negOneInvariantSubalgebra
private abbrev Qbar := AlgebraicClosure ℚ

local instance closureInvariantCommRing : CommRing V.C :=
  V.negOneInvariantSubalgebra.toCommRing

local instance closureInvariantCommSemiring : CommSemiring V.C :=
  (closureInvariantCommRing V).toCommSemiring

example : closureInvariantCommSemiring V =
    V.negOneInvariantSubalgebra.toCommSemiring := rfl

local instance invariantAlgebraicClosureRatTower :
    IsScalarTower ℚ V.specialOrthogonalCoordinateRing V.C :=
  IsScalarTower.of_algebraMap_eq' (R := ℚ)
    (S := V.specialOrthogonalCoordinateRing) (A := V.C) rfl

attribute [local instance] Algebra.TensorProduct.rightAlgebra

local instance closureSourceTensorCommRing : CommRing (V.A ⊗[ℚ] Qbar) :=
  Algebra.TensorProduct.instCommRing (R := ℚ) (A := V.A) (B := Qbar)

local instance closureInvariantTensorCommRing : CommRing (V.C ⊗[ℚ] Qbar) :=
  Algebra.TensorProduct.instCommRing (R := ℚ) (A := V.C) (B := Qbar)

local instance closureSourceTensorCommSemiring : CommSemiring (V.A ⊗[ℚ] Qbar) :=
  (closureSourceTensorCommRing V).toCommSemiring

local instance closureInvariantTensorCommSemiring : CommSemiring (V.C ⊗[ℚ] Qbar) :=
  (closureInvariantTensorCommRing V).toCommSemiring

example : closureSourceTensorCommSemiring V =
    Algebra.TensorProduct.instCommSemiring (R := ℚ) (A := V.A) (B := Qbar) := rfl

example : closureInvariantTensorCommSemiring V =
    Algebra.TensorProduct.instCommSemiring (R := ℚ) (A := V.C) (B := Qbar) := rfl

example : (Algebra.TensorProduct.instCommRing
    (R := ℚ) (A := V.A) (B := Qbar)).toCommSemiring.toSemiring =
    Algebra.TensorProduct.instSemiring (R := ℚ) (A := V.A) (B := Qbar) := rfl

example : (Algebra.TensorProduct.instCommRing
    (R := ℚ) (A := V.C) (B := Qbar)).toCommSemiring.toSemiring =
    Algebra.TensorProduct.instSemiring (R := ℚ) (A := V.C) (B := Qbar) := rfl

/-- The invariant quotient coordinate homomorphism after base change to the
rational algebraic closure, in the right-tensor orientation. -/
noncomputable def specialOrthogonalToNegOneInvariantAlgebraicClosureAlgHom :
    V.A ⊗[ℚ] Qbar →ₐ[Qbar] V.C ⊗[ℚ] Qbar :=
  Algebra.TensorProduct.mapRightAlgHom (K := Qbar)
    (V.specialOrthogonalToNegOneInvariantAlgHom.restrictScalars ℚ)

@[simp]
theorem specialOrthogonalToNegOneInvariantAlgebraicClosureAlgHom_tmul
    (a : V.A) (k : Qbar) :
    V.specialOrthogonalToNegOneInvariantAlgebraicClosureAlgHom (a ⊗ₜ[ℚ] k) =
      V.specialOrthogonalToNegOneInvariantAlgHom a ⊗ₜ[ℚ] k := by
  simp [specialOrthogonalToNegOneInvariantAlgebraicClosureAlgHom]

/-- Scalar extension of one certified invariant-quotient principal patch to
the rational algebraic closure. -/
noncomputable def negOneInvariantAwayAlgebraicClosureAlgEquiv
    (d : V.A)
    (h : Function.Bijective
      (Localization.awayMap
        V.specialOrthogonalToNegOneInvariantAlgHom.toRingHom d)) :
    (Qbar ⊗[ℚ] Localization.Away d) ≃ₐ[Qbar]
      (Qbar ⊗[ℚ]
        Localization.Away (V.specialOrthogonalToNegOneInvariantAlgHom d)) :=
  Localization.awayMapScalarExtensionAlgEquiv (K := Qbar)
    (V.specialOrthogonalToNegOneInvariantAlgHom.restrictScalars ℚ) d h

/-- Every minimal component supplies a scalar-extended principal isomorphism
patch whose defining element is avoided by a prime over the algebraic
closure.  The last clause is the affine nonemptiness certificate for that
principal open. -/
theorem exists_negOneInvariant_algebraicClosure_patch_of_mem_minimalPrimes
    (p : Ideal V.A) (hp : p ∈ minimalPrimes V.A) :
    ∃ d : V.A, d ∉ p ∧
      Nonempty
        ((Qbar ⊗[ℚ] Localization.Away d) ≃ₐ[Qbar]
          (Qbar ⊗[ℚ]
            Localization.Away
              (V.specialOrthogonalToNegOneInvariantAlgHom d))) ∧
      ¬ IsNilpotent
        (Algebra.TensorProduct.includeRight d : Qbar ⊗[ℚ] V.A) ∧
      ∃ q : Ideal (Qbar ⊗[ℚ] V.A), q.IsPrime ∧
        Algebra.TensorProduct.includeRight d ∉ q := by
  obtain ⟨d, hd, hbij⟩ :=
    V.exists_negOneInvariant_awayMap_bijective_of_mem_minimalPrimes p hp
  letI : p.IsPrime := hp.1.1
  have hbij' : Function.Bijective
      (Localization.awayMap
        V.specialOrthogonalToNegOneInvariantAlgHom.toRingHom d) := by
    simpa only [] using hbij
  refine ⟨d, hd, ⟨V.negOneInvariantAwayAlgebraicClosureAlgEquiv d hbij'⟩,
    Algebra.TensorProduct.includeRight_not_isNilpotent_of_not_mem
      (R := ℚ) (K := AlgebraicClosure ℚ) p d hd, ?_⟩
  exact Algebra.TensorProduct.exists_prime_not_mem_includeRight
    (R := ℚ) (K := AlgebraicClosure ℚ) p d hd

set_option backward.isDefEq.respectTransparency false in
set_option diagnostics true in
/-- Every minimal component supplies a literal principal-open isomorphism
patch for the invariant comparison after base change to the rational
algebraic closure.  The base-changed ambient rings use the right-tensor
orientation `A ⊗[Q] Qbar` and `C ⊗[Q] Qbar`. -/
theorem exists_negOneInvariant_algebraicClosure_ambientAwayMap_bijective_of_mem_minimalPrimes
    (p : Ideal V.A) (hp : p ∈ minimalPrimes V.A) :
    ∃ d : V.A, d ∉ p ∧
      Function.Bijective
        (Localization.awayMap
          V.specialOrthogonalToNegOneInvariantAlgebraicClosureAlgHom.toRingHom
          (Algebra.TensorProduct.includeLeft
            (R := ℚ) (S := ℚ) (A := V.A) (B := Qbar) d)) ∧
      ¬ IsNilpotent
        (Algebra.TensorProduct.includeLeft
          (R := ℚ) (S := ℚ) (A := V.A) (B := Qbar) d) ∧
      ∃ q : Ideal (V.A ⊗[ℚ] Qbar), q.IsPrime ∧
        Algebra.TensorProduct.includeLeft
          (R := ℚ) (S := ℚ) (A := V.A) (B := Qbar) d ∉ q := by
  trace "closure ambient: proof entry"
  obtain ⟨d, hd, hbij⟩ :=
    V.exists_negOneInvariant_awayMap_bijective_of_mem_minimalPrimes p hp
  trace "closure ambient: generic patch obtained"
  letI : p.IsPrime := hp.1.1
  let comparison : V.A →ₐ[ℚ] V.C :=
    V.specialOrthogonalToNegOneInvariantAlgHom.restrictScalars ℚ
  have hrestricted :
      comparison.toRingHom = algebraMap V.A V.C := by
    apply RingHom.ext
    intro coordinate
    exact V.specialOrthogonalToNegOneInvariantAlgHom.commutes coordinate
  trace "closure ambient: restricted-map equality constructed"
  have hbijRestricted : Function.Bijective
      (Localization.awayMap comparison.toRingHom d) := by
    rw [hrestricted]
    exact hbij
  trace "closure ambient: restricted away-map premise constructed"
  have hbaseChange : Function.Bijective
      (Localization.awayMap
        (Algebra.TensorProduct.mapRightAlgHom
          (R := ℚ) (K := Qbar) (A := V.A) (B := V.C) comparison).toRingHom
        (Algebra.TensorProduct.includeLeft
          (R := ℚ) (S := ℚ) (A := V.A) (B := Qbar) d)) := by
    trace "closure ambient: scalar-extension target formed"
    have scalarExtension :=
      Algebra.TensorProduct.awayMapRightScalarExtension_bijective
        (R := ℚ) (K := Qbar) (A := V.A) (B := V.C) comparison d
    trace "closure ambient: scalar-extension API specialized before premise"
    exact scalarExtension hbijRestricted
  trace "closure ambient: scalar-extension conclusion inferred"
  refine ⟨d, hd, ?_,
    Algebra.TensorProduct.includeLeft_not_isNilpotent_of_not_mem
      (R := ℚ) (K := Qbar) p d hd, ?_⟩
  · trace "closure ambient: converting scalar-extension conclusion"
    exact hbaseChange
  · trace "closure ambient: constructing prime witness"
    exact Algebra.TensorProduct.exists_prime_not_mem_includeLeft
      (R := ℚ) (K := Qbar) p d hd
  trace "closure ambient: proof body completed"

/-- Every minimal component supplies a literal principal-open isomorphism
patch together with an algebraic-closure-valued point in that open.  This is
the first actual geometric point in the invariant-quotient comparison; it is
not a rational, real, or local point of the original Spin cover. -/
theorem exists_negOneInvariant_algebraicClosure_point_of_mem_minimalPrimes
    (p : Ideal V.A) (hp : p ∈ minimalPrimes V.A) :
    ∃ d : V.A, d ∉ p ∧
      Function.Bijective
        (Localization.awayMap
          V.specialOrthogonalToNegOneInvariantAlgebraicClosureAlgHom.toRingHom
          (Algebra.TensorProduct.includeLeft
            (R := ℚ) (S := ℚ) (A := V.A) (B := Qbar) d)) ∧
      ∃ φ : (V.A ⊗[ℚ] Qbar) →ₐ[Qbar] Qbar,
        φ (Algebra.TensorProduct.includeLeft
          (R := ℚ) (S := ℚ) (A := V.A) (B := Qbar) d) ≠ 0 := by
  obtain ⟨d, hd, hbij, hnonNilpotent, _⟩ :=
    V.exists_negOneInvariant_algebraicClosure_ambientAwayMap_bijective_of_mem_minimalPrimes
      p hp
  refine ⟨d, hd, hbij, ?_⟩
  letI : Algebra.FiniteType Qbar (V.A ⊗[ℚ] Qbar) :=
    Algebra.FiniteType.of_surjective
      (Algebra.TensorProduct.commRight ℚ Qbar V.A).toAlgHom
      (Algebra.TensorProduct.commRight ℚ Qbar V.A).surjective
  exact Algebra.exists_algHom_apply_ne_zero_of_not_isNilpotent
    (K := Qbar) (D := V.A ⊗[ℚ] Qbar)
    (Algebra.TensorProduct.includeLeft
      (R := ℚ) (S := ℚ) (A := V.A) (B := Qbar) d) hnonNilpotent

set_option backward.isDefEq.respectTransparency false in
set_option diagnostics true in
/-- Every minimal component supplies compatible algebraic-closure-valued
points of the base-changed `SO` carrier and the literal invariant quotient,
both lying over the completed principal-open isomorphism patch. -/
theorem exists_negOneInvariant_algebraicClosure_compatible_points_of_mem_minimalPrimes
    (p : Ideal V.A) (hp : p ∈ minimalPrimes V.A) :
    ∃ d : V.A, d ∉ p ∧
      Function.Bijective
        (Localization.awayMap
          V.specialOrthogonalToNegOneInvariantAlgebraicClosureAlgHom.toRingHom
          (Algebra.TensorProduct.includeLeft
            (R := ℚ) (S := ℚ) (A := V.A) (B := Qbar) d)) ∧
      ∃ φA : (V.A ⊗[ℚ] Qbar) →ₐ[Qbar] Qbar,
        φA (Algebra.TensorProduct.includeLeft
          (R := ℚ) (S := ℚ) (A := V.A) (B := Qbar) d) ≠ 0 ∧
        ∃ φC : (V.C ⊗[ℚ] Qbar) →ₐ[Qbar] Qbar,
          φC.comp V.specialOrthogonalToNegOneInvariantAlgebraicClosureAlgHom = φA := by
  trace "closure compatible: proof entry"
  obtain ⟨d, hd, hbij, φA, hφA⟩ :=
    V.exists_negOneInvariant_algebraicClosure_point_of_mem_minimalPrimes p hp
  trace "closure compatible: source point obtained"
  let comparison : (V.A ⊗[ℚ] Qbar) →ₐ[Qbar] (V.C ⊗[ℚ] Qbar) :=
    V.specialOrthogonalToNegOneInvariantAlgebraicClosureAlgHom
  let principal : V.A ⊗[ℚ] Qbar :=
    Algebra.TensorProduct.includeLeft
      (R := ℚ) (S := ℚ) (A := V.A) (B := Qbar) d
  have hbijComparison : Function.Bijective
      (Localization.awayMap comparison.toRingHom principal) := by
    simpa only [comparison, principal] using hbij
  trace "closure compatible: named away-map premise formed"
  have hlift : ∃ φC : (V.C ⊗[ℚ] Qbar) →ₐ[Qbar] Qbar,
      φC.comp comparison = φA := by
    trace "closure compatible: point-lift target formed"
    exact Algebra.exists_algHom_comp_eq_of_awayMap_bijective
      (K := Qbar) (D := V.A ⊗[ℚ] Qbar) (E := V.C ⊗[ℚ] Qbar)
      comparison principal hbijComparison φA hφA
  obtain ⟨φC, hφC⟩ := hlift
  trace "closure compatible: lifted point obtained"
  exact ⟨d, hd, hbij, φA, hφA, φC, hφC⟩
  trace "closure compatible: proof body completed"

end RationalQuadraticSpaceMatrix
