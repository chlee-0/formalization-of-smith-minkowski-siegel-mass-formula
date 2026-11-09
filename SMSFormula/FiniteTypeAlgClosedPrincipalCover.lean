import Mathlib.RingTheory.RingHom.Bijective
import SMSFormula.FiniteTypeAlgClosedPoint

/-!
# Principal covers detected by algebraically closed points

For a finite-type algebra over an algebraically closed field, a family of
principal opens covers the whole spectrum as soon as it contains every
field-valued point.  Applying the standard localization gluing theorem then
shows that a ring homomorphism which is an isomorphism on all those principal
opens is already an isomorphism globally.
-/

noncomputable section

universe u

namespace Algebra

variable {K D E : Type u} [Field K] [IsAlgClosed K]
  [CommRing D] [CommRing E] [Algebra K D] [Algebra K E]
  [Algebra.FiniteType K D]

/-- Principal opens which contain every algebraically closed point of an
affine finite-type algebra generate the unit ideal. -/
theorem span_eq_top_of_forall_algHom_exists_apply_ne_zero
    (s : Set D)
    (h : ∀ φ : D →ₐ[K] K, ∃ x ∈ s, φ x ≠ 0) :
    Ideal.span s = ⊤ := by
  by_contra htop
  obtain ⟨M, hM, hsM⟩ := Ideal.exists_le_maximal (Ideal.span s) htop
  obtain ⟨φ, hker⟩ := exists_algHom_ker_eq (K := K) (D := D) M hM
  obtain ⟨x, hxs, hx⟩ := h φ
  have hxM : x ∈ M := hsM (Ideal.subset_span hxs)
  apply hx
  change x ∈ RingHom.ker φ.toRingHom
  rw [hker]
  exact hxM

/-- If every algebraically closed point lies in a principal open on which an
algebra map is bijective, then the algebra map itself is bijective. -/
theorem bijective_of_forall_algHom_exists_awayMap_bijective_apply_ne_zero
    (f : D →ₐ[K] E)
    (h : ∀ φ : D →ₐ[K] K, ∃ x : D,
      Function.Bijective (Localization.awayMap f.toRingHom x) ∧ φ x ≠ 0) :
    Function.Bijective f := by
  let s : Set D :=
    {x | Function.Bijective (Localization.awayMap f.toRingHom x)}
  have hs : Ideal.span s = ⊤ :=
    span_eq_top_of_forall_algHom_exists_apply_ne_zero s (fun φ => by
      obtain ⟨x, hxbij, hx⟩ := h φ
      exact ⟨x, hxbij, hx⟩)
  exact RingHom.Bijective.ofLocalizationSpan f.toRingHom s hs
    (fun x => x.property)

end Algebra
