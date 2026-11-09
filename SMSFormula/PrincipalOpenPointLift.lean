import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Lifting a point through an isomorphism of principal opens

This file packages the affine point lift used by the Spin invariant quotient.
If the principal localizations of `D` and `E` are isomorphic through the away
map of `f : D →ₐ[K] E`, then every `K`-point of `D` where the principal
element is nonzero lifts to a compatible `K`-point of `E`.

The construction extends the point to `D[x⁻¹]`, transports it backward
through the away-map equivalence, and restricts it along `E → E[(f x)⁻¹]`.
-/

noncomputable section

universe u

namespace Algebra

variable {K D E : Type u} [Field K] [CommRing D] [CommRing E]
  [Algebra K D] [Algebra K E]

/-- A field-valued point in a principal open lifts through a bijective away
map, compatibly with the original algebra homomorphism. -/
theorem exists_algHom_comp_eq_of_awayMap_bijective
    (f : D →ₐ[K] E) (x : D)
    (haway : Function.Bijective (Localization.awayMap f.toRingHom x))
    (φ : D →ₐ[K] K) (hx : φ x ≠ 0) :
    ∃ ψ : E →ₐ[K] K, ψ.comp f = φ := by
  let φAway : Localization.Away x →ₐ[K] K :=
    IsLocalization.liftAlgHom (M := Submonoid.powers x) (f := φ) (by
      intro y
      obtain ⟨n, hn⟩ := y.2
      rw [← hn, map_pow]
      exact IsUnit.map (powMonoidHom n : K →* K) (isUnit_iff_ne_zero.mpr hx))
  let e : Localization.Away x ≃ₐ[K] Localization.Away (f x) :=
    AlgEquiv.ofBijective (Localization.awayMapₐ f x) haway
  let ψ : E →ₐ[K] K :=
    φAway.comp <| e.symm.toAlgHom.comp <|
      IsScalarTower.toAlgHom K E (Localization.Away (f x))
  refine ⟨ψ, ?_⟩
  ext d
  change φAway (e.symm (algebraMap E (Localization.Away (f x)) (f d))) = φ d
  have hinv :
      e.symm (algebraMap E (Localization.Away (f x)) (f d)) =
        algebraMap D (Localization.Away x) d := by
    apply e.injective
    simp only [e, AlgEquiv.ofBijective_apply, AlgEquiv.apply_symm_apply]
    change (algebraMap E (Localization.Away (f x))) (f d) =
      IsLocalization.Away.map
        (Localization.Away x) (Localization.Away (f x)) f.toRingHom x
          ((algebraMap D (Localization.Away x)) d)
    unfold IsLocalization.Away.map
    rw [IsLocalization.map_eq]
    rfl
  rw [hinv]
  simp [φAway]

end Algebra
