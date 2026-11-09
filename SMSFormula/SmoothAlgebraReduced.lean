import Mathlib.AlgebraicGeometry.Geometrically.Reduced
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.LocalProperties.Reduced
import Mathlib.RingTheory.RingHom.LocallyStandardSmooth
import Mathlib.RingTheory.Unramified.Field

/-!
# Smooth algebras over fields are reduced

Mathlib has the ingredients for the standard theorem that a smooth algebra
over a field is reduced, but not the assembled implication.  This file closes
that generic bridge in three steps.

First, an étale scheme morphism is geometrically reduced: after arbitrary
field base change it remains étale, and every affine chart of an étale scheme
over a field has a formally unramified coordinate algebra, hence is reduced.
It follows from the existing flat geometrically-reduced theorem that an étale
algebra over a reduced Noetherian ring is reduced.

Next, every standard-smooth algebra factors étale over a polynomial ring.
Polynomial rings over fields are reduced and Noetherian, so standard-smooth
algebras over fields are reduced.  Finally, a smooth algebra is covered by
standard-smooth principal localizations.  Reducedness is glued directly: if a
nilpotent vanishes in every chart, suitable powers of the covering elements
annihilate it, and those powers still span the unit ideal.
-/

noncomputable section

open CategoryTheory
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-- An étale scheme over a field is reduced. -/
theorem isReduced_of_etale_to_spec_field
    {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) [Etale f] : IsReduced X := by
  letI (i : X.affineCover.I₀) : IsReduced (X.affineCover.X i) := by
    let g := X.affineCover.f i ≫ f
    haveI : Etale g := Etale.etale_comp _ _
    let A := Γ(X.affineCover.X i, ⊤)
    let φ : K →+* A :=
      (g.appLE ⊤ ⊤ (by simp)).hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom
    algebraize [φ]
    have happ : (g.appLE ⊤ ⊤ (by simp)).hom.Etale :=
      g.etale_appLE (isAffineOpen_top _) (isAffineOpen_top _) (by simp)
    have hφ : φ.Etale := RingHom.Etale.stableUnderComposition _ _
      (RingHom.Etale.of_bijective
        (Scheme.ΓSpecIso (.of K)).symm.commRingCatIsoToRingEquiv.bijective) happ
    haveI : Algebra.Etale K A := RingHom.etale_algebraMap.mp hφ
    haveI : _root_.IsReduced A :=
      Algebra.FormallyUnramified.isReduced_of_field K A
    exact isReduced_of_isAffine_isReduced (X.affineCover.X i)
  exact IsReduced.of_openCover X X.affineCover

/-- Étale morphisms are geometrically reduced. -/
instance (priority := 900) etale_geometricallyReduced
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Etale f] : GeometricallyReduced f where
  geometrically_isReduced := by
    intro K _ y Z fst snd h
    haveI : Etale snd := MorphismProperty.of_isPullback h inferInstance
    exact isReduced_of_etale_to_spec_field snd

end AlgebraicGeometry

namespace RingHom

/-- The target of an étale map from a reduced Noetherian ring is reduced. -/
theorem Etale.isReduced_of_isReduced_of_isNoetherianRing
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : f.Etale) [IsReduced R] [IsNoetherianRing R] :
    IsReduced S := by
  let sf : Spec (.of S) ⟶ Spec (.of R) :=
    Spec.map (CommRingCat.ofHom f)
  haveI : AlgebraicGeometry.Etale sf :=
    AlgebraicGeometry.HasRingHomProperty.Spec_iff.mpr hf
  haveI : AlgebraicGeometry.GeometricallyReduced sf :=
    AlgebraicGeometry.etale_geometricallyReduced sf
  haveI : AlgebraicGeometry.Flat sf := inferInstance
  haveI : AlgebraicGeometry.IsReduced (Spec (.of R)) := inferInstance
  haveI : AlgebraicGeometry.IsLocallyNoetherian (Spec (.of R)) := inferInstance
  have h : AlgebraicGeometry.IsReduced (Spec (.of S)) :=
    AlgebraicGeometry.GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian sf
  exact (AlgebraicGeometry.affine_isReduced_iff (.of S)).mp h

/-- A standard-smooth algebra over a field is reduced. -/
theorem IsStandardSmooth.isReduced_of_field
    {K A : Type u} [Field K] [CommRing A]
    (f : K →+* A) (hf : f.IsStandardSmooth) : IsReduced A := by
  obtain ⟨n, g, _, hg⟩ := hf.exists_etale_mvPolynomial
  letI : IsReduced (MvPolynomial (Fin n) K) := inferInstance
  letI : IsNoetherianRing (MvPolynomial (Fin n) K) := inferInstance
  exact hg.isReduced_of_isReduced_of_isNoetherianRing g

/-- A smooth algebra over a field is reduced. -/
theorem Smooth.isReduced_of_field
    {K A : Type u} [Field K] [CommRing A]
    (f : K →+* A) (hf : f.Smooth) : IsReduced A := by
  obtain ⟨s, hs, hlocal⟩ := hf.locally_isStandardSmooth
  constructor
  intro x hx
  suffices x ∈ (⊥ : Submodule A A) by simpa using this
  apply (⊥ : Submodule A A).mem_of_span_eq_top_of_smul_pow_mem s hs x
  intro r
  letI : IsReduced (Localization.Away (r : A)) :=
    IsStandardSmooth.isReduced_of_field _ (hlocal r r.property)
  have hz : algebraMap A (Localization.Away (r : A)) x = 0 :=
    (hx.map (algebraMap A (Localization.Away (r : A)))).eq_zero
  rw [IsLocalization.map_eq_zero_iff (Submonoid.powers (r : A))] at hz
  obtain ⟨y, hyx⟩ := hz
  have hy : (y : A) ∈ Submonoid.powers (r : A) := y.property
  rw [Submonoid.mem_powers_iff] at hy
  obtain ⟨n, hn⟩ := hy
  refine ⟨n, ?_⟩
  change (r : A) ^ n * x = 0
  rw [hn]
  exact hyx

end RingHom
