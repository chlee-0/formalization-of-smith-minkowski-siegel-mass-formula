import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Transporting principal-localization isomorphisms by automorphisms

An intertwining square of algebra automorphisms transports bijectivity of the
principal away map of an algebra homomorphism.  Contravariantly, the principal
open pulled back by the corresponding scheme automorphism is cut out by the
image of the original principal element.
-/

noncomputable section

namespace Localization

universe u

variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B]

/-- If algebra automorphisms on the source and target intertwine an algebra
homomorphism, they transport a bijective principal away map to the principal
element transformed by the source automorphism. -/
theorem awayMap_bijective_of_intertwining_algEquiv
    (f : A →ₐ[R] B) (eA : A ≃ₐ[R] A) (eB : B ≃ₐ[R] B)
    (hcomm : eB.toAlgHom.comp f = f.comp eA.toAlgHom)
    (d : A) (hbij : Function.Bijective (awayMap f.toRingHom d)) :
    Function.Bijective (awayMap f.toRingHom (eA d)) := by
  constructor
  · have hinj := hbij.1
    rw [awayMap_injective_iff] at hinj ⊢
    intro a ha
    have hpre : f (eA.symm a) = 0 := by
      apply eB.injective
      have h := DFunLike.congr_fun hcomm (eA.symm a)
      change eB (f (eA.symm a)) = f (eA (eA.symm a)) at h
      calc
        eB (f (eA.symm a)) = f a := by simpa using h
        _ = 0 := ha
        _ = eB 0 := (map_zero eB).symm
    obtain ⟨n, hn⟩ := hinj (eA.symm a) hpre
    refine ⟨n, ?_⟩
    have := congrArg eA hn
    simpa using this
  · have hsurj := hbij.2
    rw [awayMap_surjective_iff] at hsurj ⊢
    intro b
    obtain ⟨a, m, ham⟩ := hsurj (eB.symm b)
    refine ⟨eA a, m, ?_⟩
    have h := congrArg eB ham
    have ha := DFunLike.congr_fun hcomm a
    have hd := DFunLike.congr_fun hcomm d
    change eB (f a) = f (eA a) at ha
    change eB (f d) = f (eA d) at hd
    change eB (f a) = eB (f d ^ m * eB.symm b) at h
    rw [map_mul, map_pow, ha, hd, eB.apply_symm_apply] at h
    simpa using h

/-- The inverse automorphisms also intertwine the algebra homomorphism.  Thus
the image (rather than the inverse image) of the geometric principal open is
cut out by the inverse-transformed coordinate and again has a bijective away
map. -/
theorem awayMap_bijective_of_intertwining_algEquiv_symm
    (f : A →ₐ[R] B) (eA : A ≃ₐ[R] A) (eB : B ≃ₐ[R] B)
    (hcomm : eB.toAlgHom.comp f = f.comp eA.toAlgHom)
    (d : A) (hbij : Function.Bijective (awayMap f.toRingHom d)) :
    Function.Bijective (awayMap f.toRingHom (eA.symm d)) := by
  apply awayMap_bijective_of_intertwining_algEquiv
    f eA.symm eB.symm
  · apply AlgHom.ext
    intro a
    have h := DFunLike.congr_fun hcomm (eA.symm a)
    change eB (f (eA.symm a)) = f (eA (eA.symm a)) at h
    apply eB.injective
    change eB (eB.symm (f a)) = eB (f (eA.symm a))
    rw [eB.apply_symm_apply]
    simpa using h.symm
  · exact hbij

end Localization
