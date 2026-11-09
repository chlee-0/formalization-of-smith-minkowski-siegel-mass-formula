import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Nilpotent.Lemmas

/-!
# Scalar extension of a principal-localization isomorphism

This file records the algebraic base-change precursor used by the rational
Spin invariant quotient.  An algebra equivalence remains an equivalence after
tensoring its right factor.  Consequently, a principal-localization
isomorphism remains an isomorphism after arbitrary scalar extension.

For a faithfully flat scalar extension, a principal element avoiding a prime
remains nonnilpotent after tensoring.  Equivalently, some prime of the
base-changed algebra avoids it.  This is the algebraic nonemptiness statement
needed before any geometric translation argument.
-/

noncomputable section

open TensorProduct

universe u

namespace Algebra.TensorProduct

variable {R K A B : Type u} [CommSemiring R] [CommSemiring K]
  [Algebra R K] [CommSemiring A] [Algebra R A]
  [CommSemiring B] [Algebra R B]

/-- Scalar extension of an algebra equivalence in the right tensor factor. -/
noncomputable def mapRightAlgEquiv (e : A ≃ₐ[R] B) :
    K ⊗[R] A ≃ₐ[K] K ⊗[R] B :=
  AlgEquiv.ofAlgHom
    (Algebra.TensorProduct.map (AlgHom.id K K) e.toAlgHom)
    (Algebra.TensorProduct.map (AlgHom.id K K) e.symm.toAlgHom)
    (by
      ext k
      simp)
    (by
      ext k
      simp)

@[simp]
theorem mapRightAlgEquiv_apply_tmul (e : A ≃ₐ[R] B) (k : K) (a : A) :
    mapRightAlgEquiv (K := K) e (k ⊗ₜ[R] a) = k ⊗ₜ[R] e a := by
  simp [mapRightAlgEquiv]

end Algebra.TensorProduct

namespace Localization

variable {R K A B : Type u} [CommSemiring R] [CommSemiring K]
  [Algebra R K] [CommSemiring A] [Algebra R A]
  [CommSemiring B] [Algebra R B]

/-- A principal-localization isomorphism remains an isomorphism after scalar
extension. -/
noncomputable def awayMapScalarExtensionAlgEquiv (f : A →ₐ[R] B) (d : A)
    (h : Function.Bijective (Localization.awayMap f.toRingHom d)) :
    K ⊗[R] Localization.Away d ≃ₐ[K]
      K ⊗[R] Localization.Away (f d) :=
  Algebra.TensorProduct.mapRightAlgEquiv (K := K)
    (AlgEquiv.ofBijective (Localization.awayMapₐ f d) h)

@[simp]
theorem awayMapScalarExtensionAlgEquiv_apply_tmul (f : A →ₐ[R] B) (d : A)
    (h : Function.Bijective (Localization.awayMap f.toRingHom d))
    (k : K) (x : Localization.Away d) :
    awayMapScalarExtensionAlgEquiv (K := K) f d h (k ⊗ₜ[R] x) =
      k ⊗ₜ[R] Localization.awayMapₐ f d x := by
  simp [awayMapScalarExtensionAlgEquiv]

end Localization

namespace Algebra.TensorProduct

variable {R K A : Type u} [CommRing R] [CommRing K] [Algebra R K]
  [Module.FaithfullyFlat R K] [CommRing A] [Algebra R A]

/-- A scalar extended element remains nonnilpotent when the original element
avoids a prime. -/
theorem includeRight_not_isNilpotent_of_not_mem
    (p : Ideal A) [p.IsPrime] (d : A) (hd : d ∉ p) :
    ¬ IsNilpotent (Algebra.TensorProduct.includeRight d : K ⊗[R] A) := by
  intro hnil
  obtain ⟨n, hn⟩ := hnil
  have hinj : Function.Injective (TensorProduct.mk R K A 1) :=
    Module.FaithfullyFlat.tensorProduct_mk_injective A
  have hpow : d ^ n = 0 := hinj <| by
    rw [TensorProduct.mk_apply, TensorProduct.mk_apply]
    rw [← Algebra.TensorProduct.includeRight_apply, map_pow, hn]
    simp
  exact hd (Ideal.IsPrime.mem_of_pow_mem (I := p)
    (show p.IsPrime from inferInstance) n (by simp [hpow]))

/-- A principal element which avoids a prime before faithfully flat scalar
extension is avoided by some prime afterward. -/
theorem exists_prime_not_mem_includeRight
    (p : Ideal A) [p.IsPrime] (d : A) (hd : d ∉ p) :
    ∃ q : Ideal (K ⊗[R] A), q.IsPrime ∧
      Algebra.TensorProduct.includeRight d ∉ q := by
  have hnil := includeRight_not_isNilpotent_of_not_mem
    (R := R) (K := K) p d hd
  by_contra h
  push_neg at h
  exact hnil (nilpotent_iff_mem_prime.mpr h)

end Algebra.TensorProduct
