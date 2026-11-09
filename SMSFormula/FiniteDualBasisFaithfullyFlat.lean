import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Finiteness.Projective
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.RingHom.FaithfullyFlat
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Faithful flatness from a finite dual basis

This file isolates the elementary algebra at the end of the rank-two
Hopf-torsor argument. A finite dual basis makes a module finite projective.
For an algebra with injective structure map, integrality then supplies
surjectivity on prime spectra, hence faithful flatness.

The final theorem specializes the criterion to the standard involution
calculation. Its trace-lifting hypothesis is precisely the effective-quotient
or coinvariant input that is not implied by a canonical torsor map alone.
-/

noncomputable section

namespace Module

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- A finite dual basis makes the module finitely generated. -/
theorem finite_of_finite_dual_basis {ι : Type*} [Fintype ι]
    (x : ι → M) (φ : ι → M →ₗ[R] R)
    (h : ∀ m, ∑ i, (φ i m) • x i = m) : Module.Finite R M := by
  let s : (ι → R) →ₗ[R] M := (Pi.basisFun R ι).constr R x
  apply Module.Finite.of_surjective s
  intro m
  refine ⟨fun i => φ i m, ?_⟩
  simpa [s] using h m

/-- The dual-basis criterion for projectivity, with a finite indexing type. -/
theorem projective_of_finite_dual_basis {ι : Type*} [Fintype ι]
    (x : ι → M) (φ : ι → M →ₗ[R] R)
    (h : ∀ m, ∑ i, (φ i m) • x i = m) : Module.Projective R M := by
  let s : (ι → R) →ₗ[R] M := (Pi.basisFun R ι).constr R x
  let t : M →ₗ[R] (ι → R) := LinearMap.pi φ
  apply Module.Projective.of_split t s
  ext m
  simpa [s, t] using h m

end Module

namespace RingHom

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]

/-- An algebra with an injective structure map and a finite dual basis is
faithfully flat. -/
theorem faithfullyFlat_of_finite_dual_basis {ι : Type*} [Fintype ι]
    (x : ι → B) (φ : ι → B →ₗ[A] A)
    (h : ∀ b, ∑ i, (φ i b) • x i = b)
    (hinj : Function.Injective (algebraMap A B)) :
    (algebraMap A B).FaithfullyFlat := by
  letI : Module.Finite A B := Module.finite_of_finite_dual_basis x φ h
  letI : Module.Projective A B := Module.projective_of_finite_dual_basis x φ h
  letI : Module.Flat A B := inferInstance
  rw [RingHom.faithfullyFlat_algebraMap_iff]
  exact Module.FaithfullyFlat.of_comap_surjective
    ((RingHom.Finite.to_isIntegral
      (RingHom.finite_algebraMap.mpr inferInstance)).comap_surjective hinj)

/-- The elementary rank-two torsor calculation. If an involution has a trace
landing in the base algebra and a finite tensor witness satisfying the two
canonical-map equations, then the extension is faithfully flat. -/
theorem faithfullyFlat_of_involution_torsor_witness
    (σ : B ≃ₐ[A] B) (tr : B →ₗ[A] A)
    (htr : ∀ b, algebraMap A B (tr b) = b + σ b)
    {ι : Type*} [Fintype ι] (x y : ι → B)
    (hone : ∑ i, x i * y i = 1)
    (hzero : ∑ i, x i * σ (y i) = 0)
    (hinj : Function.Injective (algebraMap A B)) :
    (algebraMap A B).FaithfullyFlat := by
  let φ : ι → B →ₗ[A] A := fun i => tr.comp (LinearMap.mulLeft A (y i))
  apply faithfullyFlat_of_finite_dual_basis x φ
  · intro b
    simp_rw [φ, LinearMap.comp_apply, LinearMap.mulLeft_apply,
      Algebra.smul_def, htr, map_mul]
    calc
      ∑ i, (y i * b + σ (y i) * σ b) * x i =
          ∑ i, (x i * y i * b + x i * σ (y i) * σ b) := by
            apply Finset.sum_congr rfl
            intro i _
            ring
      _ = (∑ i, x i * y i) * b + (∑ i, x i * σ (y i)) * σ b := by
        rw [Finset.sum_add_distrib, Finset.sum_mul, Finset.sum_mul]
      _ = b := by rw [hone, hzero]; simp
  · exact hinj

end RingHom
