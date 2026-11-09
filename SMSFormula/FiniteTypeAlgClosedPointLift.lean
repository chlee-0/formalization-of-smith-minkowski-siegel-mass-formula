import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.Finiteness.Quotient
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Lifting algebraically closed points through a finite-type spectrum cover

If `A -> B` is finite type and surjective on prime spectra, then every
algebraically closed point of `A` whose kernel is maximal lifts to `B`.
This is the affine geometric-point consequence of Zariski's lemma used by
the Spin invariant quotient.
-/

noncomputable section

open TensorProduct

universe u

namespace Algebra

variable {R : Type u} [Field R]

/-- The kernel of a point into an integral field extension is maximal. -/
theorem AlgHom.ker_isMaximal_of_isIntegral
    {A K : Type u} [CommRing A] [Field K]
    [Algebra R A] [Algebra R K] [Algebra.IsIntegral R K]
    (φ : A →ₐ[R] K) : (RingHom.ker φ.toRingHom).IsMaximal := by
  letI : Algebra A K := φ.toRingHom.toAlgebra
  letI : IsScalarTower R A K := IsScalarTower.of_algebraMap_eq' (by
    ext r
    exact (φ.commutes r).symm)
  haveI : Algebra.IsIntegral A K := Algebra.IsIntegral.tower_top R
  change ((⊥ : Ideal K).comap φ.toRingHom).IsMaximal
  exact Ideal.isMaximal_comap_of_isIntegral_of_isMaximal
    (R := A) (S := K) (⊥ : Ideal K)

variable {A B K : Type u} [CommRing A] [CommRing B] [Field K] [IsAlgClosed K]
  [Algebra A B] [Algebra.FiniteType A B]

/-- A point with maximal kernel lifts through a finite-type algebra map that
is surjective on prime spectra. -/
theorem exists_ringHom_comp_algebraMap_eq_of_comap_surjective
    (hspec : Function.Surjective
      (PrimeSpectrum.comap (algebraMap A B)))
    (φ : A →+* K) (hφ : (RingHom.ker φ).IsMaximal) :
    ∃ ψ : B →+* K, ψ.comp (algebraMap A B) = φ := by
  let p : PrimeSpectrum A := ⟨RingHom.ker φ, hφ.isPrime⟩
  obtain ⟨q, hq⟩ := hspec p
  obtain ⟨M, hM, hqM⟩ := Ideal.exists_le_maximal q.asIdeal q.isPrime.ne_top
  have hunder : M.under A = RingHom.ker φ := by
    symm
    apply hφ.eq_of_le
    · exact Ideal.comap_ne_top (algebraMap A B) hM.ne_top
    · intro a ha
      have ha' : algebraMap A B a ∈ q.asIdeal := by
        change a ∈ (PrimeSpectrum.comap (algebraMap A B) q).asIdeal
        simpa only [hq]
      exact hqM ha'
  letI : M.IsMaximal := hM
  letI : (M.under A).IsMaximal := hunder ▸ hφ
  let L := A ⧸ M.under A
  let E := B ⧸ M
  letI : Field L := Ideal.Quotient.field (M.under A)
  letI : Field E := Ideal.Quotient.field M
  let φL : L →+* K := Ideal.Quotient.lift (M.under A) φ (by
    intro a ha
    rw [hunder] at ha
    exact ha)
  letI : Algebra L K := φL.toAlgebra
  letI : Algebra.FiniteType L E := inferInstance
  letI : Module.Finite L E := finite_of_finite_type_of_isJacobsonRing L E
  letI : Algebra.IsAlgebraic L E := Algebra.IsAlgebraic.of_finite L E
  let ψE : E →ₐ[L] K := IsAlgClosed.lift
  let ψ : B →+* K := ψE.toRingHom.comp (Ideal.Quotient.mk M)
  refine ⟨ψ, ?_⟩
  apply RingHom.ext
  intro a
  change ψE (Ideal.Quotient.mk M (algebraMap A B a)) = φ a
  change ψE (algebraMap L E (Ideal.Quotient.mk (M.under A) a)) = φ a
  rw [ψE.commutes]
  rfl

variable {R : Type u} [CommRing R]
  [Algebra R A] [Algebra R B] [Algebra R K] [IsScalarTower R A B]

/-- Algebra-homomorphism form of
`exists_ringHom_comp_algebraMap_eq_of_comap_surjective`. -/
theorem exists_algHom_comp_eq_of_comap_surjective
    (hspec : Function.Surjective
      (PrimeSpectrum.comap (algebraMap A B)))
    (φ : A →ₐ[R] K) (hφ : (RingHom.ker φ.toRingHom).IsMaximal) :
    ∃ ψ : B →ₐ[R] K, ψ.comp (IsScalarTower.toAlgHom R A B) = φ := by
  obtain ⟨ψ₀, hψ₀⟩ :=
    exists_ringHom_comp_algebraMap_eq_of_comap_surjective hspec φ.toRingHom hφ
  let ψ : B →ₐ[R] K :=
    { toRingHom := ψ₀
      commutes' := fun r => by
        have h := DFunLike.congr_fun hψ₀ (algebraMap R A r)
        calc
          ψ₀ (algebraMap R B r) =
              ψ₀ (algebraMap A B (algebraMap R A r)) := by
                exact congrArg ψ₀ (IsScalarTower.algebraMap_apply R A B r)
          _ = φ (algebraMap R A r) := h
          _ = algebraMap R K r := φ.commutes r }
  refine ⟨ψ, ?_⟩
  apply AlgHom.ext
  intro a
  exact DFunLike.congr_fun hψ₀ a

namespace TensorProduct

variable {R D K : Type u} [CommRing R] [CommRing D] [CommRing K]
  [Algebra R D] [Algebra R K]

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- Extend an `R`-algebra point to the corresponding point of the right
scalar extension. -/
noncomputable def rightTensorPoint (φ : D →ₐ[R] K) :
    D ⊗[R] K →ₐ[K] K := by
  let t : D ⊗[R] K →ₐ[R] K := Algebra.TensorProduct.lift
    φ (AlgHom.id R K) (fun _ _ => Commute.all _ _)
  exact
    { toRingHom := t.toRingHom
      commutes' := by
        intro k
        change t (Algebra.TensorProduct.includeRight k) = k
        simp [t] }

@[simp]
theorem rightTensorPoint_tmul (φ : D →ₐ[R] K) (d : D) (k : K) :
    rightTensorPoint φ (d ⊗ₜ[R] k) = φ d * k := by
  simp [rightTensorPoint]

@[simp]
theorem rightTensorPoint_comp_includeLeft (φ : D →ₐ[R] K) :
    ((rightTensorPoint φ).restrictScalars R).comp
        (Algebra.TensorProduct.includeLeft : D →ₐ[R] D ⊗[R] K) = φ := by
  apply AlgHom.ext
  intro d
  simp [Algebra.TensorProduct.includeLeft_apply]

/-- A point of the right scalar extension is reconstructed from its
restriction to the original algebra. -/
theorem rightTensorPoint_restrict_eq_self (φ : D ⊗[R] K →ₐ[K] K) :
    rightTensorPoint
        ((φ.restrictScalars R).comp
          (Algebra.TensorProduct.includeLeft : D →ₐ[R] D ⊗[R] K)) = φ := by
  apply AlgHom.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul d k =>
      rw [rightTensorPoint_tmul]
      change φ (d ⊗ₜ[R] (1 : K)) * k = φ (d ⊗ₜ[R] k)
      have hk : φ (algebraMap K (D ⊗[R] K) k) = k := φ.commutes k
      have ht :
          (d ⊗ₜ[R] (1 : K)) * algebraMap K (D ⊗[R] K) k = d ⊗ₜ[R] k := by
        rw [Algebra.TensorProduct.algebraMap_eq_includeRight]
        simp
      calc
        φ (d ⊗ₜ[R] (1 : K)) * k =
            φ (d ⊗ₜ[R] (1 : K)) * φ (algebraMap K (D ⊗[R] K) k) :=
          congrArg (fun z => φ (d ⊗ₜ[R] (1 : K)) * z) hk.symm
        _ = φ ((d ⊗ₜ[R] (1 : K)) * algebraMap K (D ⊗[R] K) k) :=
          (map_mul φ _ _).symm
        _ = φ (d ⊗ₜ[R] k) := congrArg φ ht

end TensorProduct

end Algebra
