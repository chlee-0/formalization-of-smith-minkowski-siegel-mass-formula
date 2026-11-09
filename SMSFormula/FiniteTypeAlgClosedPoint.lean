import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.Jacobson.Ring

/-!
# Rational points of principal opens over algebraically closed fields

This file packages the affine geometric-point consequence of the weak
Nullstellensatz needed by the Spin invariant quotient.  If `D` is a
finite-type algebra over an algebraically closed field and `x : D` is not
nilpotent, then some `K`-algebra point of `D` does not vanish on `x`.

The proof uses that `D` is Jacobson to choose a maximal ideal avoiding `x`.
Zariski's lemma makes the quotient field finite over `K`, and
`IsAlgClosed.lift` embeds that quotient field back into `K`.
-/

noncomputable section

universe u

namespace Algebra

variable {K D : Type u} [Field K] [IsAlgClosed K]
  [CommRing D] [Algebra K D] [Algebra.FiniteType K D]

/-- Every maximal ideal of an affine finite-type algebra over an
algebraically closed field is the kernel of a point valued in that field. -/
theorem exists_algHom_ker_eq (M : Ideal D) (hM : M.IsMaximal) :
    ∃ φ : D →ₐ[K] K, RingHom.ker φ.toRingHom = M := by
  letI : M.IsMaximal := hM
  letI : Field (D ⧸ M) := Ideal.Quotient.field M
  letI : Algebra.FiniteType K (D ⧸ M) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ K M)
      (Ideal.Quotient.mkₐ_surjective K M)
  letI : Module.Finite K (D ⧸ M) :=
    finite_of_finite_type_of_isJacobsonRing K (D ⧸ M)
  letI : Algebra.IsAlgebraic K (D ⧸ M) :=
    Algebra.IsAlgebraic.of_finite K (D ⧸ M)
  let ψ : D ⧸ M →ₐ[K] K := IsAlgClosed.lift
  refine ⟨ψ.comp (Ideal.Quotient.mkₐ K M), ?_⟩
  ext x
  constructor
  · intro hx
    change ψ (Ideal.Quotient.mk M x) = 0 at hx
    exact Ideal.Quotient.eq_zero_iff_mem.mp
      (ψ.injective (by simpa using hx))
  · intro hx
    change ψ (Ideal.Quotient.mk M x) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx, map_zero]

/-- A nonempty principal open in an affine finite-type algebra over an
algebraically closed field contains a point valued in that field. -/
theorem exists_algHom_apply_ne_zero_of_not_isNilpotent
    (x : D) (hx : ¬ IsNilpotent x) :
    ∃ φ : D →ₐ[K] K, φ x ≠ 0 := by
  letI : IsJacobsonRing D := isJacobsonRing_of_finiteType (A := K) (B := D)
  have hxnil : x ∉ nilradical D := by
    simpa only [mem_nilradical] using hx
  have hrad : (nilradical D).IsRadical := by
    simpa only [nilradical] using Ideal.radical_isRadical (⊥ : Ideal D)
  obtain ⟨M, ⟨_, hM⟩, hxM⟩ :=
    Ideal.eq_jacobson_iff_notMem.mp
      (IsJacobsonRing.out (R := D) inferInstance hrad) x hxnil
  letI : M.IsMaximal := hM
  letI : Field (D ⧸ M) := Ideal.Quotient.field M
  letI : Algebra.FiniteType K (D ⧸ M) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ K M)
      (Ideal.Quotient.mkₐ_surjective K M)
  letI : Module.Finite K (D ⧸ M) :=
    finite_of_finite_type_of_isJacobsonRing K (D ⧸ M)
  letI : Algebra.IsAlgebraic K (D ⧸ M) :=
    Algebra.IsAlgebraic.of_finite K (D ⧸ M)
  let ψ : D ⧸ M →ₐ[K] K := IsAlgClosed.lift
  refine ⟨ψ.comp (Ideal.Quotient.mkₐ K M), ?_⟩
  intro hzero
  change ψ (Ideal.Quotient.mk M x) = 0 at hzero
  have hquot : Ideal.Quotient.mk M x = 0 :=
    ψ.injective (by simpa using hzero)
  exact hxM (Ideal.Quotient.eq_zero_iff_mem.mp hquot)

/-- A nonnilpotent element of an affine finite-type algebra over an arbitrary
field is detected by a point valued in an algebraic closure of that field.

This is the base-field form of
`exists_algHom_apply_ne_zero_of_not_isNilpotent`: the residue field of a
maximal ideal is finite over the base field and therefore embeds into its
algebraic closure. -/
theorem exists_algHom_algebraicClosure_apply_ne_zero_of_not_isNilpotent
    {K D : Type u} [Field K] [CommRing D] [Algebra K D]
    [Algebra.FiniteType K D]
    (x : D) (hx : ¬ IsNilpotent x) :
    ∃ φ : D →ₐ[K] AlgebraicClosure K, φ x ≠ 0 := by
  letI : IsJacobsonRing D := isJacobsonRing_of_finiteType (A := K) (B := D)
  have hxnil : x ∉ nilradical D := by
    simpa only [mem_nilradical] using hx
  have hrad : (nilradical D).IsRadical := by
    simpa only [nilradical] using Ideal.radical_isRadical (⊥ : Ideal D)
  obtain ⟨M, ⟨_, hM⟩, hxM⟩ :=
    Ideal.eq_jacobson_iff_notMem.mp
      (IsJacobsonRing.out (R := D) inferInstance hrad) x hxnil
  letI : M.IsMaximal := hM
  letI : Field (D ⧸ M) := Ideal.Quotient.field M
  letI : Algebra.FiniteType K (D ⧸ M) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ K M)
      (Ideal.Quotient.mkₐ_surjective K M)
  letI : Module.Finite K (D ⧸ M) :=
    finite_of_finite_type_of_isJacobsonRing K (D ⧸ M)
  letI : Algebra.IsAlgebraic K (D ⧸ M) :=
    Algebra.IsAlgebraic.of_finite K (D ⧸ M)
  let ψ : D ⧸ M →ₐ[K] AlgebraicClosure K := IsAlgClosed.lift
  refine ⟨ψ.comp (Ideal.Quotient.mkₐ K M), ?_⟩
  intro hzero
  change ψ (Ideal.Quotient.mk M x) = 0 at hzero
  have hquot : Ideal.Quotient.mk M x = 0 :=
    ψ.injective (by simpa using hzero)
  exact hxM (Ideal.Quotient.eq_zero_iff_mem.mp hquot)

/-- An idempotent of an affine finite-type algebra is trivial if all of its
algebraic-closure-valued points have the same value.  This is a useful
algebraic replacement for reasoning directly with connected components. -/
theorem IsIdempotentElem.eq_zero_or_one_of_algebraicClosure_points_constant
    {K D : Type u} [Field K] [CommRing D] [Algebra K D]
    [Algebra.FiniteType K D]
    (e : D) (he : IsIdempotentElem e)
    (φ0 : D →ₐ[K] AlgebraicClosure K)
    (hconstant : ∀ φ : D →ₐ[K] AlgebraicClosure K, φ e = φ0 e) :
    e = 0 ∨ e = 1 := by
  obtain hzero | hone := IsIdempotentElem.iff_eq_zero_or_one.mp (he.map φ0)
  · left
    by_contra hne
    have hnonNilpotent : ¬ IsNilpotent e := by
      intro hnil
      exact hne (he.eq_zero_of_isNilpotent hnil)
    obtain ⟨φ, hφ⟩ :=
      exists_algHom_algebraicClosure_apply_ne_zero_of_not_isNilpotent
        (K := K) (D := D) e hnonNilpotent
    exact hφ (by rw [hconstant φ, hzero])
  · right
    by_contra hne
    have hne' : 1 - e ≠ 0 := by
      intro h
      apply hne
      exact (sub_eq_zero.mp h).symm
    have hnonNilpotent : ¬ IsNilpotent (1 - e) := by
      intro hnil
      exact hne' (he.one_sub.eq_zero_of_isNilpotent hnil)
    obtain ⟨φ, hφ⟩ :=
      exists_algHom_algebraicClosure_apply_ne_zero_of_not_isNilpotent
        (K := K) (D := D) (1 - e) hnonNilpotent
    apply hφ
    rw [map_sub, map_one, hconstant φ, hone, sub_self]

end Algebra
