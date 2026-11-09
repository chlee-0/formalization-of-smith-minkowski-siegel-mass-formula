import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.Topology.Instances.Matrix
import Mathlib.Tactic
import SMSFormula.StandardAxiomsGuard

/-!
# Compact extraction of a p-adic Gram isometry

Independent of the binary Gauss and odd diagonalization modules. Approximate
inverses are kept as a second compact coordinate, so neither continuity
of matrix inversion nor compatible choices at successive levels are needed.
-/

noncomputable section
namespace UnimodularPadicLift

abbrev Mat (p n : ℕ) [Fact p.Prime] := Matrix (Fin n) (Fin n) ℤ_[p]

variable {p n : ℕ} [Fact p.Prime]

instance matrixCompactSpace : CompactSpace (Mat p n) :=
  inferInstanceAs (CompactSpace (Fin n → Fin n → ℤ_[p]))

/-- Entrywise divisibility, not a determinant condition. -/
def PowDiv (k : ℕ) (A : Mat p n) : Prop :=
  ∀ i j, (p : ℤ_[p]) ^ k ∣ A i j

lemma powDiv_mono {k l : ℕ} (hkl : k ≤ l) {A : Mat p n}
    (hA : PowDiv l A) : PowDiv k A := by
  intro i j
  exact dvd_trans (pow_dvd_pow (p : ℤ_[p]) hkl) (hA i j)

lemma isClosed_powDiv_scalar (k : ℕ) :
    IsClosed {x : ℤ_[p] | (p : ℤ_[p]) ^ k ∣ x} := by
  have hset : {x : ℤ_[p] | (p : ℤ_[p]) ^ k ∣ x} =
      Set.range (fun a : ℤ_[p] => (p : ℤ_[p]) ^ k * a) := by
    ext x
    constructor
    · rintro ⟨a, ha⟩
      exact ⟨a, ha.symm⟩
    · rintro ⟨a, ha⟩
      exact ⟨a, ha.symm⟩
  rw [hset]
  exact (isCompact_range (continuous_const.mul continuous_id)).isClosed

lemma isClosed_powDiv_preimage {X : Type*} [TopologicalSpace X]
    (k : ℕ) (f : X → Mat p n) (hf : Continuous f) :
    IsClosed {x | PowDiv k (f x)} := by
  have hset : {x | PowDiv k (f x)} =
      ⋂ i : Fin n, ⋂ j : Fin n, {x | (p : ℤ_[p]) ^ k ∣ f x i j} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_iInter, PowDiv]
  rw [hset]
  exact isClosed_iInter fun i => isClosed_iInter fun j =>
    (isClosed_powDiv_scalar k).preimage (hf.matrix_elem i j)

lemma eq_zero_of_forall_pow_dvd (x : ℤ_[p])
    (hx : ∀ k : ℕ, (p : ℤ_[p]) ^ k ∣ x) : x = 0 := by
  apply eq_of_forall_dist_le
  intro ε hε
  obtain ⟨k, hk⟩ := PadicInt.exists_pow_neg_lt p hε
  have hnorm : ‖x‖ ≤ (p : ℝ) ^ (-(k : ℤ)) :=
    (x.norm_le_pow_iff_mem_span_pow k).mpr
      (Ideal.mem_span_singleton.mpr (hx k))
  simpa only [dist_eq_norm, sub_zero] using hnorm.trans hk.le

lemma matrix_eq_zero_of_forall_powDiv (A : Mat p n)
    (hA : ∀ k : ℕ, PowDiv k A) : A = 0 := by
  ext i j
  exact eq_zero_of_forall_pow_dvd (A i j) (fun k => hA k i j)

/-- Nested closed constraints in a compact space. Only finite solvability is
used; there is no chosen coherent tower hidden in the input. -/
lemma exists_mem_all_of_antitone_closed
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (S : ℕ → Set X) (hclosed : ∀ k, IsClosed (S k))
    (hanti : Antitone S) (hne : ∀ k, (S k).Nonempty) :
    ∃ x, ∀ k, x ∈ S k := by
  have hi : (⋂ k, S k).Nonempty := CompactSpace.iInter_nonempty hclosed (by
    intro t
    obtain ⟨x, hx⟩ := hne (t.sup id)
    refine ⟨x, ?_⟩
    simp only [Set.mem_iInter]
    intro k hk
    exact hanti (Finset.le_sup (f := id) hk) hx)
  obtain ⟨x, hx⟩ := hi
  exact ⟨x, fun k => Set.mem_iInter.mp hx k⟩

/-- Closed side constraints may retain a prescribed residue of the change
matrix and/or its inverse. Approximate matrices at different k need not agree. -/
theorem exists_gram_isometry_of_all_precisions
    (G H : Mat p n) (K : Set (Mat p n × Mat p n)) (hK : IsClosed K)
    (happrox : ∀ k : ℕ, ∃ U V : Mat p n,
      (U, V) ∈ K ∧ PowDiv k (U.transpose * G * U - H) ∧
        PowDiv k (U * V - 1) ∧ PowDiv k (V * U - 1)) :
    ∃ U V : Mat p n, (U, V) ∈ K ∧
      U.transpose * G * U = H ∧ U * V = 1 ∧ V * U = 1 := by
  let S : ℕ → Set (Mat p n × Mat p n) := fun k =>
    {z | z ∈ K ∧ PowDiv k (z.1.transpose * G * z.1 - H) ∧
      PowDiv k (z.1 * z.2 - 1) ∧ PowDiv k (z.2 * z.1 - 1)}
  have hc : ∀ k, IsClosed (S k) := by
    intro k
    exact hK.inter ((isClosed_powDiv_preimage k
      (fun z : Mat p n × Mat p n => z.1.transpose * G * z.1 - H)
      (by fun_prop)).inter
      ((isClosed_powDiv_preimage k
        (fun z : Mat p n × Mat p n => z.1 * z.2 - 1) (by fun_prop)).inter
        (isClosed_powDiv_preimage k
          (fun z : Mat p n × Mat p n => z.2 * z.1 - 1) (by fun_prop))))
  have ha : Antitone S := by
    intro k l hkl z hz
    exact ⟨hz.1, powDiv_mono hkl hz.2.1,
      powDiv_mono hkl hz.2.2.1, powDiv_mono hkl hz.2.2.2⟩
  have hn : ∀ k, (S k).Nonempty := by
    intro k
    obtain ⟨U, V, hUV⟩ := happrox k
    exact ⟨(U, V), hUV⟩
  obtain ⟨z, hz⟩ := exists_mem_all_of_antitone_closed S hc ha hn
  refine ⟨z.1, z.2, (hz 0).1, ?_, ?_, ?_⟩
  · exact sub_eq_zero.mp (matrix_eq_zero_of_forall_powDiv _
      (fun k => (hz k).2.1))
  · exact sub_eq_zero.mp (matrix_eq_zero_of_forall_powDiv _
      (fun k => (hz k).2.2.1))
  · exact sub_eq_zero.mp (matrix_eq_zero_of_forall_powDiv _
      (fun k => (hz k).2.2.2))

/-- The unconstrained statement returns an actual unit, not just a nonsingular
rational matrix or equality of finite counts. -/
theorem exists_unit_gram_isometry_of_all_precisions
    (G H : Mat p n)
    (happrox : ∀ k : ℕ, ∃ U V : Mat p n,
      PowDiv k (U.transpose * G * U - H) ∧
        PowDiv k (U * V - 1) ∧ PowDiv k (V * U - 1)) :
    ∃ U : Mat p n, IsUnit U ∧ U.transpose * G * U = H := by
  obtain ⟨U, V, _, hgram, huv, hvu⟩ :=
    exists_gram_isometry_of_all_precisions G H Set.univ isClosed_univ (by
      intro k
      obtain ⟨U, V, h⟩ := happrox k
      exact ⟨U, V, Set.mem_univ _, h⟩)
  let u : (Mat p n)ˣ := ⟨U, V, huv, hvu⟩
  exact ⟨U, u.isUnit, hgram⟩

/-- Entrywise residue retention is a closed side condition. At p=2 the
lifting construction retains exponent r=2, not necessarily r=3. -/
def residueConstraint (r : ℕ) (U₀ V₀ : Mat p n) : Set (Mat p n × Mat p n) :=
  {z | PowDiv r (z.1 - U₀) ∧ PowDiv r (z.2 - V₀)}

lemma isClosed_residueConstraint (r : ℕ) (U₀ V₀ : Mat p n) :
    IsClosed (residueConstraint r U₀ V₀) :=
  (isClosed_powDiv_preimage r
    (fun z : Mat p n × Mat p n => z.1 - U₀) (by fun_prop)).inter
  (isClosed_powDiv_preimage r
    (fun z : Mat p n × Mat p n => z.2 - V₀) (by fun_prop))

#assert_standard_axioms exists_mem_all_of_antitone_closed
#assert_standard_axioms exists_gram_isometry_of_all_precisions
#assert_standard_axioms exists_unit_gram_isometry_of_all_precisions
#assert_standard_axioms isClosed_residueConstraint

end UnimodularPadicLift
