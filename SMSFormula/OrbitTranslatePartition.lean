import Mathlib

/-! Partition of an orbit into translates of a normal subgroup orbit. For a group
`Γ` acting on `X`, a normal subgroup `N` and a point `x₀`, put
`L = N ⊔ Stab(x₀)`. The orbit `Γ · x₀` is the disjoint union, over `Γ ⧸ L`, of
the translates `q.out · (N · x₀)`. Consequently every measure giving each
translate the same mass `c` gives the orbit mass `[Γ : L] · c`. This is the
chart-free counting input for reading `[K : K'(K ∩ H)] · vol(K' · x_old)` as an
orbit mass. No representative beyond `Quotient.out` (used only to index the
pieces; the pieces themselves do not depend on it) is used in the statements. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace MulAction

variable {Γ X : Type*} [Group Γ] [MulAction Γ X] (N : Subgroup Γ) [hN : N.Normal] (x₀ : X)

/-- The translate of the `N`-orbit of `x₀` indexed by a coset of `N ⊔ Stab(x₀)`. -/
def normalOrbitTranslate (q : Γ ⧸ (N ⊔ stabilizer Γ x₀)) : Set X :=
  (fun g : Γ ↦ (q.out * g) • x₀) '' (N : Set Γ)

/-- Each piece is the translate by its coset representative of the `N`-orbit. -/
theorem normalOrbitTranslate_eq_image (q : Γ ⧸ (N ⊔ stabilizer Γ x₀)) :
    normalOrbitTranslate N x₀ q =
      (fun y : X ↦ q.out • y) '' ((fun g : Γ ↦ g • x₀) '' (N : Set Γ)) := by
  rw [normalOrbitTranslate, Set.image_image]
  simp only [mul_smul]

/-- Two group elements move `N`-orbit points of `x₀` to a common point exactly when
they lie in the same coset of `N ⊔ Stab(x₀)`. -/
theorem mem_sup_stabilizer_of_smul_eq {a a' g g' : Γ} (hg : g ∈ N) (hg' : g' ∈ N)
    (h : (a * g) • x₀ = (a' * g') • x₀) : a⁻¹ * a' ∈ N ⊔ stabilizer Γ x₀ := by
  have hs : g⁻¹ * (a⁻¹ * a') * g' ∈ stabilizer Γ x₀ := by
    have hre : g⁻¹ * (a⁻¹ * a') * g' = (g⁻¹ * a⁻¹) * (a' * g') := by group
    rw [mem_stabilizer_iff, hre, mul_smul, ← h, ← mul_smul,
      show (g⁻¹ * a⁻¹) * (a * g) = 1 by group, one_smul]
  set s := g⁻¹ * (a⁻¹ * a') * g' with hsdef
  have hdec : a⁻¹ * a' = (g * (s * g'⁻¹ * s⁻¹)) * s := by
    rw [hsdef]; group
  rw [hdec]
  exact Subgroup.mul_mem_sup (N.mul_mem hg (hN.conj_mem _ (N.inv_mem hg') s)) hs

/-- Distinct cosets give disjoint translates. -/
theorem pairwise_disjoint_normalOrbitTranslate :
    Pairwise (Function.onFun Disjoint (normalOrbitTranslate N x₀)) := by
  intro q q' hne
  rw [Function.onFun, Set.disjoint_left]
  rintro _ ⟨g, hg, rfl⟩ ⟨g', hg', hgg'⟩
  apply hne
  have hmem := mem_sup_stabilizer_of_smul_eq N x₀ hg' hg hgg'
  rw [← QuotientGroup.out_eq' q, ← QuotientGroup.out_eq' q']
  exact ((QuotientGroup.eq).mpr hmem).symm

/-- The translates cover the orbit of `x₀`. -/
theorem iUnion_normalOrbitTranslate :
    (⋃ q, normalOrbitTranslate N x₀ q) = range (fun γ : Γ ↦ γ • x₀) := by
  ext y
  simp only [mem_iUnion, mem_range]
  constructor
  · rintro ⟨q, g, hg, rfl⟩
    exact ⟨q.out * g, rfl⟩
  · rintro ⟨γ, rfl⟩
    refine ⟨(QuotientGroup.mk γ : Γ ⧸ (N ⊔ stabilizer Γ x₀)), ?_⟩
    have hmem : (QuotientGroup.mk γ : Γ ⧸ (N ⊔ stabilizer Γ x₀)).out⁻¹ * γ ∈
        N ⊔ stabilizer Γ x₀ :=
      (QuotientGroup.eq).mp (QuotientGroup.out_eq' _)
    obtain ⟨g, hg, s, hs, hgs⟩ := Subgroup.mem_sup_of_normal_left.mp hmem
    refine ⟨g, hg, ?_⟩
    change ((QuotientGroup.mk γ : Γ ⧸ (N ⊔ stabilizer Γ x₀)).out * g) • x₀ = γ • x₀
    have hγ : γ = (QuotientGroup.mk γ : Γ ⧸ (N ⊔ stabilizer Γ x₀)).out * g * s := by
      rw [mul_assoc, hgs, mul_inv_cancel_left]
    conv_rhs => rw [hγ, mul_smul, (mem_stabilizer_iff).mp hs]

/-- Orbit counting: if every translate has measure `c`, the orbit has measure
`[Γ : N ⊔ Stab(x₀)] · c`. -/
theorem measure_orbit_eq_index_mul [MeasurableSpace X] (μ : Measure X)
    [Finite (Γ ⧸ (N ⊔ stabilizer Γ x₀))]
    (hmeas : ∀ q, MeasurableSet (normalOrbitTranslate N x₀ q)) {c : ℝ≥0∞}
    (hc : ∀ q, μ (normalOrbitTranslate N x₀ q) = c) :
    μ (range (fun γ : Γ ↦ γ • x₀)) = ((N ⊔ stabilizer Γ x₀).index : ℝ≥0∞) * c := by
  classical
  letI := Fintype.ofFinite (Γ ⧸ (N ⊔ stabilizer Γ x₀))
  rw [← iUnion_normalOrbitTranslate N x₀,
    measure_iUnion (pairwise_disjoint_normalOrbitTranslate N x₀) hmeas, tsum_fintype]
  simp only [hc, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [Subgroup.index, Nat.card_eq_fintype_card]

end MulAction
