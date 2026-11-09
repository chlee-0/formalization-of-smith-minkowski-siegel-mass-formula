import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Analysis.Normed.Group.Basic

/-!
# Contraction inversion on a closed additive-subgroup coset

Let `L` be a closed additive subgroup of a complete normed additive
commutative group and let `N` be a map fixing a coset center `x`.  Suppose that
on the coset `x + L`, the difference

`N y - N z - (y - z)`

both belongs to `L` and has norm bounded by a strict contraction coefficient
times `‖y - z‖`.  For a prescribed target `w` in the coset, the correction map

`y ↦ y + w - N y`

is then a contracting self-map of the coset.  Banach's fixed-point theorem
gives a preimage of `w`; the same norm estimate gives injectivity.  Thus `N`
maps the coset bijectively onto itself.

This module is generic and contains no p-adic chart, Haar measure, or
change-of-variables statement.
-/

noncomputable section

open scoped NNReal Topology

namespace AddSubgroup

variable {E : Type*} [NormedAddCommGroup E]

/-- The additive coset of `L` centered at `x`, written as a centered
difference condition. -/
def translatedCoset (L : AddSubgroup E) (x : E) : Set E :=
  {y | y - x ∈ L}

@[simp]
theorem mem_translatedCoset_iff
    (L : AddSubgroup E) (x y : E) :
    y ∈ L.translatedCoset x ↔ y - x ∈ L :=
  Iff.rfl

@[simp]
theorem center_mem_translatedCoset
    (L : AddSubgroup E) (x : E) :
    x ∈ L.translatedCoset x := by
  simp [translatedCoset]

/-- A translate of a closed additive subgroup is closed. -/
theorem isClosed_translatedCoset
    [IsTopologicalAddGroup E]
    (L : AddSubgroup E) (x : E)
    (hL : IsClosed (L : Set E)) :
    IsClosed (L.translatedCoset x) := by
  have heq :
      L.translatedCoset x =
        (Homeomorph.addLeft (-x)) ⁻¹' (L : Set E) := by
    ext y
    change (y - x ∈ L) ↔ (-x + y ∈ L)
    rw [sub_eq_add_neg, add_comm]
  rw [heq]
  exact hL.preimage (Homeomorph.addLeft (-x)).continuous

/-- The correction map whose fixed points are preimages of `w` under `N`. -/
def cosetCorrection (N : E → E) (w y : E) : E :=
  y + w - N y

/-- The congruence error condition makes the correction map preserve the
closed coset. -/
theorem mapsTo_cosetCorrection
    (L : AddSubgroup E) (x : E)
    (N : E → E) (hNx : N x = x)
    (hcongr :
      ∀ y ∈ L.translatedCoset x,
        ∀ z ∈ L.translatedCoset x,
          N y - N z - (y - z) ∈ L)
    {w : E} (hw : w ∈ L.translatedCoset x) :
    Set.MapsTo (cosetCorrection N w)
      (L.translatedCoset x) (L.translatedCoset x) := by
  intro y hy
  rw [mem_translatedCoset_iff]
  rw [mem_translatedCoset_iff] at hw
  have herr :=
    hcongr y hy x (center_mem_translatedCoset L x)
  have heq :
      cosetCorrection N w y - x =
        (w - x) - (N y - N x - (y - x)) := by
    rw [hNx]
    dsimp [cosetCorrection]
    abel
  rw [heq]
  exact L.sub_mem hw herr

/-- The norm remainder condition makes the correction map a contraction on
the coset subtype. -/
theorem contractingWith_cosetCorrection
    (L : AddSubgroup E) (x : E)
    (N : E → E) (hNx : N x = x)
    {q : ℝ≥0} (hq : q < 1)
    (hcongr :
      ∀ y ∈ L.translatedCoset x,
        ∀ z ∈ L.translatedCoset x,
          N y - N z - (y - z) ∈ L)
    (hnorm :
      ∀ y ∈ L.translatedCoset x,
        ∀ z ∈ L.translatedCoset x,
          ‖N y - N z - (y - z)‖ ≤
            (q : ℝ) * ‖y - z‖)
    {w : E} (hw : w ∈ L.translatedCoset x) :
    ContractingWith q
      ((mapsTo_cosetCorrection L x N hNx hcongr hw).restrict
        (cosetCorrection N w)
        (L.translatedCoset x) (L.translatedCoset x)) := by
  refine ⟨hq, LipschitzWith.of_dist_le_mul ?_⟩
  intro y z
  change
    dist (cosetCorrection N w y) (cosetCorrection N w z) ≤
      (q : ℝ) * dist (y : E) (z : E)
  rw [dist_eq_norm, dist_eq_norm]
  calc
    ‖cosetCorrection N w (y : E) - cosetCorrection N w (z : E)‖ =
        ‖-(N (y : E) - N (z : E) - ((y : E) - (z : E)))‖ := by
      congr 1
      dsimp [cosetCorrection]
      abel
    _ = ‖N (y : E) - N (z : E) - ((y : E) - (z : E))‖ := norm_neg _
    _ ≤ (q : ℝ) * ‖(y : E) - (z : E)‖ :=
      hnorm (y : E) y.property (z : E) z.property

/-- The congruence error condition also makes `N` itself preserve the coset. -/
theorem mapsTo_of_sub_sub_mem
    (L : AddSubgroup E) (x : E)
    (N : E → E) (hNx : N x = x)
    (hcongr :
      ∀ y ∈ L.translatedCoset x,
        ∀ z ∈ L.translatedCoset x,
          N y - N z - (y - z) ∈ L) :
    Set.MapsTo N (L.translatedCoset x) (L.translatedCoset x) := by
  intro y hy
  rw [mem_translatedCoset_iff] at hy ⊢
  have herr :=
    hcongr y hy x (center_mem_translatedCoset L x)
  have heq :
      N y - x =
        (N y - N x - (y - x)) + (y - x) := by
    rw [hNx]
    abel
  rw [heq]
  exact L.add_mem herr hy

/-- Every target in the coset has a preimage in the coset. -/
theorem exists_mem_translatedCoset_map_eq
    [IsTopologicalAddGroup E] [CompleteSpace E]
    (L : AddSubgroup E) (x : E)
    (hL : IsClosed (L : Set E))
    (N : E → E) (hNx : N x = x)
    {q : ℝ≥0} (hq : q < 1)
    (hcongr :
      ∀ y ∈ L.translatedCoset x,
        ∀ z ∈ L.translatedCoset x,
          N y - N z - (y - z) ∈ L)
    (hnorm :
      ∀ y ∈ L.translatedCoset x,
        ∀ z ∈ L.translatedCoset x,
          ‖N y - N z - (y - z)‖ ≤
            (q : ℝ) * ‖y - z‖)
    {w : E} (hw : w ∈ L.translatedCoset x) :
    ∃ y ∈ L.translatedCoset x, N y = w := by
  let Φ : E → E := cosetCorrection N w
  have hmaps :
      Set.MapsTo Φ (L.translatedCoset x) (L.translatedCoset x) :=
    mapsTo_cosetCorrection L x N hNx hcongr hw
  have hcontract :
      ContractingWith q
        (hmaps.restrict Φ (L.translatedCoset x) (L.translatedCoset x)) :=
    contractingWith_cosetCorrection L x N hNx hq hcongr hnorm hw
  obtain ⟨y, hy, hfixed, -, -⟩ :=
    hcontract.exists_fixedPoint'
      (isClosed_translatedCoset L x hL).isComplete
      hmaps
      (center_mem_translatedCoset L x)
      (edist_ne_top x (Φ x))
  refine ⟨y, hy, ?_⟩
  change Φ y = y at hfixed
  have hwNy : w - N y = 0 := by
    calc
      w - N y = Φ y - y := by
        dsimp [Φ, cosetCorrection]
        abel
      _ = y - y := congrArg (fun t => t - y) hfixed
      _ = 0 := sub_self y
  exact (sub_eq_zero.mp hwNy).symm

/-- The strict norm remainder estimate makes `N` injective on the coset. -/
theorem injOn_of_norm_sub_sub_le
    (L : AddSubgroup E) (x : E)
    (N : E → E)
    {q : ℝ≥0} (hq : q < 1)
    (hnorm :
      ∀ y ∈ L.translatedCoset x,
        ∀ z ∈ L.translatedCoset x,
          ‖N y - N z - (y - z)‖ ≤
            (q : ℝ) * ‖y - z‖) :
    Set.InjOn N (L.translatedCoset x) := by
  intro y hy z hz hyz
  have hle := hnorm y hy z hz
  rw [hyz] at hle
  simp only [sub_self, zero_sub, norm_neg] at hle
  have hq_real : (q : ℝ) < 1 := by
    exact_mod_cast hq
  have hnorm_zero : ‖y - z‖ = 0 := by
    nlinarith [norm_nonneg (y - z)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hnorm_zero)

/-- Under the congruence and strict norm error conditions, `N` maps the closed
coset exactly onto itself. -/
theorem image_translatedCoset_eq
    [IsTopologicalAddGroup E] [CompleteSpace E]
    (L : AddSubgroup E) (x : E)
    (hL : IsClosed (L : Set E))
    (N : E → E) (hNx : N x = x)
    {q : ℝ≥0} (hq : q < 1)
    (hcongr :
      ∀ y ∈ L.translatedCoset x,
        ∀ z ∈ L.translatedCoset x,
          N y - N z - (y - z) ∈ L)
    (hnorm :
      ∀ y ∈ L.translatedCoset x,
        ∀ z ∈ L.translatedCoset x,
          ‖N y - N z - (y - z)‖ ≤
            (q : ℝ) * ‖y - z‖) :
    N '' L.translatedCoset x = L.translatedCoset x := by
  apply Set.Subset.antisymm
  · rintro _ ⟨y, hy, rfl⟩
    exact mapsTo_of_sub_sub_mem L x N hNx hcongr hy
  · intro w hw
    obtain ⟨y, hy, hyw⟩ :=
      exists_mem_translatedCoset_map_eq L x hL N hNx hq hcongr hnorm hw
    exact ⟨y, hy, hyw⟩

/-- The preceding hypotheses package `N` as a bijection of the closed coset
onto itself. -/
theorem image_translatedCoset_eq_and_injOn
    [IsTopologicalAddGroup E] [CompleteSpace E]
    (L : AddSubgroup E) (x : E)
    (hL : IsClosed (L : Set E))
    (N : E → E) (hNx : N x = x)
    {q : ℝ≥0} (hq : q < 1)
    (hcongr :
      ∀ y ∈ L.translatedCoset x,
        ∀ z ∈ L.translatedCoset x,
          N y - N z - (y - z) ∈ L)
    (hnorm :
      ∀ y ∈ L.translatedCoset x,
        ∀ z ∈ L.translatedCoset x,
          ‖N y - N z - (y - z)‖ ≤
            (q : ℝ) * ‖y - z‖) :
    N '' L.translatedCoset x = L.translatedCoset x ∧
      Set.InjOn N (L.translatedCoset x) :=
  ⟨image_translatedCoset_eq L x hL N hNx hq hcongr hnorm,
    injOn_of_norm_sub_sub_le L x N hq hnorm⟩

/-- Without assuming that `N` fixes the center, the same two-point hypotheses
make `N` carry the source coset exactly onto the coset centered at `N x`.

The proof applies the center-fixing theorem to
`z ↦ x + (N z - N x)`. -/
theorem image_translatedCoset_eq_translatedCoset_apply_and_injOn
    [IsTopologicalAddGroup E] [CompleteSpace E]
    (L : AddSubgroup E) (x : E)
    (hL : IsClosed (L : Set E))
    (N : E → E)
    {q : ℝ≥0} (hq : q < 1)
    (hcongr :
      ∀ y ∈ L.translatedCoset x,
        ∀ z ∈ L.translatedCoset x,
          N y - N z - (y - z) ∈ L)
    (hnorm :
      ∀ y ∈ L.translatedCoset x,
        ∀ z ∈ L.translatedCoset x,
          ‖N y - N z - (y - z)‖ ≤
            (q : ℝ) * ‖y - z‖) :
    N '' L.translatedCoset x = L.translatedCoset (N x) ∧
      Set.InjOn N (L.translatedCoset x) := by
  let M : E → E := fun z => x + (N z - N x)
  have hMx : M x = x := by
    simp [M]
  have hMerror :
      ∀ y z, M y - M z - (y - z) =
        N y - N z - (y - z) := by
    intro y z
    dsimp [M]
    abel
  have hMcongr :
      ∀ y ∈ L.translatedCoset x,
        ∀ z ∈ L.translatedCoset x,
          M y - M z - (y - z) ∈ L := by
    intro y hy z hz
    rw [hMerror]
    exact hcongr y hy z hz
  have hMnorm :
      ∀ y ∈ L.translatedCoset x,
        ∀ z ∈ L.translatedCoset x,
          ‖M y - M z - (y - z)‖ ≤
            (q : ℝ) * ‖y - z‖ := by
    intro y hy z hz
    rw [hMerror]
    exact hnorm y hy z hz
  have hMimage :
      M '' L.translatedCoset x = L.translatedCoset x :=
    image_translatedCoset_eq L x hL M hMx hq hMcongr hMnorm
  constructor
  · apply Set.Subset.antisymm
    · rintro _ ⟨z, hz, rfl⟩
      rw [mem_translatedCoset_iff]
      have hMz : M z ∈ L.translatedCoset x := by
        rw [← hMimage]
        exact ⟨z, hz, rfl⟩
      rw [mem_translatedCoset_iff] at hMz
      have heq : N z - N x = M z - x := by
        dsimp [M]
        abel
      rwa [heq]
    · intro w hw
      rw [mem_translatedCoset_iff] at hw
      let u : E := x + (w - N x)
      have hu : u ∈ L.translatedCoset x := by
        rw [mem_translatedCoset_iff]
        have heu : u - x = w - N x := by
          dsimp [u]
          abel
        rwa [heu]
      rw [← hMimage] at hu
      obtain ⟨z, hz, hzu⟩ := hu
      refine ⟨z, hz, ?_⟩
      have heq : N z - w = M z - u := by
        dsimp [M, u]
        abel
      rw [hzu, sub_self] at heq
      exact sub_eq_zero.mp heq
  · exact injOn_of_norm_sub_sub_le L x N hq hnorm

end AddSubgroup
