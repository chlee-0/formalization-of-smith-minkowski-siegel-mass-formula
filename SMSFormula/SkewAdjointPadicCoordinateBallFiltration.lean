import SMSFormula.SkewAdjointPadicCoordinateBallBasis
import Mathlib.Analysis.Normed.Group.Ultra

/-!
# The additive filtration of p-adic coordinate balls

This module packages the transported coordinate lattice as an additive
subgroup and its uniform `p ^ k` images as an antitone family of additive
subgroups. The subgroup structure supplies the exact coset geometry needed by
a later disjoint refinement: same-level translated balls are equal or
disjoint, and an intersecting higher-level ball is contained in the
lower-level ball.

No cover is selected, no Haar scaling is computed, and no nonlinear
transition statement is used.
-/

noncomputable section

open MeasureTheory
open scoped Matrix Matrix.Norms.Operator Topology Pointwise

namespace Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

local instance skewAdjointPadicCoordinateBallFiltrationMeasurableSpace
    (F : Matrix ι ι ℚ) (p : ℕ) [Fact (Nat.Prime p)] :
    MeasurableSpace
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  borel _

local instance skewAdjointPadicCoordinateBallFiltrationBorelSpace
    (F : Matrix ι ι ℚ) (p : ℕ) [Fact (Nat.Prime p)] :
    BorelSpace
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  ⟨rfl⟩

/-- The transported coordinate lattice as an additive subgroup. -/
def skewAdjointPadicCoordinateLatticeAddSubgroup
    (F : Matrix ι ι ℚ) (p : ℕ) [Fact (Nat.Prime p)] :
    AddSubgroup
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule where
  carrier := skewAdjointPadicCoordinateLattice F p
  zero_mem' := zero_mem_skewAdjointPadicCoordinateLattice F p
  add_mem' := by
    intro x y hx hy
    change x ∈ skewAdjointPadicCoordinateLattice F p at hx
    change y ∈ skewAdjointPadicCoordinateLattice F p at hy
    change x + y ∈ skewAdjointPadicCoordinateLattice F p
    rw [mem_skewAdjointPadicCoordinateLattice_iff] at hx hy ⊢
    intro i
    rw [map_add, Pi.add_apply]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans
      (max_le (hx i) (hy i))
  neg_mem' := by
    intro x hx
    change x ∈ skewAdjointPadicCoordinateLattice F p at hx
    change -x ∈ skewAdjointPadicCoordinateLattice F p
    rw [mem_skewAdjointPadicCoordinateLattice_iff] at hx ⊢
    intro i
    simpa using hx i

@[simp]
theorem skewAdjointPadicCoordinateLatticeAddSubgroup_coe
    (F : Matrix ι ι ℚ) (p : ℕ) [Fact (Nat.Prime p)] :
    (skewAdjointPadicCoordinateLatticeAddSubgroup F p : Set _) =
      (skewAdjointPadicCoordinateLattice F p :
        Set (skewAdjointMatricesLieSubalgebra
          (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule) := rfl

/-- The coordinate lattice is stable under any scalar of norm at most one. -/
theorem smul_mem_skewAdjointPadicCoordinateLatticeAddSubgroup
    (F : Matrix ι ι ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    {a : ℚ_[p]} (ha : ‖a‖ ≤ 1)
    {x : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule}
    (hx : x ∈ skewAdjointPadicCoordinateLatticeAddSubgroup F p) :
    a • x ∈ skewAdjointPadicCoordinateLatticeAddSubgroup F p := by
  change x ∈ skewAdjointPadicCoordinateLattice F p at hx
  change a • x ∈ skewAdjointPadicCoordinateLattice F p
  rw [mem_skewAdjointPadicCoordinateLattice_iff] at hx ⊢
  intro i
  rw [map_smul, Pi.smul_apply, norm_smul]
  calc
    ‖a‖ * ‖skewAdjointPadicCoordinateEquiv F p x i‖ ≤ 1 * 1 :=
      mul_le_mul ha (hx i) (norm_nonneg _) zero_le_one
    _ = 1 := one_mul 1

/-- The level-`k` uniform coordinate ball as the additive image of the
coordinate lattice under multiplication by `p ^ k`. -/
def skewAdjointPadicUniformCoordinateBallAddSubgroup
    (F : Matrix ι ι ℚ) (p k : ℕ) [Fact (Nat.Prime p)] :
    AddSubgroup
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  (skewAdjointPadicCoordinateLatticeAddSubgroup F p).map
    (skewAdjointPadicUniformCoordinateDilation F p k).toLinearEquiv.toAddEquiv.toAddMonoidHom

@[simp]
theorem skewAdjointPadicUniformCoordinateBallAddSubgroup_coe
    (F : Matrix ι ι ℚ) (p k : ℕ) [Fact (Nat.Prime p)] :
    (skewAdjointPadicUniformCoordinateBallAddSubgroup F p k : Set _) =
      skewAdjointPadicUniformCoordinateBall F p k := by
  rw [skewAdjointPadicUniformCoordinateBallAddSubgroup, AddSubgroup.coe_map]
  rfl

/-- The level-`k+1` uniform coordinate subgroup is contained in level `k`. -/
theorem skewAdjointPadicUniformCoordinateBallAddSubgroup_succ_le
    (F : Matrix ι ι ℚ) (p k : ℕ) [Fact (Nat.Prime p)] :
    skewAdjointPadicUniformCoordinateBallAddSubgroup F p (k + 1) ≤
      skewAdjointPadicUniformCoordinateBallAddSubgroup F p k := by
  intro y hy
  rw [skewAdjointPadicUniformCoordinateBallAddSubgroup,
    AddSubgroup.mem_map] at hy ⊢
  obtain ⟨z, hz, rfl⟩ := hy
  refine ⟨(p : ℚ_[p]) • z, ?_, ?_⟩
  · exact smul_mem_skewAdjointPadicCoordinateLatticeAddSubgroup
      F p (le_of_lt Padic.norm_p_lt_one) hz
  · simp [pow_succ, smul_smul, mul_comm]

/-- The uniform coordinate-ball additive subgroups form an antitone
filtration. -/
theorem antitone_skewAdjointPadicUniformCoordinateBallAddSubgroup
    (F : Matrix ι ι ℚ) (p : ℕ) [Fact (Nat.Prime p)] :
    Antitone
      (fun k => skewAdjointPadicUniformCoordinateBallAddSubgroup F p k) :=
  antitone_nat_of_succ_le
    (fun k =>
      skewAdjointPadicUniformCoordinateBallAddSubgroup_succ_le F p k)

/-- The level-`k+1` uniform coordinate ball is contained in level `k`, stated
on the original ball sets. -/
theorem skewAdjointPadicUniformCoordinateBall_succ_subset
    (F : Matrix ι ι ℚ) (p k : ℕ) [Fact (Nat.Prime p)] :
    skewAdjointPadicUniformCoordinateBall F p (k + 1) ⊆
      skewAdjointPadicUniformCoordinateBall F p k := by
  rw [← skewAdjointPadicUniformCoordinateBallAddSubgroup_coe,
    ← skewAdjointPadicUniformCoordinateBallAddSubgroup_coe]
  exact skewAdjointPadicUniformCoordinateBallAddSubgroup_succ_le F p k

/-- Uniform coordinate-ball sets are antitone in their level. -/
theorem antitone_skewAdjointPadicUniformCoordinateBall
    (F : Matrix ι ι ℚ) (p : ℕ) [Fact (Nat.Prime p)] :
    Antitone (fun k => skewAdjointPadicUniformCoordinateBall F p k) := by
  intro k l hkl
  change skewAdjointPadicUniformCoordinateBall F p l ⊆
    skewAdjointPadicUniformCoordinateBall F p k
  rw [← skewAdjointPadicUniformCoordinateBallAddSubgroup_coe,
    ← skewAdjointPadicUniformCoordinateBallAddSubgroup_coe]
  exact antitone_skewAdjointPadicUniformCoordinateBallAddSubgroup F p hkl

/-- Membership in a translated uniform coordinate ball is membership of the
centered difference in its additive subgroup. -/
theorem mem_skewAdjointPadicTranslatedUniformCoordinateBall_iff_mem_addSubgroup
    (F : Matrix ι ι ℚ) (p k : ℕ) [Fact (Nat.Prime p)]
    (x y : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule) :
    y ∈ skewAdjointPadicTranslatedUniformCoordinateBall F p k x ↔
      y - x ∈ skewAdjointPadicUniformCoordinateBallAddSubgroup F p k := by
  rw [mem_skewAdjointPadicTranslatedUniformCoordinateBall_iff]
  change
    y - x ∈ skewAdjointPadicUniformCoordinateBall F p k ↔
      y - x ∈
        (skewAdjointPadicUniformCoordinateBallAddSubgroup F p k : Set _)
  rw [skewAdjointPadicUniformCoordinateBallAddSubgroup_coe]

/-- The difference of two points in the same translated coordinate ball lies
in the corresponding zero-centered coordinate ball. -/
theorem sub_mem_skewAdjointPadicUniformCoordinateBall_of_mem_translated
    (F : Matrix ι ι ℚ) (p k : ℕ) [Fact (Nat.Prime p)]
    (x y z : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule)
    (hy : y ∈ skewAdjointPadicTranslatedUniformCoordinateBall F p k x)
    (hz : z ∈ skewAdjointPadicTranslatedUniformCoordinateBall F p k x) :
    y - z ∈ skewAdjointPadicUniformCoordinateBall F p k := by
  rw [mem_skewAdjointPadicTranslatedUniformCoordinateBall_iff_mem_addSubgroup]
    at hy hz
  rw [← skewAdjointPadicUniformCoordinateBallAddSubgroup_coe]
  have hsub :=
    (skewAdjointPadicUniformCoordinateBallAddSubgroup F p k).sub_mem hy hz
  have heq : (y - x) - (z - x) = y - z := by abel
  rwa [heq] at hsub

/-- Intersecting translated coordinate balls at the same level are equal. -/
theorem skewAdjointPadicTranslatedUniformCoordinateBall_eq_of_nonempty_inter
    (F : Matrix ι ι ℚ) (p k : ℕ) [Fact (Nat.Prime p)]
    {x y : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule}
    (hinter :
      (skewAdjointPadicTranslatedUniformCoordinateBall F p k x ∩
        skewAdjointPadicTranslatedUniformCoordinateBall F p k y).Nonempty) :
    skewAdjointPadicTranslatedUniformCoordinateBall F p k x =
      skewAdjointPadicTranslatedUniformCoordinateBall F p k y := by
  obtain ⟨z, hzx, hzy⟩ := hinter
  rw [mem_skewAdjointPadicTranslatedUniformCoordinateBall_iff_mem_addSubgroup]
    at hzx hzy
  have hxy :
      x - y ∈ skewAdjointPadicUniformCoordinateBallAddSubgroup F p k := by
    have hsub :=
      (skewAdjointPadicUniformCoordinateBallAddSubgroup F p k).sub_mem
        hzy hzx
    have heq : (z - y) - (z - x) = x - y := by abel
    rwa [heq] at hsub
  ext w
  constructor
  · intro hw
    rw [mem_skewAdjointPadicTranslatedUniformCoordinateBall_iff_mem_addSubgroup]
      at hw ⊢
    have hadd :=
      (skewAdjointPadicUniformCoordinateBallAddSubgroup F p k).add_mem
        hw hxy
    have heq : (w - x) + (x - y) = w - y := by abel
    rwa [heq] at hadd
  · intro hw
    rw [mem_skewAdjointPadicTranslatedUniformCoordinateBall_iff_mem_addSubgroup]
      at hw ⊢
    have hyx :
        y - x ∈ skewAdjointPadicUniformCoordinateBallAddSubgroup F p k := by
      simpa only [neg_sub] using
        (skewAdjointPadicUniformCoordinateBallAddSubgroup F p k).neg_mem hxy
    have hadd :=
      (skewAdjointPadicUniformCoordinateBallAddSubgroup F p k).add_mem
        hw hyx
    have heq : (w - y) + (y - x) = w - x := by abel
    rwa [heq] at hadd

/-- Any two translated coordinate balls at the same level are disjoint or
equal. -/
theorem skewAdjointPadicTranslatedUniformCoordinateBall_disjoint_or_eq
    (F : Matrix ι ι ℚ) (p k : ℕ) [Fact (Nat.Prime p)]
    (x y : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule) :
    Disjoint
        (skewAdjointPadicTranslatedUniformCoordinateBall F p k x)
        (skewAdjointPadicTranslatedUniformCoordinateBall F p k y) ∨
      skewAdjointPadicTranslatedUniformCoordinateBall F p k x =
        skewAdjointPadicTranslatedUniformCoordinateBall F p k y := by
  rcases Set.disjoint_or_nonempty_inter
      (skewAdjointPadicTranslatedUniformCoordinateBall F p k x)
      (skewAdjointPadicTranslatedUniformCoordinateBall F p k y) with h | h
  · exact Or.inl h
  · exact Or.inr
      (skewAdjointPadicTranslatedUniformCoordinateBall_eq_of_nonempty_inter
        F p k h)

/-- If `k ≤ l`, then an intersecting level-`l` translated ball is contained
in the level-`k` translated ball. -/
theorem
    skewAdjointPadicTranslatedUniformCoordinateBall_subset_of_le_of_nonempty_inter
    (F : Matrix ι ι ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    {k l : ℕ} (hkl : k ≤ l)
    {x y : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule}
    (hinter :
      (skewAdjointPadicTranslatedUniformCoordinateBall F p k x ∩
        skewAdjointPadicTranslatedUniformCoordinateBall F p l y).Nonempty) :
    skewAdjointPadicTranslatedUniformCoordinateBall F p l y ⊆
      skewAdjointPadicTranslatedUniformCoordinateBall F p k x := by
  obtain ⟨z, hzx, hzy⟩ := hinter
  rw [mem_skewAdjointPadicTranslatedUniformCoordinateBall_iff_mem_addSubgroup]
    at hzx hzy
  have hle :
      skewAdjointPadicUniformCoordinateBallAddSubgroup F p l ≤
        skewAdjointPadicUniformCoordinateBallAddSubgroup F p k :=
    antitone_skewAdjointPadicUniformCoordinateBallAddSubgroup F p hkl
  have hyx :
      y - x ∈ skewAdjointPadicUniformCoordinateBallAddSubgroup F p k := by
    have hsub :=
      (skewAdjointPadicUniformCoordinateBallAddSubgroup F p k).sub_mem
        hzx (hle hzy)
    have heq : (z - x) - (z - y) = y - x := by abel
    rwa [heq] at hsub
  intro w hw
  rw [mem_skewAdjointPadicTranslatedUniformCoordinateBall_iff_mem_addSubgroup]
    at hw ⊢
  have hadd :=
    (skewAdjointPadicUniformCoordinateBallAddSubgroup F p k).add_mem
      (hle hw) hyx
  have heq : (w - y) + (y - x) = w - x := by abel
  rwa [heq] at hadd

/-- If the center of a level-`l` ball belongs to a level-`k` ball and
`k ≤ l`, then the level-`l` ball is contained in the level-`k` ball. -/
theorem
    skewAdjointPadicTranslatedUniformCoordinateBall_subset_of_le_of_mem
    (F : Matrix ι ι ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    {k l : ℕ} (hkl : k ≤ l)
    {x y : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule}
    (hy :
      y ∈ skewAdjointPadicTranslatedUniformCoordinateBall F p k x) :
    skewAdjointPadicTranslatedUniformCoordinateBall F p l y ⊆
      skewAdjointPadicTranslatedUniformCoordinateBall F p k x := by
  apply
    skewAdjointPadicTranslatedUniformCoordinateBall_subset_of_le_of_nonempty_inter
      F p hkl
  refine ⟨y, hy, ?_⟩
  rw [mem_skewAdjointPadicTranslatedUniformCoordinateBall_iff_mem_addSubgroup]
  simp

/-- If `k ≤ l`, then a level-`k` translated ball and a level-`l` translated
ball are disjoint, or the latter is contained in the former. -/
theorem
    skewAdjointPadicTranslatedUniformCoordinateBall_disjoint_or_subset_of_le
    (F : Matrix ι ι ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    {k l : ℕ} (hkl : k ≤ l)
    (x y : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule) :
    Disjoint
        (skewAdjointPadicTranslatedUniformCoordinateBall F p k x)
        (skewAdjointPadicTranslatedUniformCoordinateBall F p l y) ∨
      skewAdjointPadicTranslatedUniformCoordinateBall F p l y ⊆
        skewAdjointPadicTranslatedUniformCoordinateBall F p k x := by
  rcases Set.disjoint_or_nonempty_inter
      (skewAdjointPadicTranslatedUniformCoordinateBall F p k x)
      (skewAdjointPadicTranslatedUniformCoordinateBall F p l y) with h | h
  · exact Or.inl h
  · exact Or.inr
      (skewAdjointPadicTranslatedUniformCoordinateBall_subset_of_le_of_nonempty_inter
        F p hkl h)

end Matrix
