import SMSFormula.PadicCayleyTranslatedChartOverlapForwardWeightedCountableCover
import SMSFormula.SkewAdjointPadicCoordinateBallFiltration
import Mathlib.Topology.Compactness.Lindelof

/-!
# Pairwise-disjoint certified source balls for p-adic overlap gluing

Starting from the countable cover by locally certified forward-weighted
coordinate balls, retain the balls meeting no strictly lower-level cover ball.
The coordinate-ball filtration makes the resulting set-valued family
pairwise disjoint, while the minimal-level argument shows that it still covers
the ambient source overlap.

Passing to the set-valued image removes duplicate presentations.  For each
resulting ball, this module chooses one original certified center and retains
its level, target tangent coset, and exact local weighted pushforward.  Target
disjointness, target coverage, and measure gluing are not asserted here.
-/

noncomputable section

open MeasureTheory
open scoped Matrix Matrix.Norms.Operator Topology NNReal ENNReal

namespace PositiveDefiniteIntegralLattice

open Matrix

variable (p : ℕ) [Fact (Nat.Prime p)] (n : ℕ)

local instance padicCayleyOverlapForwardWeightedDisjointMeasurableSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    MeasurableSpace
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  borel _

local instance padicCayleyOverlapForwardWeightedDisjointBorelSpace
    (F : Matrix (Fin n) (Fin n) ℚ) :
    BorelSpace
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  ⟨rfl⟩

/-- A certified source ball written directly as the translated coordinate
ball at its ambient center. -/
theorem skewAdjointPadicCayleyTranslatedSourceOverlapCertifiedSourceBall_eq
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.det ≠ 0)
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p])))
    (x : {x // x ∈
      skewAdjointPadicCayleyTranslatedSourceOverlapAmbientSet
        p n F hF c d}) :
    skewAdjointPadicCayleyTranslatedSourceOverlapCertifiedSourceBall
        p n F hF c d x =
      Matrix.skewAdjointPadicTranslatedUniformCoordinateBall F p
        (skewAdjointPadicCayleyTranslatedSourceOverlapCertifiedLevel
          p n F hF c d x)
        x := by
  rw [
    skewAdjointPadicCayleyTranslatedSourceOverlapCertifiedSourceBall,
    skewAdjointPadicCayleyTranslatedSourceOverlapAmbientInclusion_certifiedPoint]

/-- One chosen countable set of certified centers whose source balls cover the
ambient source overlap. -/
def skewAdjointPadicCayleyTranslatedSourceOverlapCertifiedCoverCenterSet
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.det ≠ 0)
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p]))) :
    Set {x // x ∈
      skewAdjointPadicCayleyTranslatedSourceOverlapAmbientSet
        p n F hF c d} :=
  Classical.choose
    (exists_countable_skewAdjointPadicCayleyTranslatedSourceOverlapCertifiedSourceBall_cover
      p n F hF c d)

theorem
    skewAdjointPadicCayleyTranslatedSourceOverlapCertifiedCoverCenterSet_spec
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.det ≠ 0)
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p]))) :
    (skewAdjointPadicCayleyTranslatedSourceOverlapCertifiedCoverCenterSet
        p n F hF c d).Countable ∧
    skewAdjointPadicCayleyTranslatedSourceOverlapAmbientSet
        p n F hF c d =
      ⋃ x ∈
        skewAdjointPadicCayleyTranslatedSourceOverlapCertifiedCoverCenterSet
          p n F hF c d,
        skewAdjointPadicCayleyTranslatedSourceOverlapCertifiedSourceBall
          p n F hF c d x ∧
    (∀ x ∈
        skewAdjointPadicCayleyTranslatedSourceOverlapCertifiedCoverCenterSet
          p n F hF c d,
      skewAdjointPadicCayleyTranslatedSourceOverlapCertifiedSourceBall
          p n F hF c d x ⊆
        skewAdjointPadicCayleyTranslatedSourceOverlapAmbientSet
          p n F hF c d) ∧
    ∀ x ∈
        skewAdjointPadicCayleyTranslatedSourceOverlapCertifiedCoverCenterSet
          p n F hF c d,
      Measure.map
          (skewAdjointPadicCayleyTranslatedSourceOverlapAmbientMeasurableTransition
            p n F hF c d)
          (((Matrix.skewAdjointPadicCoordinateMeasure F p).restrict
            (skewAdjointPadicCayleyTranslatedSourceOverlapCertifiedSourceBall
              p n F hF c d x)).withDensity
            (skewAdjointPadicCayleyTranslatedSourceOverlapAmbientTransitionJacobian
              p n F hF c d)) =
        (Matrix.skewAdjointPadicCoordinateMeasure F p).restrict
          (skewAdjointPadicCayleyTranslatedSourceOverlapCertifiedTargetBall
            p n F hF c d x) :=
  Classical.choose_spec
    (exists_countable_skewAdjointPadicCayleyTranslatedSourceOverlapCertifiedSourceBall_cover
      p n F hF c d)

/-- Certified centers whose balls meet no strictly lower-level ball from the
chosen countable cover. -/
def skewAdjointPadicCayleyTranslatedSourceOverlapCertifiedSelectedCenterSet
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.det ≠ 0)
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p]))) :
    Set {x // x ∈
      skewAdjointPadicCayleyTranslatedSourceOverlapAmbientSet
        p n F hF c d} :=
  {x |
    x ∈
      skewAdjointPadicCayleyTranslatedSourceOverlapCertifiedCoverCenterSet
        p n F hF c d ∧
    ∀ y ∈
        skewAdjointPadicCayleyTranslatedSourceOverlapCertifiedCoverCenterSet
          p n F hF c d,
      skewAdjointPadicCayleyTranslatedSourceOverlapCertifiedLevel
          p n F hF c d y <
        skewAdjointPadicCayleyTranslatedSourceOverlapCertifiedLevel
          p n F hF c d x →
      Disjoint
        (skewAdjointPadicCayleyTranslatedSourceOverlapCertifiedSourceBall
          p n F hF c d y)
        (skewAdjointPadicCayleyTranslatedSourceOverlapCertifiedSourceBall
          p n F hF c d x)}

/-- The set-valued pairwise-disjoint source-ball family; taking an image
removes duplicate presentations of the same ball. -/
def skewAdjointPadicCayleyTranslatedSourceOverlapCertifiedDisjointSourceBallSet
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.det ≠ 0)
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p]))) :
    Set (Set (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule) :=
  skewAdjointPadicCayleyTranslatedSourceOverlapCertifiedSourceBall
    p n F hF c d ''
      skewAdjointPadicCayleyTranslatedSourceOverlapCertifiedSelectedCenterSet
        p n F hF c d

/-- The disjoint certified source-ball family is countable, pairwise disjoint,
contained in the ambient source overlap, and covers it exactly. Every member
has a selected certified-center presentation. -/
theorem
    skewAdjointPadicCayleyTranslatedSourceOverlapCertifiedDisjointSourceBallSet_spec
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.det ≠ 0)
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p]))) :
    (skewAdjointPadicCayleyTranslatedSourceOverlapCertifiedDisjointSourceBallSet
        p n F hF c d).Countable ∧
    (skewAdjointPadicCayleyTranslatedSourceOverlapCertifiedDisjointSourceBallSet
        p n F hF c d).PairwiseDisjoint id ∧
    (∀ B ∈
        skewAdjointPadicCayleyTranslatedSourceOverlapCertifiedDisjointSourceBallSet
          p n F hF c d,
      ∃ x ∈
          skewAdjointPadicCayleyTranslatedSourceOverlapCertifiedSelectedCenterSet
            p n F hF c d,
        skewAdjointPadicCayleyTranslatedSourceOverlapCertifiedSourceBall
          p n F hF c d x = B) ∧
    (∀ B ∈
        skewAdjointPadicCayleyTranslatedSourceOverlapCertifiedDisjointSourceBallSet
          p n F hF c d,
      B ⊆
        skewAdjointPadicCayleyTranslatedSourceOverlapAmbientSet
          p n F hF c d) ∧
    ⋃₀
        (skewAdjointPadicCayleyTranslatedSourceOverlapCertifiedDisjointSourceBallSet
          p n F hF c d) =
      skewAdjointPadicCayleyTranslatedSourceOverlapAmbientSet
        p n F hF c d := by
  classical
  let U :=
    skewAdjointPadicCayleyTranslatedSourceOverlapAmbientSet
      p n F hF c d
  let t :=
    skewAdjointPadicCayleyTranslatedSourceOverlapCertifiedCoverCenterSet
      p n F hF c d
  let level :
      {x // x ∈ U} → ℕ :=
    skewAdjointPadicCayleyTranslatedSourceOverlapCertifiedLevel
      p n F hF c d
  let ball :
      {x // x ∈ U} →
        Set (skewAdjointMatricesLieSubalgebra
          (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
    skewAdjointPadicCayleyTranslatedSourceOverlapCertifiedSourceBall
      p n F hF c d
  let selected : Set {x // x ∈ U} :=
    skewAdjointPadicCayleyTranslatedSourceOverlapCertifiedSelectedCenterSet
      p n F hF c d
  let balls :
      Set (Set (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule) :=
    skewAdjointPadicCayleyTranslatedSourceOverlapCertifiedDisjointSourceBallSet
      p n F hF c d
  have htcount : t.Countable :=
    (skewAdjointPadicCayleyTranslatedSourceOverlapCertifiedCoverCenterSet_spec
      p n F hF c d).1
  have hcover : U = ⋃ x ∈ t, ball x :=
    (skewAdjointPadicCayleyTranslatedSourceOverlapCertifiedCoverCenterSet_spec
      p n F hF c d).2.1
  have hball : ∀ x : {x // x ∈ U},
      ball x =
        Matrix.skewAdjointPadicTranslatedUniformCoordinateBall F p
          (level x) x := by
    intro x
    exact
      skewAdjointPadicCayleyTranslatedSourceOverlapCertifiedSourceBall_eq
        p n F hF c d x
  have hselected_countable : selected.Countable :=
    htcount.mono fun _ hx => hx.1
  have hballs_countable : balls.Countable :=
    hselected_countable.image ball
  have hballs_pairwise : balls.PairwiseDisjoint id := by
    intro B hB C hC hBC
    obtain ⟨x, hx, rfl⟩ := hB
    obtain ⟨y, hy, rfl⟩ := hC
    change Disjoint (ball x) (ball y)
    rcases lt_trichotomy (level x) (level y) with hxy | hxy | hxy
    · exact hy.2 x hx.1 hxy
    · rcases
        Matrix.skewAdjointPadicTranslatedUniformCoordinateBall_disjoint_or_eq
          F p (level x) x y with hdisj | heq
      · simpa only [hball x, hball y, hxy] using hdisj
      · have hballxy : ball x = ball y := by
          calc
            ball x =
                Matrix.skewAdjointPadicTranslatedUniformCoordinateBall
                  F p (level x) x := hball x
            _ =
                Matrix.skewAdjointPadicTranslatedUniformCoordinateBall
                  F p (level x) y := heq
            _ =
                Matrix.skewAdjointPadicTranslatedUniformCoordinateBall
                  F p (level y) y := by rw [hxy]
            _ = ball y := (hball y).symm
        exact (hBC hballxy).elim
    · exact (hx.2 y hy.1 hxy).symm
  refine ⟨hballs_countable, hballs_pairwise, ?_, ?_, ?_⟩
  · intro B hB
    exact hB
  · intro B hB
    obtain ⟨x, hx, rfl⟩ := hB
    exact
      skewAdjointPadicCayleyTranslatedSourceOverlapCertifiedSourceBall_subset
        p n F hF c d x
  · apply Set.Subset.antisymm
    · exact Set.sUnion_subset fun B hB => by
        obtain ⟨x, hx, rfl⟩ := hB
        exact
          skewAdjointPadicCayleyTranslatedSourceOverlapCertifiedSourceBall_subset
            p n F hF c d x
    · intro z hzU
      have hzcover : z ∈ ⋃ x ∈ t, ball x := by
        rw [← hcover]
        exact hzU
      rcases Set.mem_iUnion.mp hzcover with ⟨i, hzcover⟩
      rcases Set.mem_iUnion.mp hzcover with ⟨hi, hzi⟩
      let P : ℕ → Prop := fun k =>
        ∃ j : {x // x ∈ U},
          j ∈ t ∧ level j = k ∧ (ball i ∩ ball j).Nonempty
      have hPi : P (level i) :=
        ⟨i, hi, rfl, ⟨z, hzi, hzi⟩⟩
      have hP : ∃ k, P k := ⟨level i, hPi⟩
      obtain ⟨j, hjt, hjlevel, hinter⟩ := Nat.find_spec hP
      have hji : level j ≤ level i := by
        simpa only [hjlevel] using Nat.find_min' hP hPi
      have hsub : ball i ⊆ ball j := by
        rw [hball i, hball j]
        apply
          Matrix.skewAdjointPadicTranslatedUniformCoordinateBall_subset_of_le_of_nonempty_inter
            F p hji
        simpa only [hball i, hball j, Set.inter_comm] using hinter
      have hjselected : j ∈ selected := by
        refine ⟨hjt, ?_⟩
        intro q hqt hqlt
        rcases Set.disjoint_or_nonempty_inter (ball q) (ball j) with hdisj | hqj
        · exact hdisj
        · have hjq : ball j ⊆ ball q := by
            rw [hball j, hball q]
            apply
              Matrix.skewAdjointPadicTranslatedUniformCoordinateBall_subset_of_le_of_nonempty_inter
                F p (Nat.le_of_lt hqlt)
            simpa only [hball q, hball j] using hqj
          have hPq : P (level q) :=
            ⟨q, hqt, rfl, ⟨z, hzi, hjq (hsub hzi)⟩⟩
          have hjleq : level j ≤ level q := by
            simpa only [hjlevel] using Nat.find_min' hP hPq
          exact (not_lt_of_ge hjleq hqlt).elim
      exact Set.mem_sUnion.mpr
        ⟨ball j, ⟨j, hjselected, rfl⟩, hsub hzi⟩

local instance
    skewAdjointPadicCayleyTranslatedSourceOverlapCertifiedDisjointSourceBallIndexCountable
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.det ≠ 0)
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p]))) :
    Countable
      (skewAdjointPadicCayleyTranslatedSourceOverlapCertifiedDisjointSourceBallSet
        p n F hF c d) :=
  (skewAdjointPadicCayleyTranslatedSourceOverlapCertifiedDisjointSourceBallSet_spec
    p n F hF c d).1.to_subtype

/-- A chosen original certified center representing one disjoint source ball. -/
def skewAdjointPadicCayleyTranslatedSourceOverlapCertifiedDisjointRepresentative
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.det ≠ 0)
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p])))
    (B :
      skewAdjointPadicCayleyTranslatedSourceOverlapCertifiedDisjointSourceBallSet
        p n F hF c d) :
    {x // x ∈
      skewAdjointPadicCayleyTranslatedSourceOverlapAmbientSet
        p n F hF c d} :=
  Classical.choose
    ((skewAdjointPadicCayleyTranslatedSourceOverlapCertifiedDisjointSourceBallSet_spec
      p n F hF c d).2.2.1 B B.property)

theorem
    skewAdjointPadicCayleyTranslatedSourceOverlapCertifiedDisjointRepresentative_spec
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.det ≠ 0)
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p])))
    (B :
      skewAdjointPadicCayleyTranslatedSourceOverlapCertifiedDisjointSourceBallSet
        p n F hF c d) :
    skewAdjointPadicCayleyTranslatedSourceOverlapCertifiedDisjointRepresentative
        p n F hF c d B ∈
      skewAdjointPadicCayleyTranslatedSourceOverlapCertifiedSelectedCenterSet
        p n F hF c d ∧
    skewAdjointPadicCayleyTranslatedSourceOverlapCertifiedSourceBall
        p n F hF c d
        (skewAdjointPadicCayleyTranslatedSourceOverlapCertifiedDisjointRepresentative
          p n F hF c d B) =
      B :=
  Classical.choose_spec
    ((skewAdjointPadicCayleyTranslatedSourceOverlapCertifiedDisjointSourceBallSet_spec
      p n F hF c d).2.2.1 B B.property)

/-- The certified coordinate level retained by a disjoint source ball. -/
def skewAdjointPadicCayleyTranslatedSourceOverlapCertifiedDisjointLevel
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.det ≠ 0)
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p])))
    (B :
      skewAdjointPadicCayleyTranslatedSourceOverlapCertifiedDisjointSourceBallSet
        p n F hF c d) :
    ℕ :=
  skewAdjointPadicCayleyTranslatedSourceOverlapCertifiedLevel
    p n F hF c d
    (skewAdjointPadicCayleyTranslatedSourceOverlapCertifiedDisjointRepresentative
      p n F hF c d B)

/-- The exact target tangent coset retained by a disjoint source ball. -/
def skewAdjointPadicCayleyTranslatedSourceOverlapCertifiedDisjointTargetBall
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.det ≠ 0)
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p])))
    (B :
      skewAdjointPadicCayleyTranslatedSourceOverlapCertifiedDisjointSourceBallSet
        p n F hF c d) :
    Set (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  skewAdjointPadicCayleyTranslatedSourceOverlapCertifiedTargetBall
    p n F hF c d
    (skewAdjointPadicCayleyTranslatedSourceOverlapCertifiedDisjointRepresentative
      p n F hF c d B)

/-- Every disjoint source ball retains the local forward-weighted pushforward
of its chosen certified representative. -/
theorem
    map_skewAdjointPadicCayleyTranslatedSourceOverlapCertifiedDisjointSourceBall_withDensity_forwardJacobian
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.det ≠ 0)
    (c d : specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p])))
    (B :
      skewAdjointPadicCayleyTranslatedSourceOverlapCertifiedDisjointSourceBallSet
        p n F hF c d) :
    Measure.map
        (skewAdjointPadicCayleyTranslatedSourceOverlapAmbientMeasurableTransition
          p n F hF c d)
        (((Matrix.skewAdjointPadicCoordinateMeasure F p).restrict B).withDensity
          (skewAdjointPadicCayleyTranslatedSourceOverlapAmbientTransitionJacobian
            p n F hF c d)) =
      (Matrix.skewAdjointPadicCoordinateMeasure F p).restrict
        (skewAdjointPadicCayleyTranslatedSourceOverlapCertifiedDisjointTargetBall
          p n F hF c d B) := by
  rw [
    ←
      (skewAdjointPadicCayleyTranslatedSourceOverlapCertifiedDisjointRepresentative_spec
        p n F hF c d B).2]
  exact
    map_skewAdjointPadicCayleyTranslatedSourceOverlapCertifiedSourceBall_withDensity_forwardJacobian
      p n F hF c d
      (skewAdjointPadicCayleyTranslatedSourceOverlapCertifiedDisjointRepresentative
        p n F hF c d B)

end PositiveDefiniteIntegralLattice
