import SMSFormula.SkewAdjointPadicCoordinateBallCompactness
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite

/-!
# Measure determination by deep p-adic coordinate balls

For any fixed lower level, the translated uniform coordinate balls at all
deeper levels still form a topological basis.  Their nonempty intersections
are again members of the family, so they form a π-system.  Second countability
provides a countable compact spanning subfamily.

Consequently, a locally finite Borel measure is determined by its values on
all sufficiently deep translated coordinate balls.
-/

noncomputable section

open MeasureTheory
open TopologicalSpace
open scoped Matrix Matrix.Norms.Operator Topology Pointwise

namespace Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

local instance skewAdjointPadicCoordinateBallDeterminationMeasurableSpace
    (F : Matrix ι ι ℚ) (p : ℕ) [Fact (Nat.Prime p)] :
    MeasurableSpace
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  borel _

local instance skewAdjointPadicCoordinateBallDeterminationBorelSpace
    (F : Matrix ι ι ℚ) (p : ℕ) [Fact (Nat.Prime p)] :
    BorelSpace
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  ⟨rfl⟩

local instance skewAdjointPadicCoordinateBallDeterminationSecondCountable
    (F : Matrix ι ι ℚ) (p : ℕ) [Fact (Nat.Prime p)] :
    SecondCountableTopology
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule := by
  letI : SecondCountableTopology (ι → ℚ_[p]) :=
    TopologicalSpace.instSecondCountableTopologyForallOfCountable
  letI : SecondCountableTopology (Matrix ι ι ℚ_[p]) :=
    TopologicalSpace.instSecondCountableTopologyForallOfCountable
  exact TopologicalSpace.secondCountableTopology_induced
    (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule
    (Matrix ι ι ℚ_[p])
    ((↑) : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule → Matrix ι ι ℚ_[p])

/-- The family of translated uniform coordinate balls whose level is at
least `k`. -/
def skewAdjointPadicDeepTranslatedUniformCoordinateBalls
    (F : Matrix ι ι ℚ) (p k : ℕ) [Fact (Nat.Prime p)] :
    Set (Set (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule) :=
  {B | ∃ l, k ≤ l ∧ ∃ x,
    B = skewAdjointPadicTranslatedUniformCoordinateBall F p l x}

/-- Arbitrarily deep translated coordinate balls remain a topological
basis. -/
theorem isTopologicalBasis_skewAdjointPadicDeepTranslatedUniformCoordinateBalls
    (F : Matrix ι ι ℚ) (p k : ℕ) [Fact (Nat.Prime p)] :
    IsTopologicalBasis
      (skewAdjointPadicDeepTranslatedUniformCoordinateBalls F p k) := by
  apply isTopologicalBasis_of_isOpen_of_nhds
  · rintro B ⟨l, -, x, rfl⟩
    exact
      (isClopen_skewAdjointPadicTranslatedUniformCoordinateBall
        F p l x).2
  · intro x U hx hU
    obtain ⟨l, hlU⟩ :=
      exists_skewAdjointPadicTranslatedUniformCoordinateBall_subset_of_mem_nhds
        F p x (hU.mem_nhds hx)
    let m := max k l
    refine
      ⟨skewAdjointPadicTranslatedUniformCoordinateBall F p m x,
        ⟨m, le_max_left _ _, x, rfl⟩,
        mem_skewAdjointPadicTranslatedUniformCoordinateBall_self F p m x,
        ?_⟩
    apply
      (skewAdjointPadicTranslatedUniformCoordinateBall_subset_of_le_of_mem
        F p (le_max_right k l)
        (mem_skewAdjointPadicTranslatedUniformCoordinateBall_self
          F p l x)).trans
    exact hlU

/-- Nonempty intersections of sufficiently deep translated coordinate balls
are again sufficiently deep translated coordinate balls. -/
theorem isPiSystem_skewAdjointPadicDeepTranslatedUniformCoordinateBalls
    (F : Matrix ι ι ℚ) (p k : ℕ) [Fact (Nat.Prime p)] :
    IsPiSystem
      (skewAdjointPadicDeepTranslatedUniformCoordinateBalls F p k) := by
  rintro B ⟨l, hkl, x, rfl⟩ C ⟨m, hkm, y, rfl⟩ hinter
  rcases le_total l m with hlm | hml
  · refine ⟨m, hkm, y, ?_⟩
    apply Set.inter_eq_right.mpr
    exact
      skewAdjointPadicTranslatedUniformCoordinateBall_subset_of_le_of_nonempty_inter
        F p hlm hinter
  · refine ⟨l, hkl, x, ?_⟩
    apply Set.inter_eq_left.mpr
    apply
      skewAdjointPadicTranslatedUniformCoordinateBall_subset_of_le_of_nonempty_inter
        F p hml
    simpa only [Set.inter_comm] using hinter

/-- The sufficiently deep coordinate-ball family admits a sequence of its
members covering the whole transported carrier. -/
theorem
    exists_sequence_skewAdjointPadicDeepTranslatedUniformCoordinateBalls_cover
    (F : Matrix ι ι ℚ) (p k : ℕ) [Fact (Nat.Prime p)] :
    ∃ B : ℕ → Set (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule,
      (∀ i,
        B i ∈ skewAdjointPadicDeepTranslatedUniformCoordinateBalls F p k) ∧
      ⋃ i, B i = Set.univ := by
  let C := skewAdjointPadicDeepTranslatedUniformCoordinateBalls F p k
  have hC :
      IsTopologicalBasis C :=
    isTopologicalBasis_skewAdjointPadicDeepTranslatedUniformCoordinateBalls
      F p k
  obtain ⟨S, hSC, hScount, hSbasis⟩ := hC.exists_countable
  have hnonempty : ∃ B, B ∈ C := by
    refine
      ⟨skewAdjointPadicTranslatedUniformCoordinateBall F p k 0,
        k, le_rfl, 0, rfl⟩
  apply
    (@Set.exists_seq_cover_iff_countable
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule
      (fun B => B ∈ C) hnonempty).2
  exact
    ⟨S, hScount, fun B hB => hSC hB, hSbasis.sUnion_eq⟩

/-- A Borel measure finite on compact sets is determined by its values on
every translated uniform coordinate ball beyond one fixed level. -/
theorem measure_eq_of_skewAdjointPadicTranslatedUniformCoordinateBall_eq
    (F : Matrix ι ι ℚ) (p k : ℕ) [Fact (Nat.Prime p)]
    (μ ν : Measure (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule)
    [IsFiniteMeasureOnCompacts μ]
    (hball : ∀ l, k ≤ l → ∀ x,
      μ (skewAdjointPadicTranslatedUniformCoordinateBall F p l x) =
        ν (skewAdjointPadicTranslatedUniformCoordinateBall F p l x)) :
    μ = ν := by
  let C := skewAdjointPadicDeepTranslatedUniformCoordinateBalls F p k
  obtain ⟨B, hBC, hBcover⟩ :=
    exists_sequence_skewAdjointPadicDeepTranslatedUniformCoordinateBalls_cover
      F p k
  apply Measure.ext_of_generateFrom_of_iUnion C B
  · exact
      BorelSpace.measurable_eq.trans
        (isTopologicalBasis_skewAdjointPadicDeepTranslatedUniformCoordinateBalls
          F p k).borel_eq_generateFrom
  · exact
      isPiSystem_skewAdjointPadicDeepTranslatedUniformCoordinateBalls F p k
  · exact hBcover
  · exact hBC
  · intro i
    obtain ⟨l, -, x, hBi⟩ := hBC i
    rw [hBi]
    exact
      (isCompact_skewAdjointPadicTranslatedUniformCoordinateBall
        F p l x).measure_ne_top
  · intro S hSC
    obtain ⟨l, hkl, x, rfl⟩ := hSC
    exact hball l hkl x

end Matrix
