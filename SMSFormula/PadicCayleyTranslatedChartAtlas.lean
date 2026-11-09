import SMSFormula.PadicCayleyTranslatedChartTopology
import Mathlib.Topology.Compactness.Lindelof

/-!
# A countable disjoint translated p-adic Cayley atlas

Every point of the p-adic special-orthogonal group lies in the exact
translated Cayley target centered at that point.  The group inherits a
second-countable topology from the finite-dimensional matrix ambient space,
so a countable sequence of centers still covers the group.  Disjointizing
that sequence gives measurable, pairwise-disjoint atlas pieces, each
contained in its assigned translated target.

This module is purely topological and measurable.  It does not restrict,
transport, extend, or sum any differential chart measure.
-/

noncomputable section

open scoped Matrix

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

local instance padicCayleyTranslatedChartAtlasGroupMeasurableSpace
    (F : Matrix (Fin n) (Fin n) ℚ) (p : ℕ) [Fact (Nat.Prime p)] :
    MeasurableSpace
      (specialFormPreservingMatrixSubgroup
        (F.map (algebraMap ℚ ℚ_[p]))) :=
  borel _

local instance padicCayleyTranslatedChartAtlasGroupBorelSpace
    (F : Matrix (Fin n) (Fin n) ℚ) (p : ℕ) [Fact (Nat.Prime p)] :
    BorelSpace
      (specialFormPreservingMatrixSubgroup
        (F.map (algebraMap ℚ ℚ_[p]))) :=
  ⟨rfl⟩

/-- The p-adic special-orthogonal matrix group inherits a second-countable
topology from its finite-dimensional matrix ambient space. -/
theorem padicCayleySpecialOrthogonalGroup_secondCountable
    (F : Matrix (Fin n) (Fin n) ℚ) (p : ℕ) [Fact (Nat.Prime p)] :
    SecondCountableTopology
      (specialFormPreservingMatrixSubgroup
        (F.map (algebraMap ℚ ℚ_[p]))) := by
  letI : SecondCountableTopology (Fin n → ℚ_[p]) :=
    TopologicalSpace.instSecondCountableTopologyForallOfCountable
  letI : SecondCountableTopology (Matrix (Fin n) (Fin n) ℚ_[p]) :=
    TopologicalSpace.instSecondCountableTopologyForallOfCountable
  letI : SecondCountableTopology
      (Matrix (Fin n) (Fin n) ℚ_[p])ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  letI : SecondCountableTopology
      (Matrix (Fin n) (Fin n) ℚ_[p] ×
        (Matrix (Fin n) (Fin n) ℚ_[p])ᵐᵒᵖ) :=
    inferInstance
  letI : SecondCountableTopology
      (Matrix (Fin n) (Fin n) ℚ_[p])ˣ :=
    Units.isEmbedding_embedProduct.secondCountableTopology
  letI : SecondCountableTopology
      (formPreservingMatrixSubgroup
        (F.map (algebraMap ℚ ℚ_[p]))) :=
    TopologicalSpace.secondCountableTopology_induced _ _
      ((↑) : formPreservingMatrixSubgroup
          (F.map (algebraMap ℚ ℚ_[p])) →
        (Matrix (Fin n) (Fin n) ℚ_[p])ˣ)
  exact TopologicalSpace.secondCountableTopology_induced _ _
    ((↑) : specialFormPreservingMatrixSubgroup
        (F.map (algebraMap ℚ ℚ_[p])) →
      formPreservingMatrixSubgroup
        (F.map (algebraMap ℚ ℚ_[p])))

/-- All exact translated p-adic Cayley targets cover the full
special-orthogonal group. -/
theorem iUnion_padicCayleySpecialOrthogonalTranslatedTarget
    (F : Matrix (Fin n) (Fin n) ℚ) (p : ℕ) [Fact (Nat.Prime p)] :
    (⋃ c, padicCayleySpecialOrthogonalTranslatedTarget F p c) =
      Set.univ := by
  apply Set.eq_univ_of_forall
  intro c
  exact Set.mem_iUnion.2
    ⟨c, self_mem_padicCayleySpecialOrthogonalTranslatedTarget F p c⟩

/-- A countable sequence of centers whose exact translated p-adic Cayley
targets still cover the special-orthogonal group. -/
def padicCayleySpecialOrthogonalChartCoverCenter
    (F : Matrix (Fin n) (Fin n) ℚ) (p : ℕ) [Fact (Nat.Prime p)] :
    ℕ → specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p])) :=
  letI := padicCayleySpecialOrthogonalGroup_secondCountable F p
  Classical.choose
    (eq_open_union_nat
      (padicCayleySpecialOrthogonalTranslatedTarget F p)
      (isOpen_padicCayleySpecialOrthogonalTranslatedTarget F p))

/-- The selected countable translated p-adic Cayley atlas covers the full
special-orthogonal group. -/
theorem iUnion_padicCayleySpecialOrthogonalChartCoverCenter_target
    (F : Matrix (Fin n) (Fin n) ℚ) (p : ℕ) [Fact (Nat.Prime p)] :
    (⋃ k, padicCayleySpecialOrthogonalTranslatedTarget F p
      (padicCayleySpecialOrthogonalChartCoverCenter F p k)) =
      Set.univ := by
  letI := padicCayleySpecialOrthogonalGroup_secondCountable F p
  have hcover := Classical.choose_spec
    (eq_open_union_nat
      (padicCayleySpecialOrthogonalTranslatedTarget F p)
      (isOpen_padicCayleySpecialOrthogonalTranslatedTarget F p))
  change (⋃ k, padicCayleySpecialOrthogonalTranslatedTarget F p
    (Classical.choose
      (eq_open_union_nat
        (padicCayleySpecialOrthogonalTranslatedTarget F p)
        (isOpen_padicCayleySpecialOrthogonalTranslatedTarget F p)) k)) =
      Set.univ
  exact hcover.trans
    (iUnion_padicCayleySpecialOrthogonalTranslatedTarget F p)

/-- The measurable disjoint atlas piece assigned to the `k`-th selected
translated p-adic Cayley target. -/
def padicCayleySpecialOrthogonalChartCoverPiece
    (F : Matrix (Fin n) (Fin n) ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (k : ℕ) :
    Set (specialFormPreservingMatrixSubgroup
      (F.map (algebraMap ℚ ℚ_[p]))) :=
  disjointed
    (fun j => padicCayleySpecialOrthogonalTranslatedTarget F p
      (padicCayleySpecialOrthogonalChartCoverCenter F p j)) k

/-- Every disjoint translated p-adic Cayley atlas piece is measurable. -/
theorem measurableSet_padicCayleySpecialOrthogonalChartCoverPiece
    (F : Matrix (Fin n) (Fin n) ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (k : ℕ) :
    MeasurableSet
      (padicCayleySpecialOrthogonalChartCoverPiece F p k) := by
  apply MeasurableSet.disjointed
  intro j
  exact (isOpen_padicCayleySpecialOrthogonalTranslatedTarget F p
    (padicCayleySpecialOrthogonalChartCoverCenter F p j)).measurableSet

/-- Each disjoint atlas piece remains inside its assigned translated p-adic
Cayley target. -/
theorem padicCayleySpecialOrthogonalChartCoverPiece_subset_target
    (F : Matrix (Fin n) (Fin n) ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (k : ℕ) :
    padicCayleySpecialOrthogonalChartCoverPiece F p k ⊆
      padicCayleySpecialOrthogonalTranslatedTarget F p
        (padicCayleySpecialOrthogonalChartCoverCenter F p k) :=
  disjointed_subset _ _

/-- The disjoint translated p-adic Cayley atlas pieces are pairwise
disjoint. -/
theorem pairwiseDisjoint_padicCayleySpecialOrthogonalChartCoverPiece
    (F : Matrix (Fin n) (Fin n) ℚ) (p : ℕ) [Fact (Nat.Prime p)] :
    Pairwise (Function.onFun Disjoint
      (padicCayleySpecialOrthogonalChartCoverPiece F p)) := by
  exact disjoint_disjointed
    (fun j => padicCayleySpecialOrthogonalTranslatedTarget F p
      (padicCayleySpecialOrthogonalChartCoverCenter F p j))

/-- The disjoint translated p-adic Cayley atlas pieces cover the full
special-orthogonal group. -/
theorem iUnion_padicCayleySpecialOrthogonalChartCoverPiece
    (F : Matrix (Fin n) (Fin n) ℚ) (p : ℕ) [Fact (Nat.Prime p)] :
    (⋃ k, padicCayleySpecialOrthogonalChartCoverPiece F p k) =
      Set.univ := by
  change (⋃ k, disjointed
    (fun j => padicCayleySpecialOrthogonalTranslatedTarget F p
      (padicCayleySpecialOrthogonalChartCoverCenter F p j)) k) =
      Set.univ
  rw [iUnion_disjointed,
    iUnion_padicCayleySpecialOrthogonalChartCoverCenter_target]

end PositiveDefiniteIntegralLattice
