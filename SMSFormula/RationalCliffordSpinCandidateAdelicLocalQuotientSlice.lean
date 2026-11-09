import Mathlib.Topology.Covering.Quotient
import SMSFormula.RationalCliffordSpinCandidateAdelicLeftQuotientTopology

/-!
# Local slices for the rational adelic Spin quotient

The rational diagonal is discrete in the locally compact full-adelic Spin
candidate.  Mathlib's discrete-subgroup quotient theorem therefore applies to
the literal project-local left-coset map.  This file packages that map as a
quotient covering map, hence as a covering map and local homeomorphism.

This is a topological local-slice statement only.  It does not choose a global
measurable fundamental domain, prove a periodization identity, construct a
quotient measure, or impose an invariant-differential Tamagawa normalization.
-/

noncomputable section

open PositiveDefiniteIntegralLattice
open Set
open Topology

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

local instance : MulAction V.FullAdelicCliffordSpinCandidateGroup
    V.FullAdelicCliffordSpinCandidateGroup :=
  Monoid.toMulAction V.FullAdelicCliffordSpinCandidateGroup

local instance : MulAction
    V.rationalCliffordSpinCandidateFullAdelicDiagonalSubgroup
    V.FullAdelicCliffordSpinCandidateGroup :=
  Subgroup.instMulAction

/-- The existing rational left-coset map is a quotient covering map for left
multiplication by the rational diagonal. -/
theorem fullAdelicCliffordSpinCandidateLeftQuotientMap_isQuotientCoveringMap :
    IsQuotientCoveringMap
      V.fullAdelicCliffordSpinCandidateLeftQuotientMap
      V.rationalCliffordSpinCandidateFullAdelicDiagonalSubgroup := by
  exact
    V.fullAdelicCliffordSpinCandidateLeftQuotientMap_isQuotientMap
      |>.isQuotientCoveringMap_of_subgroup
        V.rationalCliffordSpinCandidateFullAdelicDiagonalSubgroup
        (SetLike.isDiscrete_iff_discreteTopology.mpr inferInstance)
        fun {_ _} =>
          V.fullAdelicCliffordSpinCandidateLeftQuotientMap_eq_iff _ _

/-- Every full-adelic point has a neighborhood whose nontrivial rational left
translates are disjoint from it. -/
theorem
    exists_fullAdelicCliffordSpinCandidateRationalDiagonalDisjointNeighborhood
    (x : V.FullAdelicCliffordSpinCandidateGroup) :
    ∃ U ∈ 𝓝 x,
      ∀ gamma : V.rationalCliffordSpinCandidateFullAdelicDiagonalSubgroup,
        (((fun y : V.FullAdelicCliffordSpinCandidateGroup =>
            (gamma : V.FullAdelicCliffordSpinCandidateGroup) * y) '' U) ∩ U).Nonempty →
          gamma = 1 := by
  simpa only [smul_eq_mul] using
    V.fullAdelicCliffordSpinCandidateLeftQuotientMap_isQuotientCoveringMap.disjoint x

/-- The rational left-coset map is a covering map. -/
theorem fullAdelicCliffordSpinCandidateLeftQuotientMap_isCoveringMap :
    IsCoveringMap V.fullAdelicCliffordSpinCandidateLeftQuotientMap :=
  V.fullAdelicCliffordSpinCandidateLeftQuotientMap_isQuotientCoveringMap.isCoveringMap

/-- The rational left-coset map is a local homeomorphism. -/
theorem fullAdelicCliffordSpinCandidateLeftQuotientMap_isLocalHomeomorph :
    IsLocalHomeomorph V.fullAdelicCliffordSpinCandidateLeftQuotientMap :=
  V.fullAdelicCliffordSpinCandidateLeftQuotientMap_isCoveringMap.isLocalHomeomorph

/-- Around every full-adelic point, restriction of the quotient map to an open
slice is an open embedding.  Equivalently, this restriction is a homeomorphism
onto its open image. -/
theorem
    exists_openSlice_fullAdelicCliffordSpinCandidateLeftQuotientMap
    (x : V.FullAdelicCliffordSpinCandidateGroup) :
    ∃ U : Set V.FullAdelicCliffordSpinCandidateGroup,
      IsOpen U ∧ x ∈ U ∧
        IsOpenEmbedding
          (U.restrict V.fullAdelicCliffordSpinCandidateLeftQuotientMap) := by
  obtain ⟨e, hxe, he⟩ :=
    V.fullAdelicCliffordSpinCandidateLeftQuotientMap_isLocalHomeomorph x
  refine ⟨e.source, e.open_source, hxe, ?_⟩
  rw [he]
  exact e.isOpenEmbedding_restrict

/-- Every full-adelic point belongs to an open slice homeomorphic, through the
quotient map, to its open image in the rational left quotient. -/
theorem
    exists_openSliceHomeomorph_fullAdelicCliffordSpinCandidateLeftQuotientMap
    (x : V.FullAdelicCliffordSpinCandidateGroup) :
    ∃ U : Set V.FullAdelicCliffordSpinCandidateGroup,
      IsOpen U ∧ x ∈ U ∧
        IsOpen
          (V.fullAdelicCliffordSpinCandidateLeftQuotientMap '' U) ∧
        Nonempty
          (U ≃ₜ
            V.fullAdelicCliffordSpinCandidateLeftQuotientMap '' U) := by
  obtain ⟨U, hU, hxU, hUemb⟩ :=
    V.exists_openSlice_fullAdelicCliffordSpinCandidateLeftQuotientMap x
  have hrange :
      Set.range
          (U.restrict V.fullAdelicCliffordSpinCandidateLeftQuotientMap) =
        V.fullAdelicCliffordSpinCandidateLeftQuotientMap '' U := by
    ext y
    simp [Set.range]
  refine ⟨U, hU, hxU, ?_, ⟨?_⟩⟩
  · rw [← hrange]
    exact hUemb.isOpen_range
  · exact
      hUemb.isEmbedding.toHomeomorph.trans
        (Homeomorph.setCongr hrange)

end RationalQuadraticSpaceMatrix
