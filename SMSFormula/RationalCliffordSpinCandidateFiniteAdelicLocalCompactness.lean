import SMSFormula.RationalCliffordSpinCandidateLocalCompactnessPrecursor

/-!
# Local compactness of finite-adelic Clifford--Spin candidate points

For a fixed admissible block, only finitely many local factors are the full
p-adic candidate group; all remaining factors are compact integral subgroups.
This file proves local compactness of that mixed dependent product directly
from compact product neighborhoods, transports it to the genuine open
finite-adelic block, and then uses group translations to obtain local
compactness of the full finite-adelic candidate group.

No Haar or quotient measure is constructed here.
-/

noncomputable section

open PositiveDefiniteIntegralLattice
open Set Filter Topology

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1200000

local instance finiteAdelicSpinLocalCompactnessDecidableEq :
    DecidableEq (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  Classical.decEq _

/-! ## The finite-exceptional/compact-tail mixed product -/

/-- The mixed product of a fixed admissible principal block is locally
compact: only the normalized finite exceptional set needs nontrivial compact
neighborhoods, while the other factors may use their compact whole space. -/
noncomputable def
    finiteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlockLocallyCompactSpace
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    LocallyCompactSpace
      (V.FiniteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlock S) := by
  classical
  constructor
  intro t U hU
  rw [nhds_pi, Filter.mem_pi] at hU
  obtain ⟨I, hI, U', hU', hIU⟩ := hU
  choose K hKn hKU hKc using fun v =>
    LocallyCompactSpace.local_compact_nhds (t v) (U' v) (hU' v)
  let J : Set (IsDedekindDomain.HeightOneSpectrum ℤ) :=
    I ∪ (V.cliffordSpinCandidateAdmissibleExceptionalPlaces S : Set _)
  have hJ : J.Finite :=
    hI.union (V.cliffordSpinCandidateAdmissibleExceptionalPlaces S).finite_toSet
  refine ⟨J.pi K, ?_, ?_, ?_⟩
  · exact (set_pi_mem_nhds_iff hJ t).2 fun v hv => by
      exact hKn v
  · exact Set.Subset.trans
      (fun x hx v hv => hKU v (hx v (Or.inl hv))) hIU
  · rw [← Set.univ_pi_ite]
    refine isCompact_univ_pi fun v => ?_
    by_cases hv : v ∈ J
    · rw [if_pos hv]
      exact hKc v
    · rw [if_neg hv]
      have hvExceptional :
          v ∉ V.cliffordSpinCandidateAdmissibleExceptionalPlaces S := by
        intro hv'
        exact hv (Or.inr hv')
      letI : CompactSpace
          (V.FiniteAdelicCliffordSpinCandidateAdmissiblePrincipalBlockLocalFactor
            S v) :=
        V.finiteAdelicCliffordSpinCandidateAdmissiblePrincipalBlockLocalFactorCompactSpace
          S v hvExceptional
      exact isCompact_univ

/-- The genuine finite-adelic fixed block inherits local compactness from its
continuous equivalence with the mixed local product. -/
noncomputable def
    finiteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlockLocallyCompactSpace
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    LocallyCompactSpace
      (V.FiniteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlock S) := by
  letI : LocallyCompactSpace
      (V.FiniteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlock S) :=
    V.finiteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlockLocallyCompactSpace S
  exact
    (V.finiteAdelicCliffordSpinCandidateGenuineAdmissibleBlockHomeomorph S)
      |>.isOpenEmbedding.locallyCompactSpace

/-! ## The full finite-adelic carrier -/

/-- The full finite-adelic candidate group is locally compact.  A fixed
genuine admissible block is an open locally compact subgroup; translating its
compact neighborhoods supplies compact neighborhoods at every ambient point.
-/
noncomputable instance finiteAdelicCliffordSpinCandidateGroupLocallyCompactSpace :
    LocallyCompactSpace V.FiniteAdelicCliffordSpinCandidateGroup := by
  let H :=
    V.finiteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlockSubgroup ∅
  letI : LocallyCompactSpace H :=
    V.finiteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlockLocallyCompactSpace
      ∅
  constructor
  intro x U hU
  let f : H → V.FiniteAdelicCliffordSpinCandidateGroup :=
    fun h => x * h.1
  have hfContinuous : Continuous f :=
    continuous_const.mul continuous_subtype_val
  have hHOpen : IsOpen (H : Set V.FiniteAdelicCliffordSpinCandidateGroup) := by
    exact V.isOpen_finiteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlock ∅
  have hfOpen : IsOpenMap f := by
    exact (isOpenMap_mul_left x).comp
      hHOpen.isOpenEmbedding_subtypeVal.isOpenMap
  have hpreimage : f ⁻¹' U ∈ 𝓝 (1 : H) := by
    apply hfContinuous.continuousAt
    simpa [f] using hU
  obtain ⟨K, hKn, hKU, hKc⟩ := local_compact_nhds hpreimage
  refine ⟨f '' K, ?_, Set.image_subset_iff.2 hKU, hKc.image hfContinuous⟩
  have hfn : f '' K ∈ 𝓝 (f 1) := hfOpen.image_mem_nhds hKn
  simpa [f] using hfn

/-! ## Real and full-adelic carriers -/

/-- The real candidate group is locally compact through the same closed
finite-coordinate realization. -/
noncomputable instance realCliffordSpinCandidateGroupLocallyCompactSpace :
    LocallyCompactSpace V.RealCliffordSpinCandidateGroup := by
  letI : LocallyCompactSpace (Finset (Fin n) → ℝ) :=
    Pi.locallyCompactSpace_of_finite
  letI : LocallyCompactSpace (Matrix (Fin n) (Fin n) ℝ) :=
    Pi.locallyCompactSpace_of_finite
  change LocallyCompactSpace (V.CliffordSpinCandidateGroup ℝ)
  exact
    (V.cliffordSpinCandidatePointCoordinateMap_isClosedEmbedding ℝ)
      |>.locallyCompactSpace

/-- The full-adelic candidate group is locally compact by its completed
continuous real/finite product splitting. -/
noncomputable instance fullAdelicCliffordSpinCandidateGroupLocallyCompactSpace :
    LocallyCompactSpace V.FullAdelicCliffordSpinCandidateGroup := by
  exact
    V.fullAdelicCliffordSpinCandidateGroupRealFiniteContinuousEquiv
      |>.isOpenEmbedding.locallyCompactSpace

end RationalQuadraticSpaceMatrix
