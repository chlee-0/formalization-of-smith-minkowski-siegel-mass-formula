import SMSFormula.RationalCliffordGeneralSpinVerticalFiberCompactFinite

/-!
# Properness of the neutral Spin quotient inside the rational GSpin quotient

The represented rational adelic Spin quotient embeds topologically as the
neutral similitude fiber of the rational adelic `GSpin` quotient.  The key
point is local and uses no section: shrink an ambient `GSpin` open set by the
idele identity neighborhood which meets the rational idele diagonal only at
one.  Any representative of a neutral quotient point in that shrunken set
then has literal similitude one and therefore comes from intrinsic Spin.

Thus the quotient inclusion is an embedding.  In lattice rank at least three,
the already proved rational exactness identifies its range with the closed
neutral fiber, making it a closed embedding and hence a proper map.  This
closes the last geometric input in vertical compact-finiteness.
-/

noncomputable section

open PositiveDefiniteIntegralLattice
open Set
open Topology

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

/-- The quotient Spin inclusion with its codomain restricted to its literal
range. -/
def fullAdelicCliffordSpinCandidateLeftQuotientEquivRangeTarget
    (z : V.FullAdelicCliffordSpinCandidateLeftQuotient) :
    Set.range V.fullAdelicCliffordSpinCandidateLeftQuotientToGeneralSpin :=
  ⟨V.fullAdelicCliffordSpinCandidateLeftQuotientToGeneralSpin z, ⟨z, rfl⟩⟩

theorem continuous_fullAdelicCliffordSpinCandidateLeftQuotientEquivRangeTarget :
    Continuous V.fullAdelicCliffordSpinCandidateLeftQuotientEquivRangeTarget :=
  V.continuous_fullAdelicCliffordSpinCandidateLeftQuotientToGeneralSpin.subtype_mk _

theorem fullAdelicCliffordSpinCandidateLeftQuotientEquivRangeTarget_bijective :
    Function.Bijective
      V.fullAdelicCliffordSpinCandidateLeftQuotientEquivRangeTarget := by
  constructor
  · intro x y hxy
    apply V.fullAdelicCliffordSpinCandidateLeftQuotientToGeneralSpin_injective
    exact congrArg Subtype.val hxy
  · rintro ⟨z, x, rfl⟩
    exact ⟨x, rfl⟩

set_option synthInstance.maxHeartbeats 700000
set_option maxHeartbeats 2200000

/-- The Spin quotient topology is exactly the subspace topology inherited
from its range in the rational adelic `GSpin` quotient. -/
theorem fullAdelicCliffordSpinCandidateLeftQuotientEquivRangeTarget_isOpenMap :
    IsOpenMap
      V.fullAdelicCliffordSpinCandidateLeftQuotientEquivRangeTarget := by
  let i := V.fullAdelicCliffordSpinCandidateToGeneralSpinHom
  let qS := V.fullAdelicCliffordSpinCandidateLeftQuotientMap
  let qG := V.fullAdelicCliffordGeneralSpinLeftQuotientMap
  let J := V.fullAdelicCliffordSpinCandidateLeftQuotientToGeneralSpin
  let JR := V.fullAdelicCliffordSpinCandidateLeftQuotientEquivRangeTarget
  let nu := V.fullAdelicCliffordGeneralSpinSimilitudeHom
  intro U hU
  have hpreOpen : IsOpen (qS ⁻¹' U) :=
    hU.preimage V.fullAdelicCliffordSpinCandidateLeftQuotientMap_isQuotientMap.continuous
  obtain ⟨O, hOopen, hOi⟩ :=
    (V.cliffordSpinCandidateToCliffordGeneralSpinHom_isEmbedding RationalAdele
      |>.isInducing.isOpen_iff).mp hpreOpen
  let W : Set V.FullAdelicCliffordGeneralSpinGroup :=
    O ∩ nu ⁻¹' rationalIdeleRationalDiagonalIdentityNeighborhood
  have hWopen : IsOpen W := by
    exact hOopen.inter
      (isOpen_rationalIdeleRationalDiagonalIdentityNeighborhood.preimage
        V.continuous_fullAdelicCliffordGeneralSpinSimilitudeHom)
  have hqWopen : IsOpen (qG '' W) :=
    V.fullAdelicCliffordGeneralSpinLeftQuotientMap_isOpenMap W hWopen
  have hset : JR '' U = Subtype.val ⁻¹' (qG '' W) := by
    ext z
    rcases z with ⟨z, hz⟩
    rcases hz with ⟨x, rfl⟩
    constructor
    · rintro ⟨y, hyU, hy⟩
      have hyx : y = x :=
        V.fullAdelicCliffordSpinCandidateLeftQuotientEquivRangeTarget_bijective.1
          hy
      subst y
      induction x using Quot.inductionOn with
      | _ s =>
        refine ⟨i s, ?_, rfl⟩
        constructor
        · have hsU : s ∈ qS ⁻¹' U := hyU
          rw [← hOi] at hsU
          exact hsU
        · change nu (i s) ∈ rationalIdeleRationalDiagonalIdentityNeighborhood
          rw [show nu (i s) = 1 by
            have hsKer : i s ∈
                (CliffordGeneralSpinIntrinsicPoint.similitudeGroupHom
                  V RationalAdele).ker := by
              rw [← V.range_cliffordSpinCandidateToCliffordGeneralSpinHom_eq_ker
                RationalAdele]
              exact ⟨s, rfl⟩
            exact hsKer]
          rw [← rationalUnitFullAdelicDiagonalHom.map_one]
          exact
            (rationalUnitFullAdelicDiagonalHom_mem_identityNeighborhood_iff 1).mpr rfl
    · rintro ⟨g, ⟨hgO, hgN⟩, hgq⟩
      have hclass :
          QuotientGroup.mk' rationalIdeleDiagonalSubgroup (nu g) = 1 := by
        rw [← V.fullAdelicCliffordGeneralSpinLeftQuotientToIdeleClass_mk]
        change V.fullAdelicCliffordGeneralSpinLeftQuotientToIdeleClass (qG g) = 1
        rw [hgq]
        induction x using Quot.inductionOn with
        | _ s =>
          exact V.fullAdelicCliffordSpinCandidateLeftQuotientToGeneralSpin_neutral s
      have hdiag : nu g ∈ rationalIdeleDiagonalSubgroup :=
        (QuotientGroup.eq_one_iff _).mp hclass
      rcases hdiag with ⟨a, ha⟩
      have haone : a = 1 :=
        (rationalUnitFullAdelicDiagonalHom_mem_identityNeighborhood_iff a).mp
          (by rw [ha]; exact hgN)
      have hnug : nu g = 1 := by
        rw [← ha, haone, map_one]
      have hgker : g ∈
          (CliffordGeneralSpinIntrinsicPoint.similitudeGroupHom
            V RationalAdele).ker := by
        exact hnug
      rw [← V.range_cliffordSpinCandidateToCliffordGeneralSpinHom_eq_ker
        RationalAdele] at hgker
      rcases hgker with ⟨s, hs⟩
      have hsU : qS s ∈ U := by
        have hsO : i s ∈ O := by
          change V.cliffordSpinCandidateToCliffordGeneralSpinHom RationalAdele s ∈ O
          rw [hs]
          exact hgO
        have hsO' : s ∈
            (V.cliffordSpinCandidateToCliffordGeneralSpinHom RationalAdele) ⁻¹' O := hsO
        rw [hOi] at hsO'
        exact hsO'
      refine ⟨qS s, hsU, ?_⟩
      apply Subtype.ext
      change J (qS s) = J x
      change qG
        (V.cliffordSpinCandidateToCliffordGeneralSpinHom RationalAdele s) = J x
      rw [hs]
      exact hgq
  rw [hset]
  exact hqWopen.preimage continuous_subtype_val

/-- The induced map from the rational Spin quotient is a topological
embedding into the rational `GSpin` quotient. -/
theorem fullAdelicCliffordSpinCandidateLeftQuotientToGeneralSpin_isEmbedding :
    IsEmbedding V.fullAdelicCliffordSpinCandidateLeftQuotientToGeneralSpin := by
  have hRangeOpen : IsOpenEmbedding
      V.fullAdelicCliffordSpinCandidateLeftQuotientEquivRangeTarget :=
    IsOpenEmbedding.of_continuous_injective_isOpenMap
      V.continuous_fullAdelicCliffordSpinCandidateLeftQuotientEquivRangeTarget
      V.fullAdelicCliffordSpinCandidateLeftQuotientEquivRangeTarget_bijective.1
      V.fullAdelicCliffordSpinCandidateLeftQuotientEquivRangeTarget_isOpenMap
  have hcomp :
      ((fun z : Set.range
          V.fullAdelicCliffordSpinCandidateLeftQuotientToGeneralSpin => z.1) ∘
        V.fullAdelicCliffordSpinCandidateLeftQuotientEquivRangeTarget) =
          V.fullAdelicCliffordSpinCandidateLeftQuotientToGeneralSpin := rfl
  rw [← hcomp]
  exact IsEmbedding.subtypeVal.comp hRangeOpen.isEmbedding

end RationalQuadraticSpaceMatrix

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- In rank at least three, the Spin quotient range is the closed neutral
similitude fiber in the rational adelic `GSpin` quotient. -/
theorem isClosed_range_fullAdelicCliffordSpinCandidateLeftQuotientToGeneralSpin
    (L : PositiveDefiniteIntegralLattice n) (hn : 3 ≤ n) :
    IsClosed (Set.range
      L.rationalQuadraticSpaceMatrix.fullAdelicCliffordSpinCandidateLeftQuotientToGeneralSpin) := by
  let V := L.rationalQuadraticSpaceMatrix
  have hrange :
      Set.range V.fullAdelicCliffordSpinCandidateLeftQuotientToGeneralSpin =
        V.fullAdelicCliffordGeneralSpinLeftQuotientToIdeleClass ⁻¹' ({1} : Set _) := by
    ext z
    rw [L.mem_range_fullAdelicCliffordSpinCandidateLeftQuotientToGeneralSpin_iff_of_rankAtLeastThree
      hn]
    exact Set.mem_preimage.trans Set.mem_singleton_iff
  rw [hrange]
  exact isClosed_singleton.preimage
    V.continuous_fullAdelicCliffordGeneralSpinLeftQuotientToIdeleClass

/-- The rational Spin quotient is a closed embedded neutral fiber of the
rational adelic `GSpin` quotient. -/
theorem fullAdelicCliffordSpinCandidateLeftQuotientToGeneralSpin_isClosedEmbedding
    (L : PositiveDefiniteIntegralLattice n) (hn : 3 ≤ n) :
    IsClosedEmbedding
      L.rationalQuadraticSpaceMatrix.fullAdelicCliffordSpinCandidateLeftQuotientToGeneralSpin :=
  ⟨L.rationalQuadraticSpaceMatrix
      |>.fullAdelicCliffordSpinCandidateLeftQuotientToGeneralSpin_isEmbedding,
    L.isClosed_range_fullAdelicCliffordSpinCandidateLeftQuotientToGeneralSpin hn⟩

/-- The properness input needed for vertical compact-finiteness holds
for every lattice of rank at least three. -/
theorem hasProperSpinQuotientEmbedding
    (L : PositiveDefiniteIntegralLattice n) (hn : 3 ≤ n) :
    RationalQuadraticSpaceMatrix.CliffordSpinCandidateRawOnoTamagawaData.HasProperSpinQuotientEmbedding
      L.rationalQuadraticSpaceMatrix :=
  (L.fullAdelicCliffordSpinCandidateLeftQuotientToGeneralSpin_isClosedEmbedding hn).isProperMap

end PositiveDefiniteIntegralLattice

namespace RationalQuadraticSpaceMatrix.CliffordSpinCandidateRawOnoTamagawaData

variable {n : ℕ}

/-- Every translated vertical Spin fiber is unconditionally finite on compact
sets in lattice rank at least three. -/
theorem verticalSpinFiberMeasure_isFiniteMeasureOnCompacts
    (L : PositiveDefiniteIntegralLattice n) (hn : 3 ≤ n)
    (D : L.rationalQuadraticSpaceMatrix.CliffordSpinCandidateRawOnoTamagawaData)
    (hsurj : Function.Surjective
      L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinLeftQuotientToIdeleClass)
    (c : RationalIdeleClassGroup) :
    MeasureTheory.IsFiniteMeasureOnCompacts
      (D.verticalSpinFiberMeasure L.rationalQuadraticSpaceMatrix hsurj c) :=
  D.verticalSpinFiberMeasure_isFiniteMeasureOnCompacts_of_proper
    (L.hasProperSpinQuotientEmbedding hn) hsurj c

/-- Every descended vertical kernel value is unconditionally finite on
compact sets. -/
theorem verticalSpinFiberKernelAtIdeleClass_apply_isFiniteMeasureOnCompacts
    (L : PositiveDefiniteIntegralLattice n) (hn : 3 ≤ n)
    (D : L.rationalQuadraticSpaceMatrix.CliffordSpinCandidateRawOnoTamagawaData)
    (hsurj : Function.Surjective
      L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinLeftQuotientToIdeleClass)
    (c : RationalIdeleClassGroup) :
    MeasureTheory.IsFiniteMeasureOnCompacts
      (D.verticalSpinFiberKernelAtIdeleClass L hn hsurj c) :=
  D.verticalSpinFiberKernelAtIdeleClass_apply_isFiniteMeasureOnCompacts_of_proper
    L hn (L.hasProperSpinQuotientEmbedding hn) hsurj c

/-- The section-free common compact cover exists unconditionally. -/
theorem hasUniformFiniteVerticalFiberCover
    (L : PositiveDefiniteIntegralLattice n) (hn : 3 ≤ n)
    (D : L.rationalQuadraticSpaceMatrix.CliffordSpinCandidateRawOnoTamagawaData)
    (hsurj : Function.Surjective
      L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinLeftQuotientToIdeleClass) :
    D.HasUniformFiniteVerticalFiberCover L hn hsurj :=
  D.hasUniformFiniteVerticalFiberCover_of_proper
    L hn (L.hasProperSpinQuotientEmbedding hn) hsurj

/-- The vertical class-Haar bind is unconditionally sigma-finite. -/
theorem verticalSpinFiberHaarBoundMeasure_sigmaFinite
    (L : PositiveDefiniteIntegralLattice n) (hn : 3 ≤ n)
    (D : L.rationalQuadraticSpaceMatrix.CliffordSpinCandidateRawOnoTamagawaData)
    (hsurj : Function.Surjective
      L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinLeftQuotientToIdeleClass) :
    MeasureTheory.SigmaFinite
      (D.verticalSpinFiberHaarBoundMeasure L hn hsurj) :=
  D.verticalSpinFiberHaarBoundMeasure_sigmaFinite_of_proper
    L hn (L.hasProperSpinQuotientEmbedding hn) hsurj

/-- The exact ambient periodization of the vertical bind is unconditionally
sigma-finite. -/
theorem periodizedVerticalSpinFiberHaarBoundMeasure_sigmaFinite
    (L : PositiveDefiniteIntegralLattice n) (hn : 3 ≤ n)
    (D : L.rationalQuadraticSpaceMatrix.CliffordSpinCandidateRawOnoTamagawaData)
    (hsurj : Function.Surjective
      L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinLeftQuotientToIdeleClass) :
    MeasureTheory.SigmaFinite
      (L.rationalQuadraticSpaceMatrix.fullAdelicCliffordGeneralSpinPeriodizedQuotientLift
        (D.verticalSpinFiberHaarBoundMeasure L hn hsurj)) :=
  D.periodizedVerticalSpinFiberHaarBoundMeasure_sigmaFinite_of_proper
    L hn (L.hasProperSpinQuotientEmbedding hn) hsurj

end RationalQuadraticSpaceMatrix.CliffordSpinCandidateRawOnoTamagawaData
