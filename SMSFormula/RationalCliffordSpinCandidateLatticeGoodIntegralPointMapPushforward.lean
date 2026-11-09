import SMSFormula.RationalCliffordSpinCandidateLocalPointMapRestriction
import SMSFormula.RationalCliffordSpinCandidateIntegralSpinorNormUnitValued
import SMSFormula.RationalCliffordSpinCandidateRawDifferentialVolumeProductConvergence

/-!
# Good integral Spin pushforwards for the lattice comparison block

Outside the literal comparison bad set, the completed arithmetic inputs say
that the Spin and `SO` integral differential volumes agree and that the
integral Spin image has index two.  Combining the volume equality with the
ambient restriction formula identifies each normalized good Spin factor with
twice the normalized `SO` factor restricted to the actual integral image.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

set_option synthInstance.maxHeartbeats 500000
set_option maxHeartbeats 1600000

local instance latticeGoodIntegralPointMapHeightDecidableEq :
    DecidableEq (IsDedekindDomain.HeightOneSpectrum ℤ) := Classical.decEq _

local instance latticeGoodIntegralPointMapPrimeFact
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

local instance latticeGoodIntegralPointMapSOGroupMeasurableSpace
    (L : PositiveDefiniteIntegralLattice n) (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    MeasurableSpace
      (L.rationalQuadraticSpaceMatrix.HeightOnePadicSpecialOrthogonalGroup v) :=
  borel _

local instance latticeGoodIntegralPointMapSOGroupBorelSpace
    (L : PositiveDefiniteIntegralLattice n) (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    BorelSpace
      (L.rationalQuadraticSpaceMatrix.HeightOnePadicSpecialOrthogonalGroup v) :=
  ⟨rfl⟩

/-- The local integral volume comparison, with its internal
`r + 2` indexing hidden behind the natural rank hypothesis used downstream. -/
theorem
    heightOnePadicCliffordSpinCandidateIntegralVolume_eq_soIntegralVolume_of_rankAtLeastThree
    (L : PositiveDefiniteIntegralLattice n) (hn : 3 ≤ n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : L.rationalQuadraticSpaceMatrix.CliffordSpinCandidateAdmissibleIntegralPlace S)
    (hvRange : v.1 ∉
      L.rationalQuadraticSpaceMatrix.cliffordSpinCandidateOddUnimodularBadPlaces)
    (hvLift : v.1 ∉
      L.rationalQuadraticSpaceMatrix.cliffordSpinCandidateIntegralLiftingBadPlaces) :
    L.rationalQuadraticSpaceMatrix.heightOnePadicCliffordSpinCandidateChartGluedIntegralVolume
        v.1 =
      L.rationalQuadraticSpaceMatrix.heightOnePadicSpecialOrthogonalIntegralVolume
        v.1 := by
  obtain ⟨r, rfl⟩ : ∃ r, n = r + 2 := ⟨n - 2, by omega⟩
  exact
    L.heightOnePadicCliffordSpinCandidateIntegralVolume_eq_soIntegralVolume_of_not_mem_badPlaces
      S v hvRange hvLift

/-- Outside the same two arithmetic bad sets, the actual integral Spin image
has index two in the integral `SO` group. -/
theorem
    heightOnePadicCliffordSpinCandidateIntegralImageIndex_eq_two_of_rankAtLeastThree
    (L : PositiveDefiniteIntegralLattice n) (hn : 3 ≤ n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : L.rationalQuadraticSpaceMatrix.CliffordSpinCandidateAdmissibleIntegralPlace S)
    (hvRange : v.1 ∉
      L.rationalQuadraticSpaceMatrix.cliffordSpinCandidateOddUnimodularBadPlaces)
    (hvLift : v.1 ∉
      L.rationalQuadraticSpaceMatrix.cliffordSpinCandidateIntegralLiftingBadPlaces) :
    L.rationalQuadraticSpaceMatrix.heightOnePadicCliffordSpinCandidateIntegralImageIndex
        S v = 2 := by
  obtain ⟨r, rfl⟩ : ∃ r, n = r + 2 := ⟨n - 2, by omega⟩
  apply
    L.rationalQuadraticSpaceMatrix.heightOnePadicCliffordSpinCandidateIntegralImageIndex_eq_two_of_lifting_of_spinorRangeDegree_eq_two
  · exact
      L.rationalQuadraticSpaceMatrix.cliffordSpinCandidateIntegralLiftingAt_of_not_mem_badPlaces
        S v hvLift
  · exact
      L.heightOnePadicSpecialOrthogonalIntegralSpinorNormRangeDegree_eq_two_of_not_mem_badPlaces
        S v hvRange

/-- At a tail place for the common comparison block, all three explicit bad
sets are absent. -/
theorem cliffordSpinCandidateComparisonTail_not_mem_badPlaces
    (L : PositiveDefiniteIntegralLattice n)
    (v : L.rationalQuadraticSpaceMatrix.CliffordSpinCandidateAdmissibleIntegralPlace
      L.rationalQuadraticSpaceMatrix.cliffordSpinCandidateIntegralVolumeComparisonBadPlaces) :
    v.1 ∉ L.rationalQuadraticSpaceMatrix.cliffordSpinCandidateOddUnimodularBadPlaces ∧
      v.1 ∉ L.rationalQuadraticSpaceMatrix.cliffordSpinCandidateIntegralLiftingBadPlaces := by
  have hv : v.1 ∉
      L.rationalQuadraticSpaceMatrix.cliffordSpinCandidateIntegralVolumeComparisonBadPlaces := by
    intro hv
    exact v.2 (Finset.mem_union_left _ hv)
  have hvAll :
      v.1 ∉ L.rationalQuadraticSpaceMatrix.cliffordSpinCandidateAdmissibleBadPlaces ∧
        v.1 ∉ L.rationalQuadraticSpaceMatrix.cliffordSpinCandidateOddUnimodularBadPlaces ∧
          v.1 ∉ L.rationalQuadraticSpaceMatrix.cliffordSpinCandidateIntegralLiftingBadPlaces := by
    simpa [RationalQuadraticSpaceMatrix.cliffordSpinCandidateIntegralVolumeComparisonBadPlaces]
      using hv
  exact ⟨hvAll.2.1, hvAll.2.2⟩

end PositiveDefiniteIntegralLattice
