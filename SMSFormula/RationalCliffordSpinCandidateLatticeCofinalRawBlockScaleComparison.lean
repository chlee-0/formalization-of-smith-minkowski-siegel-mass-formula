import SMSFormula.RationalCliffordSpinCandidateLatticeExceptionalBadPlaceScalar
import SMSFormula.RationalCliffordSpinCandidateLatticeGoodIntegralPointMapPushforward
import SMSFormula.AdelicProperFinitePresentation
import SMSFormula.RationalCliffordSpinCandidateRawDifferentialVolumeProductConvergence
import SMSFormula.RationalSpecialOrthogonalFiniteAdelicGenuinePrincipalBlockCarrier
import SMSFormula.RationalSpecialOrthogonalFiniteAdelicMixedPrincipalBlockSplit

/-!
# Raw Spin--SO comparison on cofinal lattice blocks

The original raw scalar comparison was proved on the fixed finite comparison
bad set.  Every place added beyond that set is a good place: the
integral Spin and `SO` differential volumes agree there.  Hence the Spin and
`SO` transition volumes from the comparison block to any larger block agree,
and the common raw block scalar propagates by coherent transition-volume
cancellation.

The final specialization uses the common proper-representative block.  This
is the numerical measure-compatibility part of enlarging the block; it adds no
new scale and does not compare singular limits.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

set_option synthInstance.maxHeartbeats 500000
set_option maxHeartbeats 1800000

local instance cofinalRawBlockScaleComparisonDecidableEq :
    DecidableEq (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  Classical.decEq _

local instance cofinalRawBlockScaleComparisonPrimeFact
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

local instance cofinalRawBlockScaleComparisonSOGroupMeasurableSpace
    (L : PositiveDefiniteIntegralLattice n) (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    MeasurableSpace
      (L.rationalQuadraticSpaceMatrix.HeightOnePadicSpecialOrthogonalGroup v) :=
  borel _

local instance cofinalRawBlockScaleComparisonSOGroupBorelSpace
    (L : PositiveDefiniteIntegralLattice n) (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    BorelSpace
      (L.rationalQuadraticSpaceMatrix.HeightOnePadicSpecialOrthogonalGroup v) :=
  ⟨rfl⟩

private theorem admissibleExceptionalPlaces_eq_of_comparisonBadPlaces_subset
    (L : PositiveDefiniteIntegralLattice n)
    (T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hST :
      L.rationalQuadraticSpaceMatrix.cliffordSpinCandidateIntegralVolumeComparisonBadPlaces ⊆
        T) :
    L.rationalQuadraticSpaceMatrix.cliffordSpinCandidateAdmissibleExceptionalPlaces
        T = T := by
  let V := L.rationalQuadraticSpaceMatrix
  ext v
  simp only [RationalQuadraticSpaceMatrix.cliffordSpinCandidateAdmissibleExceptionalPlaces,
    Finset.mem_union]
  constructor
  · rintro (hv | hv)
    · exact hv
    · apply hST
      exact Finset.mem_union_left _ (Finset.mem_union_left _ hv)
  · exact fun hv => Or.inl hv

/-- Beyond the complete comparison bad set, the coherent Spin and `SO`
transition volumes are literally equal. -/
theorem
    finiteAdelicCliffordSpinCandidateAdmissibleTransitionVolume_eq_specialOrthogonal_of_comparisonBadPlaces_subset
    (L : PositiveDefiniteIntegralLattice n) (hn : 3 ≤ n)
    (T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hST :
      L.rationalQuadraticSpaceMatrix.cliffordSpinCandidateIntegralVolumeComparisonBadPlaces ⊆
        T) :
    L.rationalQuadraticSpaceMatrix.finiteAdelicCliffordSpinCandidateAdmissibleTransitionVolume
        L.rationalQuadraticSpaceMatrix.cliffordSpinCandidateIntegralVolumeComparisonBadPlaces
        T =
      L.rationalQuadraticSpaceMatrix.finiteAdelicSpecialOrthogonalTransitionVolume
        L.rationalQuadraticSpaceMatrix.cliffordSpinCandidateIntegralVolumeComparisonBadPlaces
        T := by
  let V := L.rationalQuadraticSpaceMatrix
  let S := V.cliffordSpinCandidateIntegralVolumeComparisonBadPlaces
  have hS : V.cliffordSpinCandidateAdmissibleExceptionalPlaces S = S :=
    V.cliffordSpinCandidateAdmissibleExceptionalPlaces_comparisonBadPlaces_eq
  have hT : V.cliffordSpinCandidateAdmissibleExceptionalPlaces T = T :=
    L.admissibleExceptionalPlaces_eq_of_comparisonBadPlaces_subset T hST
  rw [V.finiteAdelicCliffordSpinCandidateAdmissibleTransitionVolume_eq_prod_sdiff,
    V.finiteAdelicSpecialOrthogonalTransitionVolume_eq_prod_sdiff, hS, hT]
  apply Finset.prod_congr rfl
  intro v hv
  have hvS : v ∉ S := (Finset.mem_sdiff.mp hv).2
  have hvAdmissible :
      v ∉ V.cliffordSpinCandidateAdmissibleExceptionalPlaces S := by
    simpa only [hS] using hvS
  have hvRange : v ∉ V.cliffordSpinCandidateOddUnimodularBadPlaces := by
    intro h
    exact hvS (Finset.mem_union_left _ (Finset.mem_union_right _ h))
  have hvLift : v ∉ V.cliffordSpinCandidateIntegralLiftingBadPlaces := by
    intro h
    exact hvS (Finset.mem_union_right _ h)
  exact
    L.heightOnePadicCliffordSpinCandidateIntegralVolume_eq_soIntegralVolume_of_rankAtLeastThree
      hn S ⟨v, hvAdmissible⟩ hvRange hvLift

private theorem ennreal_eq_of_mul_eq_mul_right_finite
    {a b c : ℝ≥0∞} (hc0 : c ≠ 0) (hctop : c ≠ ⊤)
    (h : a * c = b * c) :
    a = b := by
  calc
    a = a * 1 := (mul_one a).symm
    _ = a * (c * c⁻¹) := by rw [ENNReal.mul_inv_cancel hc0 hctop]
    _ = (a * c) * c⁻¹ := by rw [mul_assoc]
    _ = (b * c) * c⁻¹ := by rw [h]
    _ = b * (c * c⁻¹) := by rw [mul_assoc]
    _ = b * 1 := by rw [ENNReal.mul_inv_cancel hc0 hctop]
    _ = b := mul_one b

/-- The raw Spin and `SO` block scalars remain equal on every enlargement of
the comparison bad set. -/
theorem
    cliffordSpinCandidateRawFiniteScaleOfLattice_mul_blockWeight_eq_soScale_mul_blockWeight_of_comparisonBadPlaces_subset
    (L : PositiveDefiniteIntegralLattice n) (hn : 3 ≤ n)
    {P : ℝ} (hP : 0 < P)
    (hconv : massLocalInverseProductTendsTo L P)
    (T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hST :
      L.rationalQuadraticSpaceMatrix.cliffordSpinCandidateIntegralVolumeComparisonBadPlaces ⊆
        T) :
    (cliffordSpinCandidateRawFiniteScaleOfLattice L hn hP hconv : ℝ≥0∞) *
        L.rationalQuadraticSpaceMatrix.finiteAdelicCliffordSpinCandidateAdmissibleBlockWeight
          T =
      L.localPadicSpecialOrthogonalDifferentialFiniteStabilizerVolume P *
        L.rationalQuadraticSpaceMatrix.finiteAdelicSpecialOrthogonalBlockWeight T := by
  let V := L.rationalQuadraticSpaceMatrix
  let S := V.cliffordSpinCandidateIntegralVolumeComparisonBadPlaces
  let c := V.finiteAdelicSpecialOrthogonalTransitionVolume S T
  apply ennreal_eq_of_mul_eq_mul_right_finite
    (V.finiteAdelicSpecialOrthogonalTransitionVolume_ne_zero S T)
    (V.finiteAdelicSpecialOrthogonalTransitionVolume_ne_top S T)
  have htransition :
      V.finiteAdelicCliffordSpinCandidateAdmissibleTransitionVolume S T = c :=
    L.finiteAdelicCliffordSpinCandidateAdmissibleTransitionVolume_eq_specialOrthogonal_of_comparisonBadPlaces_subset
      hn T hST
  calc
    ((cliffordSpinCandidateRawFiniteScaleOfLattice L hn hP hconv : ℝ≥0∞) *
          V.finiteAdelicCliffordSpinCandidateAdmissibleBlockWeight T) * c =
        (cliffordSpinCandidateRawFiniteScaleOfLattice L hn hP hconv : ℝ≥0∞) *
          (V.finiteAdelicCliffordSpinCandidateAdmissibleBlockWeight T *
            V.finiteAdelicCliffordSpinCandidateAdmissibleTransitionVolume S T) := by
      rw [htransition]
      exact mul_assoc _ _ _
    _ = (cliffordSpinCandidateRawFiniteScaleOfLattice L hn hP hconv : ℝ≥0∞) *
          V.finiteAdelicCliffordSpinCandidateAdmissibleBlockWeight S := by
      rw [V.finiteAdelicCliffordSpinCandidateAdmissibleBlockWeight_mul_transitionVolume
        S T hST]
    _ = L.localPadicSpecialOrthogonalDifferentialFiniteStabilizerVolume P *
          V.finiteAdelicSpecialOrthogonalBlockWeight S :=
      L.cliffordSpinCandidateRawFiniteScaleOfLattice_mul_comparisonBlockWeight_eq_soScale_mul_blockWeight
        hn hP hconv
    _ = (L.localPadicSpecialOrthogonalDifferentialFiniteStabilizerVolume P *
          V.finiteAdelicSpecialOrthogonalBlockWeight T) * c := by
      rw [mul_assoc,
        V.finiteAdelicSpecialOrthogonalBlockWeight_mul_transitionVolume S T hST]

/-- Datum-facing form of raw scalar compatibility on every cofinal block. -/
theorem
    cliffordSpinCandidateRawOnoTamagawaDataOfLattice_spinScale_mul_blockWeight_eq_soScale_mul_blockWeight_of_comparisonBadPlaces_subset
    (L : PositiveDefiniteIntegralLattice n) [Nonempty (Fin n)] (hn : 3 ≤ n)
    (inst : Fintype L.ConcreteProperRationalDoubleCosetSet)
    {P : ℝ} (hP : 0 < P)
    (hconv : massLocalInverseProductTendsTo L P)
    (T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hST :
      L.rationalQuadraticSpaceMatrix.cliffordSpinCandidateIntegralVolumeComparisonBadPlaces ⊆
        T) :
    ((cliffordSpinCandidateRawOnoTamagawaDataOfLattice
          L hn inst hP hconv).spinFiniteScale : ℝ≥0∞) *
        L.rationalQuadraticSpaceMatrix.finiteAdelicCliffordSpinCandidateAdmissibleBlockWeight
          T =
      (cliffordSpinCandidateRawOnoTamagawaDataOfLattice
          L hn inst hP hconv).specialOrthogonalFiniteScale *
        L.rationalQuadraticSpaceMatrix.finiteAdelicSpecialOrthogonalBlockWeight T := by
  simpa using
    L.cliffordSpinCandidateRawFiniteScaleOfLattice_mul_blockWeight_eq_soScale_mul_blockWeight_of_comparisonBadPlaces_subset
      hn hP hconv T hST

end PositiveDefiniteIntegralLattice

end
