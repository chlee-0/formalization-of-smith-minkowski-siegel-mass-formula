import SMSFormula.HaarMeasureTwoSheetLocalHomeomorph
import SMSFormula.MeasureInversionTransport
import SMSFormula.RationalCliffordSpinCandidateKernelMuTwo
import SMSFormula.RationalCliffordSpinCandidatePlacewiseHaar
import SMSFormula.RationalCliffordSpinCandidatePlacewiseSpinorNormContinuity
import SMSFormula.RationalSpecialOrthogonalFiniteAdelicDifferentialUnimodular
import SMSFormula.RationalSpecialOrthogonalFullAdelicDifferentialUnimodular

/-!
# Placewise unimodularity of the Clifford--Spin candidate

The real and p-adic candidate point maps need not be onto `SO`.  Instead we
push the glued source Haar measure to the actual open image.  The chosen
identity chart and the scalar kernel `{1, -1}` show that this pushforward is
a Haar measure on that image.  The image inherits an inversion-invariant Haar
measure from `SO`, so Haar uniqueness makes the pushed measure unimodular;
the generic homomorphic descent theorem then makes the source measure
unimodular.

No global point-map surjectivity, Tamagawa-volume formula, or condition (K)
enters these arguments.
-/

noncomputable section

open PositiveDefiniteIntegralLattice MeasureTheory

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

noncomputable local instance placewiseUnimodularRealSpecialOrthogonalMeasurableSpace :
    MeasurableSpace
      (PositiveDefiniteIntegralLattice.specialFormPreservingMatrixSubgroup
        (V.pairingMatrix.map (algebraMap ℚ ℝ))) := borel _

noncomputable local instance placewiseUnimodularRealSpecialOrthogonalBorelSpace :
    BorelSpace
      (PositiveDefiniteIntegralLattice.specialFormPreservingMatrixSubgroup
        (V.pairingMatrix.map (algebraMap ℚ ℝ))) := ⟨rfl⟩

noncomputable local instance placewiseUnimodularPadicSpecialOrthogonalMeasurableSpace
    (p : ℕ) [Fact (Nat.Prime p)] :
    MeasurableSpace
      (PositiveDefiniteIntegralLattice.specialFormPreservingMatrixSubgroup
        (V.pairingMatrix.map (algebraMap ℚ ℚ_[p]))) := borel _

noncomputable local instance placewiseUnimodularPadicSpecialOrthogonalBorelSpace
    (p : ℕ) [Fact (Nat.Prime p)] :
    BorelSpace
      (PositiveDefiniteIntegralLattice.specialFormPreservingMatrixSubgroup
        (V.pairingMatrix.map (algebraMap ℚ ℚ_[p]))) := ⟨rfl⟩

/-! ## The scalar two-point kernel over fields -/

/-- The scalar `-1` point in the candidate point-map kernel. -/
def cliffordSpinCandidateNegOnePoint
    (K : Type*) [Field K] [Algebra ℚ K] :
    V.CliffordSpinCandidateGroup K :=
  (V.rootsOfUnityMulEquivCliffordSpinCandidateAffineCoordinateKernelPoint
    K (negOneRootOfUnity K)).1

@[simp]
theorem cliffordSpinCandidateNegOnePoint_mem_ker
    (K : Type*) [Field K] [Algebra ℚ K] :
    V.cliffordSpinCandidateGroupToSpecialOrthogonal K
      (V.cliffordSpinCandidateNegOnePoint K) = 1 :=
  (V.rootsOfUnityMulEquivCliffordSpinCandidateAffineCoordinateKernelPoint
    K (negOneRootOfUnity K)).2

/-- Over a field, every point in the candidate point-map kernel is scalar
`1` or scalar `-1`. -/
theorem eq_one_or_cliffordSpinCandidateNegOnePoint_of_pointMap_eq_one
    (K : Type*) [Field K] [Algebra ℚ K]
    (g : V.CliffordSpinCandidateGroup K)
    (hg : V.cliffordSpinCandidateGroupToSpecialOrthogonal K g = 1) :
    g = 1 ∨ g = V.cliffordSpinCandidateNegOnePoint K := by
  let E :=
    V.rootsOfUnityMulEquivCliffordSpinCandidateAffineCoordinateKernelPoint K
  let x : (V.cliffordSpinCandidateGroupToSpecialOrthogonal K).ker := ⟨g, hg⟩
  let z : rootsOfUnity 2 K := E.symm x
  have hzpow : (((z : Kˣ) : K)) ^ 2 = 1 := by
    exact congrArg Units.val z.property
  rcases sq_eq_one_iff.mp hzpow with hz | hz
  · left
    have hz' : z = 1 := by
      apply Subtype.ext
      apply Units.ext
      exact hz
    have hx : x = 1 := by
      calc
        x = E z := (E.apply_symm_apply x).symm
        _ = E 1 := congrArg E hz'
        _ = 1 := map_one E
    exact congrArg
      (fun y : (V.cliffordSpinCandidateGroupToSpecialOrthogonal K).ker => y.1) hx
  · right
    have hz' : z = negOneRootOfUnity K := by
      apply Subtype.ext
      apply Units.ext
      simpa [negOneRootOfUnity] using hz
    have hx : x = E (negOneRootOfUnity K) := by
      calc
        x = E z := (E.apply_symm_apply x).symm
        _ = E (negOneRootOfUnity K) := congrArg E hz'
    exact congrArg
      (fun y : (V.cliffordSpinCandidateGroupToSpecialOrthogonal K).ker => y.1) hx

/-! ## Real place -/

noncomputable instance realCliffordSpinCandidateImageLocallyCompactSpace :
    LocallyCompactSpace V.RealCliffordSpinCandidateImage :=
  V.isOpen_realCliffordSpinCandidateImage.locallyCompactSpace

noncomputable instance realCliffordSpinCandidateImageSecondCountableTopology :
    SecondCountableTopology V.RealCliffordSpinCandidateImage :=
  TopologicalSpace.Subtype.secondCountableTopology _

/-- The fixed differential `SO(ℝ)` measure restricted to the actual Spin
image. -/
def realCliffordSpinCandidateImageDifferentialMeasure :
    Measure V.RealCliffordSpinCandidateImage :=
  Measure.comap V.RealCliffordSpinCandidateImage.subtype
    V.realInvariantDifferentialGroupMeasure

noncomputable instance realCliffordSpinCandidateImageDifferentialMeasure_isHaar :
    Measure.IsHaarMeasure V.realCliffordSpinCandidateImageDifferentialMeasure := by
  letI : Measure.IsHaarMeasure V.realInvariantDifferentialGroupMeasure :=
    V.realInvariantDifferentialGroupMeasure_isHaarMeasure
  unfold realCliffordSpinCandidateImageDifferentialMeasure
  exact Measure.IsHaarMeasure.comap
    (μ := V.realInvariantDifferentialGroupMeasure)
    (f := V.RealCliffordSpinCandidateImage.subtype)
    (mH := ContinuousMul.measurableMul)
    V.isOpen_realCliffordSpinCandidateImage.isOpenEmbedding_subtypeVal

set_option backward.isDefEq.respectTransparency false in
noncomputable instance
    realCliffordSpinCandidateImageDifferentialMeasure_isInvInvariant :
    Measure.IsInvInvariant V.realCliffordSpinCandidateImageDifferentialMeasure := by
  letI : Measure.IsInvInvariant V.realInvariantDifferentialGroupMeasure :=
    V.realInvariantDifferentialGroupMeasure_isInvInvariant
  unfold realCliffordSpinCandidateImageDifferentialMeasure
  exact Measure.subgroup_comap_measure_isInvInvariant_of_subtype_mspace
    (G := V.RealSpecialOrthogonalGroup)
    (muG := V.realInvariantDifferentialGroupMeasure)
    V.RealCliffordSpinCandidateImage rfl
    V.isOpen_realCliffordSpinCandidateImage.measurableSet

/-- The pushforward of the real glued Spin Haar measure to its actual image
is Haar. -/
noncomputable instance
    map_realCliffordSpinCandidateRangeRestrict_chartGluedMeasure_isHaar :
    Measure.IsHaarMeasure
      (Measure.map
        V.realCliffordSpinCandidateToSpecialOrthogonalHom.rangeRestrict
        V.realCliffordSpinCandidateChartGluedMeasure) := by
  letI : Measure.IsHaarMeasure
      V.realCliffordSpinCandidateChartGluedMeasure :=
    V.realCliffordSpinCandidateChartGluedMeasure_isHaarMeasure
  exact
    MeasureTheory.TranslatedHomChart.isHaarMeasure_map_rangeRestrict_of_two_point_local_chart
      V.realCliffordSpinCandidateToSpecialOrthogonalHom
      V.realCliffordSpinCandidateIdentityChart
      (V.continuous_cliffordSpinCandidateGroupToSpecialOrthogonal ℝ)
      V.realCliffordSpinCandidateIdentityChart_coe
      V.one_mem_realCliffordSpinCandidateIdentityChart_source
      V.isOpen_realCliffordSpinCandidateImage
      (V.cliffordSpinCandidateNegOnePoint ℝ)
      (V.cliffordSpinCandidateNegOnePoint_mem_ker ℝ)
      (V.eq_one_or_cliffordSpinCandidateNegOnePoint_of_pointMap_eq_one ℝ)
      V.realCliffordSpinCandidateChartGluedMeasure

/-- The pushed real Spin Haar measure is inversion invariant on the actual
image. -/
noncomputable instance
    map_realCliffordSpinCandidateRangeRestrict_chartGluedMeasure_isInvInvariant :
    Measure.IsInvInvariant
      (Measure.map
        V.realCliffordSpinCandidateToSpecialOrthogonalHom.rangeRestrict
        V.realCliffordSpinCandidateChartGluedMeasure) := by
  exact Measure.isInvInvariant_of_isHaarMeasure_of_exists
    (Measure.map
      V.realCliffordSpinCandidateToSpecialOrthogonalHom.rangeRestrict
      V.realCliffordSpinCandidateChartGluedMeasure)
    V.realCliffordSpinCandidateImageDifferentialMeasure

/-- The actual real glued Spin measure is inversion invariant. -/
noncomputable instance realCliffordSpinCandidateChartGluedMeasure_isInvInvariant :
    Measure.IsInvInvariant V.realCliffordSpinCandidateChartGluedMeasure := by
  letI : Measure.IsHaarMeasure
      V.realCliffordSpinCandidateChartGluedMeasure :=
    V.realCliffordSpinCandidateChartGluedMeasure_isHaarMeasure
  have hf : Continuous
      V.realCliffordSpinCandidateToSpecialOrthogonalHom.rangeRestrict :=
    (V.continuous_cliffordSpinCandidateGroupToSpecialOrthogonal ℝ).subtype_mk _
  exact Measure.isInvInvariant_of_map_of_isHaarMeasure
    V.realCliffordSpinCandidateChartGluedMeasure
    V.realCliffordSpinCandidateToSpecialOrthogonalHom.rangeRestrict
    hf.measurable

/-- The actual real glued Spin measure is right invariant at the same scale. -/
noncomputable instance realCliffordSpinCandidateChartGluedMeasure_isMulRightInvariant :
    Measure.IsMulRightInvariant V.realCliffordSpinCandidateChartGluedMeasure := by
  letI : Measure.IsHaarMeasure
      V.realCliffordSpinCandidateChartGluedMeasure :=
    V.realCliffordSpinCandidateChartGluedMeasure_isHaarMeasure
  exact Measure.isMulRightInvariant_of_isInvInvariant
    V.realCliffordSpinCandidateChartGluedMeasure

/-! ## P-adic places -/

noncomputable instance padicCliffordSpinCandidateImageLocallyCompactSpace
    (p : ℕ) [Fact (Nat.Prime p)] :
    LocallyCompactSpace (V.PadicCliffordSpinCandidateImage p) :=
  (V.isOpen_padicCliffordSpinCandidateImage p).locallyCompactSpace

noncomputable instance padicCliffordSpinCandidateImageSecondCountableTopology
    (p : ℕ) [Fact (Nat.Prime p)] :
    SecondCountableTopology (V.PadicCliffordSpinCandidateImage p) :=
  TopologicalSpace.Subtype.secondCountableTopology _

/-- The fixed differential `SO(ℚ_p)` measure restricted to the actual Spin
image. -/
def padicCliffordSpinCandidateImageDifferentialMeasure
    (p : ℕ) [Fact (Nat.Prime p)] :
    Measure (V.PadicCliffordSpinCandidateImage p) :=
  Measure.comap (V.PadicCliffordSpinCandidateImage p).subtype
    (V.padicInvariantDifferentialGroupMeasure p)

noncomputable instance padicCliffordSpinCandidateImageDifferentialMeasure_isHaar
    (p : ℕ) [Fact (Nat.Prime p)] :
    Measure.IsHaarMeasure
      (V.padicCliffordSpinCandidateImageDifferentialMeasure p) := by
  letI : Measure.IsHaarMeasure (V.padicInvariantDifferentialGroupMeasure p) :=
    V.padicInvariantDifferentialGroupMeasure_isHaarMeasure p
  unfold padicCliffordSpinCandidateImageDifferentialMeasure
  exact Measure.IsHaarMeasure.comap
    (μ := V.padicInvariantDifferentialGroupMeasure p)
    (f := (V.PadicCliffordSpinCandidateImage p).subtype)
    (mH := ContinuousMul.measurableMul)
    (V.isOpen_padicCliffordSpinCandidateImage p).isOpenEmbedding_subtypeVal

set_option backward.isDefEq.respectTransparency false in
noncomputable instance
    padicCliffordSpinCandidateImageDifferentialMeasure_isInvInvariant
    (p : ℕ) [Fact (Nat.Prime p)] :
    Measure.IsInvInvariant
      (V.padicCliffordSpinCandidateImageDifferentialMeasure p) := by
  letI : Measure.IsInvInvariant (V.padicInvariantDifferentialGroupMeasure p) :=
    V.padicInvariantDifferentialGroupMeasure_isInvInvariant p
  unfold padicCliffordSpinCandidateImageDifferentialMeasure
  exact Measure.subgroup_comap_measure_isInvInvariant_of_subtype_mspace
    (G := V.specialOrthogonalMatrixGroup ℚ_[p])
    (muG := V.padicInvariantDifferentialGroupMeasure p)
    (V.PadicCliffordSpinCandidateImage p) rfl
    (V.isOpen_padicCliffordSpinCandidateImage p).measurableSet

/-- The pushforward of the p-adic glued Spin Haar measure to its actual image
is Haar. -/
noncomputable instance
    map_padicCliffordSpinCandidateRangeRestrict_chartGluedMeasure_isHaar
    (p : ℕ) [Fact (Nat.Prime p)] :
    Measure.IsHaarMeasure
      (Measure.map
        (V.cliffordSpinCandidateGroupToSpecialOrthogonal ℚ_[p]).rangeRestrict
        (V.padicCliffordSpinCandidateChartGluedMeasure p)) := by
  letI : Measure.IsHaarMeasure
      (V.padicCliffordSpinCandidateChartGluedMeasure p) :=
    V.padicCliffordSpinCandidateChartGluedMeasure_isHaarMeasure p
  exact
    MeasureTheory.TranslatedHomChart.isHaarMeasure_map_rangeRestrict_of_two_point_local_chart
      (V.cliffordSpinCandidateGroupToSpecialOrthogonal ℚ_[p])
      (V.padicCliffordSpinCandidateIdentityChart p)
      (V.continuous_cliffordSpinCandidateGroupToSpecialOrthogonal ℚ_[p])
      (V.padicCliffordSpinCandidateIdentityChart_coe p)
      (V.one_mem_padicCliffordSpinCandidateIdentityChart_source p)
      (V.isOpen_padicCliffordSpinCandidateImage p)
      (V.cliffordSpinCandidateNegOnePoint ℚ_[p])
      (V.cliffordSpinCandidateNegOnePoint_mem_ker ℚ_[p])
      (V.eq_one_or_cliffordSpinCandidateNegOnePoint_of_pointMap_eq_one ℚ_[p])
      (V.padicCliffordSpinCandidateChartGluedMeasure p)

/-- The pushed p-adic Spin Haar measure is inversion invariant on the actual
image. -/
noncomputable instance
    map_padicCliffordSpinCandidateRangeRestrict_chartGluedMeasure_isInvInvariant
    (p : ℕ) [Fact (Nat.Prime p)] :
    Measure.IsInvInvariant
      (Measure.map
        (V.cliffordSpinCandidateGroupToSpecialOrthogonal ℚ_[p]).rangeRestrict
        (V.padicCliffordSpinCandidateChartGluedMeasure p)) := by
  exact Measure.isInvInvariant_of_isHaarMeasure_of_exists
    (Measure.map
      (V.cliffordSpinCandidateGroupToSpecialOrthogonal ℚ_[p]).rangeRestrict
      (V.padicCliffordSpinCandidateChartGluedMeasure p))
    (V.padicCliffordSpinCandidateImageDifferentialMeasure p)

/-- The actual p-adic glued Spin measure is inversion invariant. -/
noncomputable instance padicCliffordSpinCandidateChartGluedMeasure_isInvInvariant
    (p : ℕ) [Fact (Nat.Prime p)] :
    Measure.IsInvInvariant
      (V.padicCliffordSpinCandidateChartGluedMeasure p) := by
  letI : Measure.IsHaarMeasure
      (V.padicCliffordSpinCandidateChartGluedMeasure p) :=
    V.padicCliffordSpinCandidateChartGluedMeasure_isHaarMeasure p
  have hf : Continuous
      (V.cliffordSpinCandidateGroupToSpecialOrthogonal ℚ_[p]).rangeRestrict :=
    (V.continuous_cliffordSpinCandidateGroupToSpecialOrthogonal ℚ_[p]).subtype_mk _
  exact Measure.isInvInvariant_of_map_of_isHaarMeasure
    (V.padicCliffordSpinCandidateChartGluedMeasure p)
    (V.cliffordSpinCandidateGroupToSpecialOrthogonal ℚ_[p]).rangeRestrict
    hf.measurable

/-- The actual p-adic glued Spin measure is right invariant at the same
scale. -/
noncomputable instance padicCliffordSpinCandidateChartGluedMeasure_isMulRightInvariant
    (p : ℕ) [Fact (Nat.Prime p)] :
    Measure.IsMulRightInvariant
      (V.padicCliffordSpinCandidateChartGluedMeasure p) := by
  letI : Measure.IsHaarMeasure
      (V.padicCliffordSpinCandidateChartGluedMeasure p) :=
    V.padicCliffordSpinCandidateChartGluedMeasure_isHaarMeasure p
  exact Measure.isMulRightInvariant_of_isInvInvariant
    (V.padicCliffordSpinCandidateChartGluedMeasure p)

end RationalQuadraticSpaceMatrix
