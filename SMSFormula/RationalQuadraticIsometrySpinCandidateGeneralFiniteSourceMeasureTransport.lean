import SMSFormula.RationalQuadraticIsometrySpinCandidateGeneralRawGoodTailTransport
import SMSFormula.RationalQuadraticIsometrySpinCandidateGeneralRawVolumeProductTransport

/-!
# Finite Spin source measures under an arbitrary rational isometry

The normalized infinite good tail has already been transported through the
canonical raw index `{v // v ∉ S}`.  Here the finite exceptional product is
treated in the same separated manner.  Each native exceptional product first
reindexes, for its own matrix only, to the canonical index `{v // v ∈ S}`.
The arbitrary-isometry Spin equivalence then acts fiberwise on those literal
raw primes, carrying the unnormalized local Haar product by the exact product
of reciprocal tangent moduli.

This keeps the exceptional scalar visible and avoids a cross-matrix dependent
Pi reindexing.  No genuine finite-adelic carrier, raw full Haar, quotient
measure, or Tamagawa value is asserted in this file.
-/

noncomputable section

open MeasureTheory PositiveDefiniteIntegralLattice
open scoped BigOperators ENNReal NNReal

namespace RationalQuadraticSpaceMatrix

set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 700000

variable {m : ℕ}
variable (W Z : RationalQuadraticSpaceMatrix (m + 1))
variable (e : W.quadraticForm.IsometryEquiv Z.quadraticForm)

local instance generalFiniteSourceDecidableEq :
    DecidableEq (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  Classical.decEq _

local instance generalFiniteSourcePrimeFact
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

local instance generalFiniteSourceGroupMeasurableSpace
    (V : RationalQuadraticSpaceMatrix (m + 1))
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    MeasurableSpace (V.HeightOnePadicCliffordSpinCandidateGroup v) :=
  borel _

local instance generalFiniteSourceGroupBorelSpace
    (V : RationalQuadraticSpaceMatrix (m + 1))
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    BorelSpace (V.HeightOnePadicCliffordSpinCandidateGroup v) :=
  ⟨rfl⟩

local instance generalFiniteSourceGroupSecondCountable
    (V : RationalQuadraticSpaceMatrix (m + 1))
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    SecondCountableTopology (V.HeightOnePadicCliffordSpinCandidateGroup v) := by
  infer_instance

/-- The canonical finite set of literal exceptional places. -/
abbrev SpinCandidateRawExceptionalPlace
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :=
  {v : IsDedekindDomain.HeightOneSpectrum ℤ // v ∈ S}

/-- The canonical raw exceptional product for one rational quadratic matrix. -/
abbrev SpinCandidateRawExceptionalProduct
    (V : RationalQuadraticSpaceMatrix (m + 1))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :=
  (v : SpinCandidateRawExceptionalPlace S) →
    V.HeightOnePadicCliffordSpinCandidateGroup v.1

local instance generalFiniteSourceRawExceptionalProductBorelSpace
    (V : RationalQuadraticSpaceMatrix (m + 1))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    BorelSpace (V.SpinCandidateRawExceptionalProduct S) :=
  Pi.borelSpace

local instance generalFiniteSourceNativeExceptionalProductBorelSpace
    (V : RationalQuadraticSpaceMatrix (m + 1))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    BorelSpace
      (V.FiniteAdelicCliffordSpinCandidateAdmissibleExceptionalProduct S) :=
  Pi.borelSpace

/-- Once `S` contains the native admissible bad set, its normalized
exceptional-place index is canonically the literal finite set `S`. -/
def cliffordSpinCandidateAdmissibleExceptionalPlaceEquivRaw
    (V : RationalQuadraticSpaceMatrix (m + 1))
    {S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)}
    (hV : V.cliffordSpinCandidateAdmissibleBadPlaces ⊆ S) :
    {v // v ∈ V.cliffordSpinCandidateAdmissibleExceptionalPlaces S} ≃
      SpinCandidateRawExceptionalPlace S where
  toFun v := ⟨v.1, by
    rcases Finset.mem_union.mp v.2 with hv | hv
    · exact hv
    · exact hV hv⟩
  invFun v := ⟨v.1, Finset.mem_union_left _ v.2⟩
  left_inv v := Subtype.ext rfl
  right_inv v := Subtype.ext rfl

/-- Reindex one native exceptional product to the canonical raw finite index.
This map mentions only one quadratic matrix. -/
def cliffordSpinCandidateAdmissibleExceptionalProductRawMeasurableEquiv
    (V : RationalQuadraticSpaceMatrix (m + 1))
    {S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)}
    (hV : V.cliffordSpinCandidateAdmissibleBadPlaces ⊆ S) :
    V.FiniteAdelicCliffordSpinCandidateAdmissibleExceptionalProduct S ≃ᵐ
      V.SpinCandidateRawExceptionalProduct S :=
  let ι := V.cliffordSpinCandidateAdmissibleExceptionalPlaceEquivRaw hV
  (MeasurableEquiv.piCongrLeft
    (fun v : {v // v ∈
        V.cliffordSpinCandidateAdmissibleExceptionalPlaces S} ↦
      V.HeightOnePadicCliffordSpinCandidateGroup v.1)
    ι.symm).symm

/-- The finite product of the native unnormalized local Spin Haar measures on
the canonical raw exceptional index. -/
def spinCandidateRawExceptionalProductMeasure
    (V : RationalQuadraticSpaceMatrix (m + 1))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measure (V.SpinCandidateRawExceptionalProduct S) :=
  Measure.pi fun v : SpinCandidateRawExceptionalPlace S ↦
    V.heightOnePadicCliffordSpinCandidateChartGluedGroupMeasure v.1

/-- Same-matrix exceptional reindexing preserves the finite Haar product. -/
theorem cliffordSpinCandidateAdmissibleExceptionalProductRaw_measurePreserving
    (V : RationalQuadraticSpaceMatrix (m + 1))
    {S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)}
    (hV : V.cliffordSpinCandidateAdmissibleBadPlaces ⊆ S) :
    MeasurePreserving
      (V.cliffordSpinCandidateAdmissibleExceptionalProductRawMeasurableEquiv hV)
      (V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalProductMeasure S)
      (V.spinCandidateRawExceptionalProductMeasure S) := by
  let ι := V.cliffordSpinCandidateAdmissibleExceptionalPlaceEquivRaw hV
  let μ := fun v : {v // v ∈
      V.cliffordSpinCandidateAdmissibleExceptionalPlaces S} ↦
    V.heightOnePadicCliffordSpinCandidateChartGluedGroupMeasure v.1
  let reindex :=
    (MeasurableEquiv.piCongrLeft
      (fun v : {v // v ∈
          V.cliffordSpinCandidateAdmissibleExceptionalPlaces S} ↦
        V.HeightOnePadicCliffordSpinCandidateGroup v.1)
      ι.symm).symm
  have hBack : MeasurePreserving reindex.symm
      (Measure.pi fun w : SpinCandidateRawExceptionalPlace S ↦ μ (ι.symm w))
      (Measure.pi μ) :=
    MeasureTheory.measurePreserving_piCongrLeft μ ι.symm
  have hForward : MeasurePreserving reindex
      (Measure.pi μ)
      (Measure.pi fun w : SpinCandidateRawExceptionalPlace S ↦ μ (ι.symm w)) :=
    MeasurePreserving.symm reindex.symm hBack
  simpa only [
    cliffordSpinCandidateAdmissibleExceptionalProductRawMeasurableEquiv,
    finiteAdelicCliffordSpinCandidateAdmissibleExceptionalProductMeasure,
    spinCandidateRawExceptionalProductMeasure, ι, μ, reindex] using hForward

/-- Product of the exact reciprocal p-adic tangent moduli over `S`. -/
def rationalIsometrySpinCandidateFiniteExceptionalModulus
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) : ℝ≥0 :=
  ∏ v : SpinCandidateRawExceptionalPlace S,
    ‖algebraMap ℚ ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1]
      (rationalIsometrySkewAdjointDetScalar W Z e)‖₊⁻¹

/-- Apply the unrestricted local Spin equivalence fiberwise on the canonical
raw exceptional index. -/
def rationalIsometrySpinCandidateRawExceptionalProductMeasurableEquiv
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    W.SpinCandidateRawExceptionalProduct S ≃ᵐ
      Z.SpinCandidateRawExceptionalProduct S :=
  MeasurableEquiv.piCongrRight fun v : SpinCandidateRawExceptionalPlace S ↦
    (rationalIsometrySpinCandidateContinuousMulEquiv
      W Z e ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1]).toMeasurableEquiv

/-- The canonical raw exceptional Haar product transports by precisely the
finite product of reciprocal local tangent moduli. -/
theorem map_rationalIsometrySpinCandidateRawExceptionalProductMeasure
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measure.map
        (rationalIsometrySpinCandidateRawExceptionalProductMeasurableEquiv
          W Z e S)
        (W.spinCandidateRawExceptionalProductMeasure S) =
      (rationalIsometrySpinCandidateFiniteExceptionalModulus W Z e S : ℝ≥0∞) •
        Z.spinCandidateRawExceptionalProductMeasure S := by
  let μ := fun v : SpinCandidateRawExceptionalPlace S ↦
    W.heightOnePadicCliffordSpinCandidateChartGluedGroupMeasure v.1
  let ν := fun v : SpinCandidateRawExceptionalPlace S ↦
    Z.heightOnePadicCliffordSpinCandidateChartGluedGroupMeasure v.1
  let q := fun v : SpinCandidateRawExceptionalPlace S ↦
    ‖algebraMap ℚ ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1]
      (rationalIsometrySkewAdjointDetScalar W Z e)‖₊⁻¹
  let f := fun v : SpinCandidateRawExceptionalPlace S ↦
    rationalIsometrySpinCandidateContinuousMulEquiv
      W Z e ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1]
  let fiberMap := fun (v : SpinCandidateRawExceptionalPlace S)
      (g : W.HeightOnePadicCliffordSpinCandidateGroup v.1) ↦ f v g
  let fiber :=
    rationalIsometrySpinCandidateRawExceptionalProductMeasurableEquiv W Z e S
  have hLocal (v : SpinCandidateRawExceptionalPlace S) :
      Measure.map (f v) (μ v) = q v • ν v := by
    simpa only [μ, ν, q, f,
      heightOnePadicCliffordSpinCandidateChartGluedGroupMeasure] using
      map_rationalIsometryPadicCliffordSpinCandidateChartGluedMeasure
        W Z e (Rat.HeightOneSpectrum.primesEquiv v.1).1
  letI (v : SpinCandidateRawExceptionalPlace S) :
      SigmaFinite (Measure.map (f v) (μ v)) := by
    rw [hLocal v]
    infer_instance
  letI (v : SpinCandidateRawExceptionalPlace S) :
      SigmaFinite (Measure.map (fiberMap v) (μ v)) := by
    change SigmaFinite (Measure.map (f v) (μ v))
    infer_instance
  have hFiber : Measure.map fiber (Measure.pi μ) =
      Measure.pi fun v ↦ q v • ν v := by
    calc
      Measure.map fiber (Measure.pi μ) =
          Measure.pi fun v ↦ Measure.map (fiberMap v) (μ v) := by
        exact Measure.pi_map_pi fun v ↦ (f v).measurable.aemeasurable
      _ = Measure.pi fun v ↦ q v • ν v := by
        congr 1
        funext v
        exact hLocal v
  have hPiScalar : Measure.pi (fun v ↦ q v • ν v) =
      ((↑(∏ v, q v) : ℝ≥0∞) • Measure.pi ν) := by
    apply Measure.pi_eq
    intro s hs
    rw [Measure.smul_apply, Measure.pi_pi]
    simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
    rw [ENNReal.coe_finset_prod, Finset.prod_mul_distrib]
  change Measure.map fiber (Measure.pi μ) = _
  rw [hFiber, hPiScalar]
  rfl

/-- The exceptional Haar product times the normalized good-tail probability
on the two canonical raw place indices. -/
def spinCandidateRawExceptionalTailSourceMeasure
    (V : RationalQuadraticSpaceMatrix (m + 1))
    {S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)}
    (hV : V.cliffordSpinCandidateAdmissibleBadPlaces ⊆ S) :
    Measure
      (V.SpinCandidateRawExceptionalProduct S × V.SpinCandidateRawGoodTail S) :=
  (V.spinCandidateRawExceptionalProductMeasure S).prod
    (V.spinCandidateRawGoodNormalizedTailMeasure hV)

/-- For one matrix, the native exceptional/tail source reindexes to the two
canonical raw place products. -/
def cliffordSpinCandidateAdmissibleExceptionalTailSourceRawMeasurableEquiv
    (V : RationalQuadraticSpaceMatrix (m + 1))
    {S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)}
    (hV : V.cliffordSpinCandidateAdmissibleBadPlaces ⊆ S) :
    (V.FiniteAdelicCliffordSpinCandidateAdmissibleExceptionalProduct S ×
        V.FiniteAdelicCliffordSpinCandidateAdmissibleIntegralTail S) ≃ᵐ
      (V.SpinCandidateRawExceptionalProduct S ×
        V.SpinCandidateRawGoodTail S) :=
  MeasurableEquiv.prodCongr
    (V.cliffordSpinCandidateAdmissibleExceptionalProductRawMeasurableEquiv hV)
    (V.cliffordSpinCandidateAdmissibleIntegralTailRawGoodMeasurableEquiv hV)

/-- Same-matrix passage from the native exceptional/tail source to the raw
middle source preserves its product measure exactly. -/
theorem
    cliffordSpinCandidateAdmissibleExceptionalTailSourceRaw_measurePreserving
    (V : RationalQuadraticSpaceMatrix (m + 1))
    {S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)}
    (hV : V.cliffordSpinCandidateAdmissibleBadPlaces ⊆ S) :
    MeasurePreserving
      (V.cliffordSpinCandidateAdmissibleExceptionalTailSourceRawMeasurableEquiv hV)
      (V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailCylinderSourceMeasure
        S)
      (V.spinCandidateRawExceptionalTailSourceMeasure hV) := by
  let f :=
    V.cliffordSpinCandidateAdmissibleExceptionalProductRawMeasurableEquiv hV
  let g :=
    V.cliffordSpinCandidateAdmissibleIntegralTailRawGoodMeasurableEquiv hV
  let μE :=
    V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalProductMeasure S
  let μT :=
    V.finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralTailMeasure S
  let νE := V.spinCandidateRawExceptionalProductMeasure S
  let νT := V.spinCandidateRawGoodNormalizedTailMeasure hV
  letI : SigmaFinite μE :=
    V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalProductMeasure_isSigmaFinite
      S
  refine ⟨(MeasurableEquiv.prodCongr f g).measurable, ?_⟩
  unfold
    finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailCylinderSourceMeasure
    spinCandidateRawExceptionalTailSourceMeasure
  change Measure.map (Prod.map f g) (μE.prod μT) = νE.prod νT
  rw [← Measure.map_prod_map μE μT f.measurable g.measurable,
    (V.cliffordSpinCandidateAdmissibleExceptionalProductRaw_measurePreserving
      hV).map_eq,
    (V.cliffordSpinCandidateAdmissibleIntegralTailRawGood_measurePreserving
      hV).map_eq]

/-- The arbitrary isometry acts separately on the raw exceptional and raw
good products. -/
def rationalIsometrySpinCandidateRawExceptionalTailSourceMeasurableEquiv
    {S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)}
    (hS : IsHorizontalIntegralTailRationalIsometrySupport W Z e S)
    (hW : W.cliffordSpinCandidateAdmissibleBadPlaces ⊆ S)
    (hZ : Z.cliffordSpinCandidateAdmissibleBadPlaces ⊆ S) :
    (W.SpinCandidateRawExceptionalProduct S × W.SpinCandidateRawGoodTail S) ≃ᵐ
      (Z.SpinCandidateRawExceptionalProduct S × Z.SpinCandidateRawGoodTail S) :=
  MeasurableEquiv.prodCongr
    (rationalIsometrySpinCandidateRawExceptionalProductMeasurableEquiv W Z e S)
    (rationalIsometrySpinCandidateRawGoodTailMeasurableEquiv W Z e hS hW hZ)

/-- The complete raw exceptional/tail source transports by exactly the
supported product of reciprocal p-adic tangent moduli. -/
theorem map_rationalIsometrySpinCandidateRawExceptionalTailSourceMeasure
    {S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)}
    (hS : IsHorizontalIntegralTailRationalIsometrySupport W Z e S)
    (hW : W.cliffordSpinCandidateAdmissibleBadPlaces ⊆ S)
    (hZ : Z.cliffordSpinCandidateAdmissibleBadPlaces ⊆ S) :
    Measure.map
        (rationalIsometrySpinCandidateRawExceptionalTailSourceMeasurableEquiv
          W Z e hS hW hZ)
        (W.spinCandidateRawExceptionalTailSourceMeasure hW) =
      (rationalIsometrySpinCandidateFiniteExceptionalModulus W Z e S : ℝ≥0∞) •
        Z.spinCandidateRawExceptionalTailSourceMeasure hZ := by
  let f := rationalIsometrySpinCandidateRawExceptionalProductMeasurableEquiv
    W Z e S
  let g := rationalIsometrySpinCandidateRawGoodTailMeasurableEquiv
    W Z e hS hW hZ
  let μE := W.spinCandidateRawExceptionalProductMeasure S
  let μT := W.spinCandidateRawGoodNormalizedTailMeasure hW
  let νE := Z.spinCandidateRawExceptionalProductMeasure S
  let νT := Z.spinCandidateRawGoodNormalizedTailMeasure hZ
  letI : SigmaFinite μE := by
    change SigmaFinite (W.spinCandidateRawExceptionalProductMeasure S)
    unfold spinCandidateRawExceptionalProductMeasure
    infer_instance
  letI (v : SpinCandidateRawGoodPlace S) : IsProbabilityMeasure
      (W.finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralLocalFactorMeasure
        S ⟨v.1,
          spinCandidateRawGoodPlace_not_mem_admissibleExceptionalPlaces
            W hW v⟩) :=
    W.finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralLocalFactorMeasure_isProbability
      S ⟨v.1,
        spinCandidateRawGoodPlace_not_mem_admissibleExceptionalPlaces W hW v⟩
  letI : IsProbabilityMeasure μT := by
    change IsProbabilityMeasure (W.spinCandidateRawGoodNormalizedTailMeasure hW)
    unfold spinCandidateRawGoodNormalizedTailMeasure
    infer_instance
  letI (v : SpinCandidateRawGoodPlace S) : IsProbabilityMeasure
      (Z.finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralLocalFactorMeasure
        S ⟨v.1,
          spinCandidateRawGoodPlace_not_mem_admissibleExceptionalPlaces
            Z hZ v⟩) :=
    Z.finiteAdelicCliffordSpinCandidateAdmissibleNormalizedIntegralLocalFactorMeasure_isProbability
      S ⟨v.1,
        spinCandidateRawGoodPlace_not_mem_admissibleExceptionalPlaces Z hZ v⟩
  letI : IsProbabilityMeasure νT := by
    change IsProbabilityMeasure (Z.spinCandidateRawGoodNormalizedTailMeasure hZ)
    unfold spinCandidateRawGoodNormalizedTailMeasure
    infer_instance
  unfold spinCandidateRawExceptionalTailSourceMeasure
  change Measure.map (Prod.map f g) (μE.prod μT) = _
  rw [← Measure.map_prod_map μE μT f.measurable g.measurable,
    map_rationalIsometrySpinCandidateRawExceptionalProductMeasure W Z e S,
    (rationalIsometrySpinCandidateRawGoodTail_measurePreserving
      W Z e hS hW hZ).map_eq]
  exact Measure.prod_smul_left
    (ν := νT)
    (((rationalIsometrySpinCandidateFiniteExceptionalModulus W Z e S : ℝ≥0) :
      ℝ≥0∞))

/-- On a support containing both native bad sets, the raw inverse-volume
correction is exactly the ratio of the two coherent finite block weights. -/
theorem spinCandidateRawRationalIsometryInverseVolumeCorrection_eq_weightRatio
    {S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)}
    (hS : IsHorizontalIntegralTailRationalIsometrySupport W Z e S)
    (hW : W.cliffordSpinCandidateAdmissibleBadPlaces ⊆ S)
    (hZ : Z.cliffordSpinCandidateAdmissibleBadPlaces ⊆ S) :
    e.spinCandidateRawRationalIsometryInverseVolumeCorrection S =
      W.finiteAdelicCliffordSpinCandidateAdmissibleBlockWeight S *
        (Z.finiteAdelicCliffordSpinCandidateAdmissibleBlockWeight S)⁻¹ := by
  have hbad : e.spinCandidateRawRationalIsometryBadPlaces S = S := by
    unfold QuadraticMap.IsometryEquiv.spinCandidateRawRationalIsometryBadPlaces
    rw [Finset.union_eq_left.mpr hW, Finset.union_eq_left.mpr hZ,
      Finset.union_eq_left.mpr hS.2.2.1]
  unfold
    QuadraticMap.IsometryEquiv.spinCandidateRawRationalIsometryInverseVolumeCorrection
  rw [QuadraticMap.IsometryEquiv.sourceSpinCandidateRawRationalIsometryExceptionalInverseVolume,
    QuadraticMap.IsometryEquiv.targetSpinCandidateRawRationalIsometryExceptionalInverseVolume,
    hbad,
    ← W.finiteAdelicCliffordSpinCandidateAdmissibleBlockWeight_eq_prod_sdiff_badPlaces
      S,
    ← Z.finiteAdelicCliffordSpinCandidateAdmissibleBlockWeight_eq_prod_sdiff_badPlaces
      S]

/-- Equivalently, the source coherent weight is the raw correction times the
target coherent weight. -/
theorem finiteAdelicSpinCandidateSourceWeight_eq_correction_mul_targetWeight
    {S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)}
    (hS : IsHorizontalIntegralTailRationalIsometrySupport W Z e S)
    (hW : W.cliffordSpinCandidateAdmissibleBadPlaces ⊆ S)
    (hZ : Z.cliffordSpinCandidateAdmissibleBadPlaces ⊆ S) :
    W.finiteAdelicCliffordSpinCandidateAdmissibleBlockWeight S =
      e.spinCandidateRawRationalIsometryInverseVolumeCorrection S *
        Z.finiteAdelicCliffordSpinCandidateAdmissibleBlockWeight S := by
  rw [spinCandidateRawRationalIsometryInverseVolumeCorrection_eq_weightRatio
    W Z e hS hW hZ]
  rw [mul_assoc, ENNReal.inv_mul_cancel
    (Z.finiteAdelicCliffordSpinCandidateAdmissibleBlockWeight_ne_zero S)
    (Z.finiteAdelicCliffordSpinCandidateAdmissibleBlockWeight_ne_top S),
    mul_one]

/-- After inserting the coherent finite weights, the canonical raw source
transports by the raw product correction times the exact exceptional tangent
modulus. -/
theorem map_rationalIsometrySpinCandidateCoherentRawExceptionalTailSourceMeasure
    {S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)}
    (hS : IsHorizontalIntegralTailRationalIsometrySupport W Z e S)
    (hW : W.cliffordSpinCandidateAdmissibleBadPlaces ⊆ S)
    (hZ : Z.cliffordSpinCandidateAdmissibleBadPlaces ⊆ S) :
    Measure.map
        (rationalIsometrySpinCandidateRawExceptionalTailSourceMeasurableEquiv
          W Z e hS hW hZ)
        (W.finiteAdelicCliffordSpinCandidateAdmissibleBlockWeight S •
          W.spinCandidateRawExceptionalTailSourceMeasure hW) =
      (e.spinCandidateRawRationalIsometryInverseVolumeCorrection S *
          (rationalIsometrySpinCandidateFiniteExceptionalModulus W Z e S :
            ℝ≥0∞)) •
        (Z.finiteAdelicCliffordSpinCandidateAdmissibleBlockWeight S •
          Z.spinCandidateRawExceptionalTailSourceMeasure hZ) := by
  rw [Measure.map_smul,
    map_rationalIsometrySpinCandidateRawExceptionalTailSourceMeasure
      W Z e hS hW hZ]
  have hscalar :
      W.finiteAdelicCliffordSpinCandidateAdmissibleBlockWeight S *
          (rationalIsometrySpinCandidateFiniteExceptionalModulus W Z e S :
            ℝ≥0∞) =
        (e.spinCandidateRawRationalIsometryInverseVolumeCorrection S *
            (rationalIsometrySpinCandidateFiniteExceptionalModulus W Z e S :
              ℝ≥0∞)) *
          Z.finiteAdelicCliffordSpinCandidateAdmissibleBlockWeight S := by
    rw [finiteAdelicSpinCandidateSourceWeight_eq_correction_mul_targetWeight
      W Z e hS hW hZ]
    ac_rfl
  simpa only [smul_smul] using congrArg
    (fun c : ℝ≥0∞ ↦ c • Z.spinCandidateRawExceptionalTailSourceMeasure hZ)
    hscalar

end RationalQuadraticSpaceMatrix
