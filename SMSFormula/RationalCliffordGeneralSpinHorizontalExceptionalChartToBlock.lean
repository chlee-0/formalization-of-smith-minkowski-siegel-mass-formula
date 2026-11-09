import SMSFormula.RationalCliffordGeneralSpinHorizontalExceptionalChartDisintegration
import SMSFormula.RationalCliffordGeneralSpinHorizontalExceptionalTailMeasure

/-!
# Horizontal exceptional identity charts inside the established block source

The finite square/Spin calculation was carried out on products of local
parameter charts, whereas the horizontal restricted-product construction uses
finite products of the ambient local `GSpin` groups.  This file gives the exact
carrier and measure bridge between those two models.

Componentwise scalar-times-Spin multiplication sends the parameter product to
the literal identity-chart carrier in the established exceptional product.
Its measure is exactly the restriction of the already fixed exceptional Haar
product to that carrier.  In particular, transporting the finite chart
calculation introduces no new scalar, sheet count, or Euler product.
-/

noncomputable section

open MeasureTheory

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

set_option synthInstance.maxHeartbeats 600000
set_option maxHeartbeats 2400000

local instance horizontalExceptionalChartToBlockPrimeFact
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

local instance horizontalExceptionalChartToBlockDecidableEq :
    DecidableEq (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  Classical.decEq _

noncomputable local instance
    horizontalExceptionalChartToBlockPadicUnitMeasurableSpace
    (p : ℕ) [Fact (Nat.Prime p)] : MeasurableSpace ℚ_[p]ˣ := borel _

noncomputable local instance horizontalExceptionalChartToBlockPadicUnitBorelSpace
    (p : ℕ) [Fact (Nat.Prime p)] : BorelSpace ℚ_[p]ˣ := ⟨rfl⟩

noncomputable local instance
    horizontalExceptionalChartToBlockPadicUnitSecondCountable
    (p : ℕ) [Fact (Nat.Prime p)] : SecondCountableTopology ℚ_[p]ˣ := by
  letI : SecondCountableTopology ℚ_[p]ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  letI : SecondCountableTopology (ℚ_[p] × ℚ_[p]ᵐᵒᵖ) := inferInstance
  exact Units.isEmbedding_embedProduct.secondCountableTopology

noncomputable local instance horizontalExceptionalChartToBlockPadicSOMeasurableSpace
    (p : ℕ) [Fact (Nat.Prime p)] :
    MeasurableSpace (V.specialOrthogonalMatrixGroup ℚ_[p]) :=
  V.padicSpecialOrthogonalGroupMeasurableSpace_spinorNorm p

noncomputable local instance horizontalExceptionalChartToBlockPadicSOBorelSpace
    (p : ℕ) [Fact (Nat.Prime p)] :
    BorelSpace (V.specialOrthogonalMatrixGroup ℚ_[p]) :=
  V.padicSpecialOrthogonalGroupBorelSpace_spinorNorm p

noncomputable local instance
    horizontalExceptionalChartToBlockPadicGSpinMeasurableSpace
    (p : ℕ) [Fact (Nat.Prime p)] :
    MeasurableSpace (V.CliffordGeneralSpinIntrinsicPoint ℚ_[p]) := borel _

noncomputable local instance horizontalExceptionalChartToBlockPadicGSpinBorelSpace
    (p : ℕ) [Fact (Nat.Prime p)] :
    BorelSpace (V.CliffordGeneralSpinIntrinsicPoint ℚ_[p]) := ⟨rfl⟩

/-! ## Local carrier equality -/

/-- Scalar-times-Spin multiplication identifies the local parameter measure
with the fixed ambient horizontal Haar restricted to the identity chart. -/
theorem
    map_padicCliffordGeneralSpinHorizontalProductIdentityChartSourceMeasure_centralSpin_eq_restrict
    (p : ℕ) [Fact (Nat.Prime p)] :
    Measure.map
        (fun x :
            (V.padicCliffordGeneralSpinHorizontalProductIdentityChart p).source ↦
          V.cliffordGeneralSpinCentralSpinMultiplication ℚ_[p] x)
        (V.padicCliffordGeneralSpinHorizontalProductIdentityChartSourceMeasure p) =
      (V.padicCliffordGeneralSpinHorizontalDifferentialHaarMeasure p).restrict
        (V.padicCliffordGeneralSpinCentralFiberIdentityChart p).source := by
  rw [V.map_padicCliffordGeneralSpinHorizontalProductIdentityChartSourceMeasure_centralSpin p]
  exact
    (V.restrict_padicCliffordGeneralSpinHorizontalDifferentialHaarMeasure_identity p).symm

/-! ## Finite exceptional product bridge -/

/-- The parameter source over precisely the exceptional coordinates used by
the established horizontal block at `S`. -/
abbrev CliffordGeneralSpinHorizontalExceptionalBlockChartSource
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :=
  V.CliffordGeneralSpinHorizontalExceptionalChartSource
    (S ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces)

/-- Componentwise scalar-times-Spin multiplication into the established
exceptional product carrier. -/
def cliffordGeneralSpinHorizontalExceptionalChartToBlock
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    V.CliffordGeneralSpinHorizontalExceptionalBlockChartSource S →
      V.CliffordGeneralSpinHorizontalExceptionalProduct S :=
  fun g v ↦
    V.cliffordGeneralSpinCentralSpinMultiplication
      ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1] (g v)

theorem continuous_cliffordGeneralSpinHorizontalExceptionalChartToBlock
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Continuous (V.cliffordGeneralSpinHorizontalExceptionalChartToBlock S) := by
  exact continuous_pi fun v ↦
    (V.continuous_cliffordGeneralSpinCentralSpinMultiplication
      ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1]).comp
        (continuous_subtype_val.comp (continuous_apply v))

/-- The literal product of local ambient horizontal Haar restrictions to the
identity charts. -/
def cliffordGeneralSpinHorizontalExceptionalIdentityChartRestrictedMeasure
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measure (V.CliffordGeneralSpinHorizontalExceptionalProduct S) :=
  Measure.pi fun
      v : {v // v ∈ S ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces} ↦
    (V.heightOnePadicCliffordGeneralSpinHorizontalHaarMeasure v.1).restrict
      (V.padicCliffordGeneralSpinCentralFiberIdentityChart
        (Rat.HeightOneSpectrum.primesEquiv v.1).1).source

/-- The product of parameter-chart measures maps exactly to the product of
the restricted ambient local Haar measures. -/
theorem map_cliffordGeneralSpinHorizontalExceptionalChartToBlock
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measure.map
        (V.cliffordGeneralSpinHorizontalExceptionalChartToBlock S)
        (V.cliffordGeneralSpinHorizontalExceptionalChartSourceMeasure
          (S ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces)) =
      V.cliffordGeneralSpinHorizontalExceptionalIdentityChartRestrictedMeasure S := by
  let f := fun
      v : {v // v ∈ S ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces} ↦
    fun x :
        (V.padicCliffordGeneralSpinHorizontalProductIdentityChart
          (Rat.HeightOneSpectrum.primesEquiv v.1).1).source ↦
      V.cliffordGeneralSpinCentralSpinMultiplication
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1] x
  let μ := fun
      v : {v // v ∈ S ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces} ↦
    V.padicCliffordGeneralSpinHorizontalProductIdentityChartSourceMeasure
      (Rat.HeightOneSpectrum.primesEquiv v.1).1
  letI (v : {v // v ∈
      S ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces}) :
      SigmaFinite ((μ v).map (f v)) := by
    rw [V.map_padicCliffordGeneralSpinHorizontalProductIdentityChartSourceMeasure_centralSpin_eq_restrict]
    letI : Measure.IsHaarMeasure
        (V.padicCliffordGeneralSpinHorizontalDifferentialHaarMeasure
          (Rat.HeightOneSpectrum.primesEquiv v.1).1) :=
      V.padicCliffordGeneralSpinHorizontalDifferentialHaarMeasure_isHaarMeasure
        (Rat.HeightOneSpectrum.primesEquiv v.1).1
    letI : SigmaFinite
        (V.padicCliffordGeneralSpinHorizontalDifferentialHaarMeasure
          (Rat.HeightOneSpectrum.primesEquiv v.1).1) :=
      Measure.IsHaarMeasure.sigmaFinite _
    infer_instance
  have hpi :
      (Measure.pi μ).map (fun g v ↦ f v (g v)) =
        Measure.pi fun v ↦ (μ v).map (f v) :=
    Measure.pi_map_pi fun v ↦
      ((V.continuous_cliffordGeneralSpinCentralSpinMultiplication
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1]).comp
          continuous_subtype_val).measurable.aemeasurable
  simpa [cliffordGeneralSpinHorizontalExceptionalChartToBlock,
    cliffordGeneralSpinHorizontalExceptionalChartSourceMeasure,
    cliffordGeneralSpinHorizontalExceptionalIdentityChartRestrictedMeasure,
    heightOnePadicCliffordGeneralSpinHorizontalHaarMeasure, f, μ,
    V.map_padicCliffordGeneralSpinHorizontalProductIdentityChartSourceMeasure_centralSpin_eq_restrict]
    using hpi

/-- The literal identity-chart carrier inside the established exceptional
product. -/
def cliffordGeneralSpinHorizontalExceptionalIdentityChartCarrier
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Set (V.CliffordGeneralSpinHorizontalExceptionalProduct S) :=
  Set.pi Set.univ fun
      v : {v // v ∈ S ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces} ↦
    (V.padicCliffordGeneralSpinCentralFiberIdentityChart
      (Rat.HeightOneSpectrum.primesEquiv v.1).1).source

/-- The finite chart map has exactly the identity-chart carrier as its image;
no ambient exceptional point is lost inside that carrier. -/
theorem range_cliffordGeneralSpinHorizontalExceptionalChartToBlock
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Set.range (V.cliffordGeneralSpinHorizontalExceptionalChartToBlock S) =
      V.cliffordGeneralSpinHorizontalExceptionalIdentityChartCarrier S := by
  ext g
  constructor
  · rintro ⟨x, rfl⟩
    intro v _
    exact
      (V.padicCliffordGeneralSpinCentralSpinIdentityChart
        (Rat.HeightOneSpectrum.primesEquiv v.1).1).map_source (x v).2
  · intro hg
    let x : V.CliffordGeneralSpinHorizontalExceptionalBlockChartSource S :=
      fun v ↦
        (V.padicCliffordGeneralSpinCentralSpinIdentityChart
          (Rat.HeightOneSpectrum.primesEquiv v.1).1).toHomeomorphSourceTarget.symm
            ⟨g v, hg v (Set.mem_univ v)⟩
    refine ⟨x, ?_⟩
    funext v
    have h :=
      (V.padicCliffordGeneralSpinCentralSpinIdentityChart
        (Rat.HeightOneSpectrum.primesEquiv v.1).1).toHomeomorphSourceTarget
          |>.apply_symm_apply ⟨g v, hg v (Set.mem_univ v)⟩
    exact congrArg Subtype.val h

/-- Restricting the established exceptional Haar product to the identity
chart carrier is coordinatewise restriction, exactly as in the bridge
measure. -/
theorem restrict_cliffordGeneralSpinHorizontalExceptionalProductMeasure_identityChart
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    (V.cliffordGeneralSpinHorizontalExceptionalProductMeasure S).restrict
        (V.cliffordGeneralSpinHorizontalExceptionalIdentityChartCarrier S) =
      V.cliffordGeneralSpinHorizontalExceptionalIdentityChartRestrictedMeasure S := by
  unfold cliffordGeneralSpinHorizontalExceptionalProductMeasure
    cliffordGeneralSpinHorizontalExceptionalIdentityChartCarrier
    cliffordGeneralSpinHorizontalExceptionalIdentityChartRestrictedMeasure
  rw [Measure.restrict_pi_pi]

/-- The finite parameter chart therefore lands on the established horizontal
exceptional block with exactly its restricted ambient Haar measure. -/
theorem map_cliffordGeneralSpinHorizontalExceptionalChartToBlock_eq_restrict
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measure.map
        (V.cliffordGeneralSpinHorizontalExceptionalChartToBlock S)
        (V.cliffordGeneralSpinHorizontalExceptionalChartSourceMeasure
          (S ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces)) =
      (V.cliffordGeneralSpinHorizontalExceptionalProductMeasure S).restrict
        (V.cliffordGeneralSpinHorizontalExceptionalIdentityChartCarrier S) := by
  rw [V.map_cliffordGeneralSpinHorizontalExceptionalChartToBlock S,
    V.restrict_cliffordGeneralSpinHorizontalExceptionalProductMeasure_identityChart S]

end RationalQuadraticSpaceMatrix
