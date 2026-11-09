import SMSFormula.RationalQuadraticIsometryGeneralSpinFiniteExceptionalOverlapMeasure
import SMSFormula.RationalQuadraticIsometryGeneralSpinIntegralTailTransport
import SMSFormula.RationalCliffordGeneralSpinHorizontalRealFiniteChartParameter

/-!
# Finite-adelic presentation overlap cylinders

The finite product of selected p-adic chart overlaps is
adjoined to the normalized cofinite integral tail.  The resulting block and
ambient sources map through the existing exceptional/tail assembly into the
finite-adelic intrinsic `GSpin` groups, and presentation transport
commutes exactly with those maps.

The source and finite-adelic overlap-cylinder measures transform by the finite
product of reciprocal local presentation moduli.  The coherent principal-block
weights used by the directed horizontal Haar measure are not
inserted here; they are compared separately.
-/

noncomputable section

open MeasureTheory
open scoped NNReal ENNReal

namespace RationalQuadraticSpaceMatrix

local instance presentationOverlapCylinderDecidableEq :
    DecidableEq (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  Classical.decEq _

local instance presentationOverlapCylinderPrimeFact
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

local instance presentationOverlapCylinderFiniteMeasurableSpace
    {k : ℕ} (W : RationalQuadraticSpaceMatrix k) :
    MeasurableSpace W.FiniteAdelicCliffordGeneralSpinGroup :=
  borel _

local instance presentationOverlapCylinderFiniteBorelSpace
    {k : ℕ} (W : RationalQuadraticSpaceMatrix k) :
    BorelSpace W.FiniteAdelicCliffordGeneralSpinGroup :=
  ⟨rfl⟩

/-! ## Exact components of the existing exceptional/tail assembly -/

theorem cliffordGeneralSpinHorizontalIdentityChartSourceToAmbient_component_of_mem
    {n : ℕ}
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (g : V.CliffordGeneralSpinHorizontalExceptionalProduct S ×
      V.CliffordGeneralSpinHorizontalIntegralTail S)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ)
    (hv : v ∈ S ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces) :
    V.finiteAdelicCliffordGeneralSpinHeightOneComponentHom v
        (V.cliffordGeneralSpinHorizontalIdentityChartSourceToAmbient S g) =
      g.1 ⟨v, hv⟩ := by
  let h := V.finiteAdelicCliffordGeneralSpinHeightOneComponents_assembly
    ((V.cliffordGeneralSpinHorizontalExceptionalTailRestrictedPrincipalBlockHomeomorph
      S g).1)
  have hvComponent := congrFun h v
  change V.finiteAdelicCliffordGeneralSpinHeightOneComponentsHom
      (V.finiteAdelicCliffordGeneralSpinRestrictedFamilyAssembly
        ((V.cliffordGeneralSpinHorizontalExceptionalTailRestrictedPrincipalBlockHomeomorph
          S g).1)) v = g.1 ⟨v, hv⟩
  rw [hvComponent]
  exact
    V.cliffordGeneralSpinHorizontalExceptionalTailToRestrictedPrincipalBlock_apply_mem
      S g v hv

theorem cliffordGeneralSpinHorizontalIdentityChartSourceToAmbient_component_of_notMem
    {n : ℕ}
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (g : V.CliffordGeneralSpinHorizontalExceptionalProduct S ×
      V.CliffordGeneralSpinHorizontalIntegralTail S)
    (v : V.CliffordGeneralSpinHorizontalIntegralPlace S) :
    V.finiteAdelicCliffordGeneralSpinHeightOneComponentHom v.1
        (V.cliffordGeneralSpinHorizontalIdentityChartSourceToAmbient S g) =
      (g.2 v).1 := by
  let h := V.finiteAdelicCliffordGeneralSpinHeightOneComponents_assembly
    ((V.cliffordGeneralSpinHorizontalExceptionalTailRestrictedPrincipalBlockHomeomorph
      S g).1)
  have hvComponent := congrFun h v.1
  change V.finiteAdelicCliffordGeneralSpinHeightOneComponentsHom
      (V.finiteAdelicCliffordGeneralSpinRestrictedFamilyAssembly
        ((V.cliffordGeneralSpinHorizontalExceptionalTailRestrictedPrincipalBlockHomeomorph
          S g).1)) v.1 = (g.2 v).1
  rw [hvComponent]
  exact
    V.cliffordGeneralSpinHorizontalExceptionalTailToRestrictedPrincipalBlock_apply_notMem
      S g v.1 v.2

namespace AnisotropicComplementPresentation

set_option synthInstance.maxHeartbeats 500000
set_option maxHeartbeats 1600000

variable {n m : ℕ}
variable {V : RationalQuadraticSpaceMatrix n} {x : Fin n → ℚ}
variable (P : V.AnisotropicComplementPresentation x m)

/-! ## Common exceptional overlap and the two native cylinder sources -/

private def ambientExceptionalPlaceInSupport
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    {S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)}
    (hS : P.IsHorizontalIntegralTailPresentationSupport hx S)
    (v : {v // v ∈ S ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces}) :
    {v // v ∈ S} :=
  ⟨v.1,
    (Finset.mem_union.mp v.2).elim (fun hv ↦ hv) (fun hv ↦ hS.2.1 hv)⟩

private def blockExceptionalPlaceInSupport
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    {S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)}
    (hS : P.IsHorizontalIntegralTailPresentationSupport hx S)
    (v : {v // v ∈ S ∪
      (P.blockSpace hx).cliffordGeneralSpinHorizontalIntegralBadPlaces}) :
    {v // v ∈ S} :=
  ⟨v.1,
    (Finset.mem_union.mp v.2).elim (fun hv ↦ hv) (fun hv ↦ hS.1 hv)⟩

/-- Forget the common source-overlap proof in every exceptional ambient
coordinate. -/
def ambientFiniteExceptionalOverlapToExceptionalProduct
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    {S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)}
    (hS : P.IsHorizontalIntegralTailPresentationSupport hx S) :
    P.FiniteExceptionalPadicCentralFiberSourceOverlap S hx →
      V.CliffordGeneralSpinHorizontalExceptionalProduct S :=
  fun g v ↦ (g (P.ambientExceptionalPlaceInSupport hx hS v)).1

theorem measurable_ambientFiniteExceptionalOverlapToExceptionalProduct
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    {S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)}
    (hS : P.IsHorizontalIntegralTailPresentationSupport hx S) :
    Measurable (P.ambientFiniteExceptionalOverlapToExceptionalProduct hx hS) := by
  exact measurable_pi_lambda _ fun v ↦
    continuous_subtype_val.measurable.comp
      (measurable_pi_apply (P.ambientExceptionalPlaceInSupport hx hS v))

/-- Convert every common ambient source-overlap point back to the native block
coordinate at the corresponding exceptional place. -/
def blockFiniteExceptionalOverlapToExceptionalProduct
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    {S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)}
    (hS : P.IsHorizontalIntegralTailPresentationSupport hx S) :
    P.FiniteExceptionalPadicCentralFiberSourceOverlap S hx →
      (P.blockSpace hx).CliffordGeneralSpinHorizontalExceptionalProduct S :=
  fun g v ↦
    P.ambientToBlockGeneralSpinIntrinsicPoint
      ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1] hx
      (g (P.blockExceptionalPlaceInSupport hx hS v)).1

theorem measurable_blockFiniteExceptionalOverlapToExceptionalProduct
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    {S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)}
    (hS : P.IsHorizontalIntegralTailPresentationSupport hx S) :
    Measurable (P.blockFiniteExceptionalOverlapToExceptionalProduct hx hS) := by
  exact measurable_pi_lambda _ fun v ↦
    (P.blockToAmbientGeneralSpinContinuousMulEquiv hx
      ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1]).symm.continuous.measurable.comp
        (continuous_subtype_val.measurable.comp
          (measurable_pi_apply (P.blockExceptionalPlaceInSupport hx hS v)))

/-- The common overlap coordinates together with the native block integral
tail. -/
abbrev BlockFiniteAdelicPresentationOverlapCylinderSource
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :=
  P.FiniteExceptionalPadicCentralFiberSourceOverlap S hx ×
    (P.blockSpace hx).CliffordGeneralSpinHorizontalIntegralTail S

/-- The corresponding ambient source uses the same exceptional overlap and
the ambient integral tail. -/
abbrev AmbientFiniteAdelicPresentationOverlapCylinderSource
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :=
  P.FiniteExceptionalPadicCentralFiberSourceOverlap S hx ×
    V.CliffordGeneralSpinHorizontalIntegralTail S

/-- Identity on the common exceptional overlap, together with the already
certified normalized tail equivalence. -/
def finiteAdelicPresentationOverlapCylinderSourceMeasurableEquiv
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    {S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)}
    (hS : P.IsHorizontalIntegralTailPresentationSupport hx S) :
    P.BlockFiniteAdelicPresentationOverlapCylinderSource S hx ≃ᵐ
      P.AmbientFiniteAdelicPresentationOverlapCylinderSource S hx :=
  MeasurableEquiv.prodCongr (MeasurableEquiv.refl _)
    (P.blockToAmbientHorizontalIntegralTailMeasurableEquiv hx hS)

/-- Assemble the block exceptional coordinates and block tail through the
existing native finite-adelic cylinder map. -/
def blockFiniteAdelicPresentationOverlapCylinderToFiniteAdeles
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    {S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)}
    (hS : P.IsHorizontalIntegralTailPresentationSupport hx S) :
    P.BlockFiniteAdelicPresentationOverlapCylinderSource S hx →
      (P.blockSpace hx).FiniteAdelicCliffordGeneralSpinGroup :=
  fun g ↦
    (P.blockSpace hx).cliffordGeneralSpinHorizontalIdentityChartSourceToAmbient S
      (P.blockFiniteExceptionalOverlapToExceptionalProduct hx hS g.1, g.2)

theorem measurable_blockFiniteAdelicPresentationOverlapCylinderToFiniteAdeles
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    {S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)}
    (hS : P.IsHorizontalIntegralTailPresentationSupport hx S) :
    Measurable (P.blockFiniteAdelicPresentationOverlapCylinderToFiniteAdeles hx hS) := by
  exact ((P.blockSpace hx)
    |>.measurable_cliffordGeneralSpinHorizontalIdentityChartSourceToAmbient S).comp
      ((P.measurable_blockFiniteExceptionalOverlapToExceptionalProduct hx hS
        |>.prodMap measurable_id))

/-- Assemble the ambient exceptional coordinates and ambient tail through the
same existing native finite-adelic cylinder map. -/
def ambientFiniteAdelicPresentationOverlapCylinderToFiniteAdeles
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    {S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)}
    (hS : P.IsHorizontalIntegralTailPresentationSupport hx S) :
    P.AmbientFiniteAdelicPresentationOverlapCylinderSource S hx →
      V.FiniteAdelicCliffordGeneralSpinGroup :=
  fun g ↦ V.cliffordGeneralSpinHorizontalIdentityChartSourceToAmbient S
    (P.ambientFiniteExceptionalOverlapToExceptionalProduct hx hS g.1, g.2)

theorem measurable_ambientFiniteAdelicPresentationOverlapCylinderToFiniteAdeles
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    {S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)}
    (hS : P.IsHorizontalIntegralTailPresentationSupport hx S) :
    Measurable (P.ambientFiniteAdelicPresentationOverlapCylinderToFiniteAdeles hx hS) := by
  exact V.measurable_cliffordGeneralSpinHorizontalIdentityChartSourceToAmbient S |>.comp
    ((P.measurable_ambientFiniteExceptionalOverlapToExceptionalProduct hx hS
      |>.prodMap measurable_id))

/-! ## Source and finite-adelic transport -/

theorem blockToAmbientFiniteAdelicPresentationOverlapCylinder_commutes
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    {S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)}
    (hS : P.IsHorizontalIntegralTailPresentationSupport hx S)
    (g : P.BlockFiniteAdelicPresentationOverlapCylinderSource S hx) :
    P.blockToAmbientFiniteAdelicGeneralSpinContinuousMulEquiv hx
        (P.blockFiniteAdelicPresentationOverlapCylinderToFiniteAdeles hx hS g) =
      P.ambientFiniteAdelicPresentationOverlapCylinderToFiniteAdeles hx hS
        (P.finiteAdelicPresentationOverlapCylinderSourceMeasurableEquiv hx hS g) := by
  apply V.finiteAdelicCliffordGeneralSpinHeightOneComponentsHom_injective
  funext v
  change V.finiteAdelicCliffordGeneralSpinHeightOneComponentHom v
      (P.blockToAmbientFiniteAdelicGeneralSpinContinuousMulEquiv hx
        (P.blockFiniteAdelicPresentationOverlapCylinderToFiniteAdeles hx hS g)) =
    V.finiteAdelicCliffordGeneralSpinHeightOneComponentHom v
      (P.ambientFiniteAdelicPresentationOverlapCylinderToFiniteAdeles hx hS
        (P.finiteAdelicPresentationOverlapCylinderSourceMeasurableEquiv hx hS g))
  rw [P.blockToAmbientFiniteAdelicGeneralSpin_heightOneComponent_commutes]
  by_cases hvS : v ∈ S
  · let vb : {v // v ∈ S ∪
        (P.blockSpace hx).cliffordGeneralSpinHorizontalIntegralBadPlaces} :=
      ⟨v, Finset.mem_union_left _ hvS⟩
    let va : {v // v ∈ S ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces} :=
      ⟨v, Finset.mem_union_left _ hvS⟩
    change P.blockToAmbientGeneralSpinIntrinsicPoint
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1] hx
          ((P.blockSpace hx).finiteAdelicCliffordGeneralSpinHeightOneComponentHom v
            ((P.blockSpace hx)
              |>.cliffordGeneralSpinHorizontalIdentityChartSourceToAmbient S
                (P.blockFiniteExceptionalOverlapToExceptionalProduct hx hS g.1,
                  g.2))) =
      V.finiteAdelicCliffordGeneralSpinHeightOneComponentHom v
        (V.cliffordGeneralSpinHorizontalIdentityChartSourceToAmbient S
          (P.ambientFiniteExceptionalOverlapToExceptionalProduct hx hS g.1,
            P.blockToAmbientHorizontalIntegralTailMeasurableEquiv hx hS g.2))
    rw [(P.blockSpace hx)
      |>.cliffordGeneralSpinHorizontalIdentityChartSourceToAmbient_component_of_mem
        S _ v vb.2]
    rw [V.cliffordGeneralSpinHorizontalIdentityChartSourceToAmbient_component_of_mem
      S _ v va.2]
    change P.blockToAmbientGeneralSpinIntrinsicPoint
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1] hx
          (P.ambientToBlockGeneralSpinIntrinsicPoint
            ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1] hx
            (g.1 ⟨v, hvS⟩).1) = (g.1 ⟨v, hvS⟩).1
    exact P.blockToAmbientGeneralSpinIntrinsicPoint_ambientToBlock
      ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1] hx _
  · let w : V.CliffordGeneralSpinHorizontalIntegralPlace S :=
      ⟨v, by
        intro hv
        rcases Finset.mem_union.mp hv with hvS' | hvBad
        · exact hvS hvS'
        · exact hvS (hS.2.1 hvBad)⟩
    let u := (P.blockToAmbientHorizontalIntegralPlaceEquiv hx hS).symm w
    change P.blockToAmbientGeneralSpinIntrinsicPoint
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv u.1).1] hx
          ((P.blockSpace hx).finiteAdelicCliffordGeneralSpinHeightOneComponentHom
            u.1 ((P.blockSpace hx)
              |>.cliffordGeneralSpinHorizontalIdentityChartSourceToAmbient S
                (P.blockFiniteExceptionalOverlapToExceptionalProduct hx hS g.1,
                  g.2))) =
      V.finiteAdelicCliffordGeneralSpinHeightOneComponentHom w.1
        (V.cliffordGeneralSpinHorizontalIdentityChartSourceToAmbient S
          (P.ambientFiniteExceptionalOverlapToExceptionalProduct hx hS g.1,
            P.blockToAmbientHorizontalIntegralTailMeasurableEquiv hx hS g.2))
    rw [(P.blockSpace hx)
      |>.cliffordGeneralSpinHorizontalIdentityChartSourceToAmbient_component_of_notMem
        S _ u]
    rw [V.cliffordGeneralSpinHorizontalIdentityChartSourceToAmbient_component_of_notMem
      S _ w]
    change P.blockToAmbientGeneralSpinIntrinsicPoint
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv u.1).1] hx (g.2 u).1 =
      ((P.blockToAmbientHorizontalIntegralTailMeasurableEquiv hx hS g.2) w).1
    rw [P.blockToAmbientHorizontalIntegralTailMeasurableEquiv_apply hx hS g.2 w]
    rfl

/-- Product of the transported exceptional overlap measure and the normalized
block tail. -/
def transportedFiniteAdelicPresentationOverlapCylinderSourceMeasure
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    Measure (P.BlockFiniteAdelicPresentationOverlapCylinderSource S hx) :=
  (P.transportedFiniteExceptionalPadicCentralFiberSourceOverlapMeasure S hx).prod
    ((P.blockSpace hx).cliffordGeneralSpinHorizontalNormalizedIntegralTailMeasure S)

/-- Product of the ambient exceptional overlap measure and the normalized
ambient tail. -/
def ambientFiniteAdelicPresentationOverlapCylinderSourceMeasure
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    Measure (P.AmbientFiniteAdelicPresentationOverlapCylinderSource S hx) :=
  (P.ambientFiniteExceptionalPadicCentralFiberSourceOverlapMeasure S hx).prod
    (V.cliffordGeneralSpinHorizontalNormalizedIntegralTailMeasure S)

local instance transportedFiniteAdelicPresentationOverlapCylinderExceptionalMeasureSigmaFinite
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hx : V.nativeRationalQuadraticForm x ≠ 0) :
    SigmaFinite
      (P.transportedFiniteExceptionalPadicCentralFiberSourceOverlapMeasure S hx) :=
  Measure.pi.sigmaFinite _

/-- The complete exceptional-overlap/tail source measure transports by the
finite product of reciprocal local presentation moduli. -/
theorem map_transportedFiniteAdelicPresentationOverlapCylinderSourceMeasure
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    {S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)}
    (hS : P.IsHorizontalIntegralTailPresentationSupport hx S) :
    Measure.map
        (P.finiteAdelicPresentationOverlapCylinderSourceMeasurableEquiv hx hS)
        (P.transportedFiniteAdelicPresentationOverlapCylinderSourceMeasure S hx) =
      P.finiteExceptionalPadicPresentationModulus S hx •
        P.ambientFiniteAdelicPresentationOverlapCylinderSourceMeasure S hx := by
  unfold transportedFiniteAdelicPresentationOverlapCylinderSourceMeasure
    ambientFiniteAdelicPresentationOverlapCylinderSourceMeasure
  change Measure.map
      (Prod.map id
        (P.blockToAmbientHorizontalIntegralTailMeasurableEquiv hx hS))
      ((P.transportedFiniteExceptionalPadicCentralFiberSourceOverlapMeasure S hx).prod
        ((P.blockSpace hx)
          |>.cliffordGeneralSpinHorizontalNormalizedIntegralTailMeasure S)) =
    P.finiteExceptionalPadicPresentationModulus S hx •
      (P.ambientFiniteExceptionalPadicCentralFiberSourceOverlapMeasure S hx).prod
        (V.cliffordGeneralSpinHorizontalNormalizedIntegralTailMeasure S)
  rw [← Measure.map_prod_map _ _ measurable_id
    (P.blockToAmbientHorizontalIntegralTailMeasurableEquiv hx hS).measurable]
  rw [Measure.map_id,
    P.transportedFiniteExceptionalPadicCentralFiberSourceOverlapMeasure_eq_smul S hx,
    (P.blockToAmbientHorizontalIntegralTail_measurePreserving hx hS).map_eq]
  exact Measure.prod_smul_left _

/-- The block and ambient finite-adelic overlap-cylinder measures formed with
the existing native assembly maps. -/
def transportedFiniteAdelicPresentationOverlapCylinderMeasure
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    {S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)}
    (hS : P.IsHorizontalIntegralTailPresentationSupport hx S) :
    Measure (P.blockSpace hx).FiniteAdelicCliffordGeneralSpinGroup :=
  Measure.map
    (P.blockFiniteAdelicPresentationOverlapCylinderToFiniteAdeles hx hS)
    (P.transportedFiniteAdelicPresentationOverlapCylinderSourceMeasure S hx)

def ambientFiniteAdelicPresentationOverlapCylinderMeasure
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    {S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)}
    (hS : P.IsHorizontalIntegralTailPresentationSupport hx S) :
    Measure V.FiniteAdelicCliffordGeneralSpinGroup :=
  Measure.map
    (P.ambientFiniteAdelicPresentationOverlapCylinderToFiniteAdeles hx hS)
    (P.ambientFiniteAdelicPresentationOverlapCylinderSourceMeasure S hx)

/-- Presentation transport carries the assembled block overlap cylinder by
the exact finite product of reciprocal local moduli. -/
theorem map_transportedFiniteAdelicPresentationOverlapCylinderMeasure
    (hx : V.nativeRationalQuadraticForm x ≠ 0)
    {S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)}
    (hS : P.IsHorizontalIntegralTailPresentationSupport hx S) :
    Measure.map (P.blockToAmbientFiniteAdelicGeneralSpinContinuousMulEquiv hx)
        (P.transportedFiniteAdelicPresentationOverlapCylinderMeasure hx hS) =
      P.finiteExceptionalPadicPresentationModulus S hx •
        P.ambientFiniteAdelicPresentationOverlapCylinderMeasure hx hS := by
  let e := P.finiteAdelicPresentationOverlapCylinderSourceMeasurableEquiv hx hS
  let f := P.blockFiniteAdelicPresentationOverlapCylinderToFiniteAdeles hx hS
  let F := P.blockToAmbientFiniteAdelicGeneralSpinContinuousMulEquiv hx
  let g := P.ambientFiniteAdelicPresentationOverlapCylinderToFiniteAdeles hx hS
  let μ := P.transportedFiniteAdelicPresentationOverlapCylinderSourceMeasure S hx
  let ν := P.ambientFiniteAdelicPresentationOverlapCylinderSourceMeasure S hx
  let q := P.finiteExceptionalPadicPresentationModulus S hx
  have hf : Measurable f :=
    P.measurable_blockFiniteAdelicPresentationOverlapCylinderToFiniteAdeles hx hS
  have hg : Measurable g :=
    P.measurable_ambientFiniteAdelicPresentationOverlapCylinderToFiniteAdeles hx hS
  have hcomm : F ∘ f = g ∘ e := by
    funext z
    exact P.blockToAmbientFiniteAdelicPresentationOverlapCylinder_commutes hx hS z
  unfold transportedFiniteAdelicPresentationOverlapCylinderMeasure
    ambientFiniteAdelicPresentationOverlapCylinderMeasure
  calc
    Measure.map F (Measure.map f μ) = Measure.map (F ∘ f) μ := by
      simpa only using Measure.map_map F.continuous.measurable hf
    _ = Measure.map (g ∘ e) μ := by rw [hcomm]
    _ = Measure.map g (Measure.map e μ) := by
      simpa only using (Measure.map_map hg e.measurable).symm
    _ = Measure.map g (q • ν) := by
      rw [P.map_transportedFiniteAdelicPresentationOverlapCylinderSourceMeasure hx hS]
    _ = q • Measure.map g ν := by rw [Measure.map_smul]

end AnisotropicComplementPresentation
end RationalQuadraticSpaceMatrix

end
