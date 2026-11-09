import SMSFormula.RationalQuadraticIsometrySpinCandidateGeneralFiniteSourceMeasureTransport
import SMSFormula.RationalQuadraticIsometrySpinCandidateFiniteCarrierTransport

/-!
# Finite Spin carrier transport under an arbitrary rational isometry

The canonical raw exceptional/good source is assembled into the existing
genuine finite-adelic Spin carrier.  This module proves that assembly commutes
with a supplied arbitrary rational isometry and transports the coherent
supported carrier measure by the exact source scalar.

No new finite carrier, chart, lattice, quotient measure, or scalar-one
normalization is introduced.
-/

noncomputable section

open MeasureTheory PositiveDefiniteIntegralLattice
open scoped ENNReal

namespace RationalQuadraticSpaceMatrix

set_option synthInstance.maxHeartbeats 700000
set_option maxHeartbeats 200000

variable {m : ℕ}
variable (W Z : RationalQuadraticSpaceMatrix (m + 1))
variable (e : W.quadraticForm.IsometryEquiv Z.quadraticForm)

local instance generalFiniteCarrierDecidableEq :
    DecidableEq (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  Classical.decEq _

local instance generalFiniteCarrierPrimeFact
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

local instance generalFiniteCarrierGroupMeasurableSpace
    (V : RationalQuadraticSpaceMatrix (m + 1)) :
    MeasurableSpace V.FiniteAdelicCliffordSpinCandidateGroup :=
  borel _

local instance generalFiniteCarrierGroupBorelSpace
    (V : RationalQuadraticSpaceMatrix (m + 1)) :
    BorelSpace V.FiniteAdelicCliffordSpinCandidateGroup :=
  ⟨rfl⟩

/-! ## Raw source assembly -/

/-- Assemble the canonical raw exceptional/good source through the already
fixed native source and genuine finite-adelic carrier. -/
def spinCandidateRawExceptionalTailToFiniteAdeles
    (V : RationalQuadraticSpaceMatrix (m + 1))
    {S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)}
    (hV : V.cliffordSpinCandidateAdmissibleBadPlaces ⊆ S) :
    (V.SpinCandidateRawExceptionalProduct S × V.SpinCandidateRawGoodTail S) →
      V.FiniteAdelicCliffordSpinCandidateGroup :=
  V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailToFiniteAdeles S ∘
    (V.cliffordSpinCandidateAdmissibleExceptionalTailSourceRawMeasurableEquiv
      hV).symm

theorem measurable_spinCandidateRawExceptionalTailToFiniteAdeles
    (V : RationalQuadraticSpaceMatrix (m + 1))
    {S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)}
    (hV : V.cliffordSpinCandidateAdmissibleBadPlaces ⊆ S) :
    Measurable (V.spinCandidateRawExceptionalTailToFiniteAdeles hV) := by
  exact
    (V.measurable_finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailToFiniteAdeles
      S).comp
      (V.cliffordSpinCandidateAdmissibleExceptionalTailSourceRawMeasurableEquiv
        hV).symm.measurable

theorem spinCandidateRawExceptionalTailToFiniteAdeles_component_of_mem
    (V : RationalQuadraticSpaceMatrix (m + 1))
    {S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)}
    (hV : V.cliffordSpinCandidateAdmissibleBadPlaces ⊆ S)
    (g : V.SpinCandidateRawExceptionalProduct S ×
      V.SpinCandidateRawGoodTail S)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ)
    (hv : v ∈ S) :
  V.finiteAdelicCliffordSpinCandidateHeightOneComponentHom v
        (V.spinCandidateRawExceptionalTailToFiniteAdeles hV g) =
      g.1 ⟨v, hv⟩ := by
  unfold spinCandidateRawExceptionalTailToFiniteAdeles
  change
    V.finiteAdelicCliffordSpinCandidateHeightOneComponentHom v
        (V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailToFiniteAdeles
          S
          ((V.cliffordSpinCandidateAdmissibleExceptionalTailSourceRawMeasurableEquiv
            hV).symm g)) = _
  rw [V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailToFiniteAdeles_component_of_mem
    S _ v (Finset.mem_union_left _ hv)]
  rfl

theorem spinCandidateRawExceptionalTailToFiniteAdeles_component_of_notMem
    (V : RationalQuadraticSpaceMatrix (m + 1))
    {S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)}
    (hV : V.cliffordSpinCandidateAdmissibleBadPlaces ⊆ S)
    (g : V.SpinCandidateRawExceptionalProduct S ×
      V.SpinCandidateRawGoodTail S)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ)
    (hv : v ∉ S) :
    V.finiteAdelicCliffordSpinCandidateHeightOneComponentHom v
        (V.spinCandidateRawExceptionalTailToFiniteAdeles hV g) =
      (g.2 ⟨v, hv⟩).1 := by
  have hvNative :
      v ∉ V.cliffordSpinCandidateAdmissibleExceptionalPlaces S := by
    intro hv'
    rcases Finset.mem_union.mp hv' with hvS | hvBad
    · exact hv hvS
    · exact hv (hV hvBad)
  unfold spinCandidateRawExceptionalTailToFiniteAdeles
  change
    V.finiteAdelicCliffordSpinCandidateHeightOneComponentHom v
        (V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailToFiniteAdeles
          S
          ((V.cliffordSpinCandidateAdmissibleExceptionalTailSourceRawMeasurableEquiv
            hV).symm g)) = _
  rw [V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailToFiniteAdeles_component_of_notMem
    S _ v hvNative]
  rfl

/-- Raw source assembly recovers the existing supported genuine finite
carrier measure. -/
theorem map_spinCandidateRawExceptionalTailToFiniteAdeles
    (V : RationalQuadraticSpaceMatrix (m + 1))
    {S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)}
    (hV : V.cliffordSpinCandidateAdmissibleBadPlaces ⊆ S) :
    Measure.map (V.spinCandidateRawExceptionalTailToFiniteAdeles hV)
        (V.spinCandidateRawExceptionalTailSourceMeasure hV) =
      V.finiteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlockAmbientMeasure
        S := by
  let r :=
    V.cliffordSpinCandidateAdmissibleExceptionalTailSourceRawMeasurableEquiv hV
  let a :=
    V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailToFiniteAdeles S
  let μ :=
    V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailCylinderSourceMeasure
      S
  let ν := V.spinCandidateRawExceptionalTailSourceMeasure hV
  have hr : MeasurePreserving r μ ν :=
    V.cliffordSpinCandidateAdmissibleExceptionalTailSourceRaw_measurePreserving hV
  have hrSymm : MeasurePreserving r.symm ν μ :=
    MeasurePreserving.symm r hr
  have ha : Measurable a :=
    V.measurable_finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailToFiniteAdeles
      S
  change Measure.map (a ∘ r.symm) ν = _
  calc
    Measure.map (a ∘ r.symm) ν = Measure.map a (Measure.map r.symm ν) :=
      (Measure.map_map ha r.symm.measurable).symm
    _ = Measure.map a μ := by rw [hrSymm.map_eq]
    _ =
        V.finiteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlockAmbientMeasure
          S := V.map_finiteAdelicCliffordSpinCandidateAdmissibleExceptionalTailToFiniteAdeles S

/-- The coherently weighted raw source assembles to the fixed coherent
supported carrier measure. -/
theorem map_spinCandidateCoherentRawExceptionalTailToFiniteAdeles
    (V : RationalQuadraticSpaceMatrix (m + 1))
    {S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)}
    (hV : V.cliffordSpinCandidateAdmissibleBadPlaces ⊆ S) :
    Measure.map (V.spinCandidateRawExceptionalTailToFiniteAdeles hV)
        (V.finiteAdelicCliffordSpinCandidateAdmissibleBlockWeight S •
          V.spinCandidateRawExceptionalTailSourceMeasure hV) =
      V.finiteAdelicCliffordSpinCandidateCoherentGenuineAdmissiblePrincipalBlockAmbientMeasure
        S := by
  rw [Measure.map_smul, V.map_spinCandidateRawExceptionalTailToFiniteAdeles hV]
  exact
    (V.finiteAdelicCliffordSpinCandidateCoherentGenuineAdmissiblePrincipalBlockAmbientMeasure_eq_weight_smul
      S).symm

/-! ## Exact arbitrary-isometry carrier square -/

/-- Arbitrary-isometry Spin transport over the finite adeles commutes with
evaluation at every rational height-one place. -/
theorem rationalIsometryFiniteAdelicSpinCandidate_heightOneComponent_commutes
    (v : IsDedekindDomain.HeightOneSpectrum ℤ)
    (z : W.FiniteAdelicCliffordSpinCandidateGroup) :
    Z.finiteAdelicCliffordSpinCandidateHeightOneComponentHom v
        (rationalIsometrySpinCandidateContinuousMulEquiv
          W Z e RationalFiniteAdele z) =
      rationalIsometrySpinCandidateContinuousMulEquiv
        W Z e ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]
        (W.finiteAdelicCliffordSpinCandidateHeightOneComponentHom v z) := by
  exact (rationalIsometrySpinCandidateMulEquiv_naturality W Z e
    (finiteAdelicCliffordSpinCandidateHeightOneAlgHom v) z).symm

/-- Raw exceptional/good transport commutes exactly with assembly into the
genuine finite-adelic Spin carrier. -/
theorem rationalIsometrySpinCandidateRawExceptionalTailToFiniteAdeles_commutes
    {S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)}
    (hS : IsHorizontalIntegralTailRationalIsometrySupport W Z e S)
    (hW : W.cliffordSpinCandidateAdmissibleBadPlaces ⊆ S)
    (hZ : Z.cliffordSpinCandidateAdmissibleBadPlaces ⊆ S)
    (g : W.SpinCandidateRawExceptionalProduct S ×
      W.SpinCandidateRawGoodTail S) :
    rationalIsometrySpinCandidateContinuousMulEquiv W Z e RationalFiniteAdele
        (W.spinCandidateRawExceptionalTailToFiniteAdeles hW g) =
      Z.spinCandidateRawExceptionalTailToFiniteAdeles hZ
        (rationalIsometrySpinCandidateRawExceptionalTailSourceMeasurableEquiv
          W Z e hS hW hZ g) := by
  apply Z.finiteAdelicCliffordSpinCandidateHeightOneComponentsHom_injective
  funext v
  change
    Z.finiteAdelicCliffordSpinCandidateHeightOneComponentHom v
        (rationalIsometrySpinCandidateContinuousMulEquiv
          W Z e RationalFiniteAdele
          (W.spinCandidateRawExceptionalTailToFiniteAdeles hW g)) =
      Z.finiteAdelicCliffordSpinCandidateHeightOneComponentHom v
        (Z.spinCandidateRawExceptionalTailToFiniteAdeles hZ
          (rationalIsometrySpinCandidateRawExceptionalTailSourceMeasurableEquiv
            W Z e hS hW hZ g))
  rw [rationalIsometryFiniteAdelicSpinCandidate_heightOneComponent_commutes]
  by_cases hv : v ∈ S
  · rw [W.spinCandidateRawExceptionalTailToFiniteAdeles_component_of_mem
      hW g v hv]
    rw [Z.spinCandidateRawExceptionalTailToFiniteAdeles_component_of_mem
      hZ _ v hv]
    rfl
  · rw [W.spinCandidateRawExceptionalTailToFiniteAdeles_component_of_notMem
      hW g v hv]
    rw [Z.spinCandidateRawExceptionalTailToFiniteAdeles_component_of_notMem
      hZ _ v hv]
    rfl


end RationalQuadraticSpaceMatrix

end
