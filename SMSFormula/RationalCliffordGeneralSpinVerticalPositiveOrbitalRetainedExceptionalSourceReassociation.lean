import SMSFormula.RationalCliffordGeneralSpinVerticalPositiveOrbitalRetainedTailScalarReassociation

/-!
# Reassociate the retained exceptional Spin source

The normalized retained cylinder presents its exceptional Spin coordinate in
the ambient admissible exceptional product, restricted to the literal
identity-chart carrier.  This file exposes that restricted measure as the
finite product of the already existing local identity-chart source
pushforwards.  This is the source-level form used by the remaining
nonnegative-integral reassociation; no dependent global `comap`, new chart, or
normalization is introduced.
-/

noncomputable section

open MeasureTheory

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

local instance retainedExceptionalSourceDecidableEq :
    DecidableEq (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  Classical.decEq _

local instance retainedExceptionalSourcePrimeFact
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

/-- Restriction to the retained exceptional identity carrier is literally the
finite product of the existing local Spin identity-chart source
pushforwards.  In particular, this source transport has coefficient one. -/
theorem finiteAdelicCliffordSpinCandidateAdmissibleExceptionalProductMeasure_restrict_retainedCarrier_eq_pi_map
    (B : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    (V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalProductMeasure B).restrict
        (V.retainedSpinExceptionalIdentityCarrier B) =
      Measure.pi fun v : {v //
          v ∈ V.cliffordSpinCandidateAdmissibleExceptionalPlaces B} =>
        Measure.map Subtype.val
          (V.padicCliffordSpinCandidateIdentityChartSourceMeasure
            (Rat.HeightOneSpectrum.primesEquiv v.1).1) := by
  rw [finiteAdelicCliffordSpinCandidateAdmissibleExceptionalProductMeasure,
    retainedSpinExceptionalIdentityCarrier, Measure.restrict_pi_pi]
  congr 1
  funext v
  symm
  simpa only [
    heightOnePadicCliffordSpinCandidateChartGluedGroupMeasure] using
      V.map_padicCliffordSpinCandidateIdentityChartSourceMeasure_subtypeVal
        (Rat.HeightOneSpectrum.primesEquiv v.1).1

/-- Nonnegative-integral change of variables for the retained exceptional
source.  The index type is deliberately left as the admissible exceptional
set; the later horizontal reassociation may reindex it only after the local
chart coordinates have been exposed. -/
theorem lintegral_finiteAdelicCliffordSpinCandidateAdmissibleExceptionalProductMeasure_restrict_retainedCarrier
    (B : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (f : V.FiniteAdelicCliffordSpinCandidateAdmissibleExceptionalProduct B → ENNReal)
    (hf : Measurable f) :
    (∫⁻ x, f x
      ∂(V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalProductMeasure B).restrict
        (V.retainedSpinExceptionalIdentityCarrier B)) =
      ∫⁻ x, f (fun v => (x v : V.HeightOnePadicCliffordSpinCandidateGroup v.1))
        ∂Measure.pi fun v : {v //
            v ∈ V.cliffordSpinCandidateAdmissibleExceptionalPlaces B} =>
          V.padicCliffordSpinCandidateIdentityChartSourceMeasure
            (Rat.HeightOneSpectrum.primesEquiv v.1).1 := by
  let I := {v // v ∈ V.cliffordSpinCandidateAdmissibleExceptionalPlaces B}
  let μ := fun v : I =>
    V.padicCliffordSpinCandidateIdentityChartSourceMeasure
      (Rat.HeightOneSpectrum.primesEquiv v.1).1
  let ι := fun v : I =>
    fun x : (V.padicCliffordSpinCandidateIdentityChart
      (Rat.HeightOneSpectrum.primesEquiv v.1).1).source =>
        (x : V.HeightOnePadicCliffordSpinCandidateGroup v.1)
  let g := fun x : ∀ v : I, (V.padicCliffordSpinCandidateIdentityChart
      (Rat.HeightOneSpectrum.primesEquiv v.1).1).source =>
    fun v : I => ι v (x v)
  letI (v : I) : SigmaFinite ((μ v).map (ι v)) := by
    rw [show (μ v).map (ι v) =
      (V.heightOnePadicCliffordSpinCandidateChartGluedGroupMeasure v.1).restrict
        (V.padicCliffordSpinCandidateIdentityChart
          (Rat.HeightOneSpectrum.primesEquiv v.1).1).source by
      simpa only [μ, ι,
        heightOnePadicCliffordSpinCandidateChartGluedGroupMeasure] using
          V.map_padicCliffordSpinCandidateIdentityChartSourceMeasure_subtypeVal
            (Rat.HeightOneSpectrum.primesEquiv v.1).1]
    infer_instance
  have hg : Measurable g := by
    apply measurable_pi_lambda
    intro v
    exact continuous_subtype_val.measurable.comp (measurable_pi_apply _)
  have hpi :
      (Measure.pi μ).map g =
        Measure.pi fun v => (μ v).map (ι v) :=
    Measure.pi_map_pi fun v => continuous_subtype_val.measurable.aemeasurable
  rw [V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalProductMeasure_restrict_retainedCarrier_eq_pi_map
    B, ← hpi]
  exact lintegral_map hf hg

end RationalQuadraticSpaceMatrix

namespace PositiveDefiniteIntegralLattice

variable {r : ℕ}

local instance retainedExceptionalSourceIntegralDecidableEq :
    DecidableEq (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  Classical.decEq _

local instance retainedExceptionalSourceIntegralPrimeFact
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

/-- Include the existing horizontal exceptional Spin chart source into the
admissible exceptional product.  The retained admissible-place theorem
supplies the index conversion; no representative is chosen. -/
def retainedExceptionalSpinChartSourceToAdmissibleProduct
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    let V := L.rationalQuadraticSpaceMatrix
    let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
    let B := E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
    V.CliffordGeneralSpinHorizontalExceptionalSOChartSource B →
      V.FiniteAdelicCliffordSpinCandidateAdmissibleExceptionalProduct B := by
  let V := L.rationalQuadraticSpaceMatrix
  let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
  let B := E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
  exact fun x v => by
    let w : {w // w ∈ B} := ⟨v.1, by
      have hv := v.2
      simpa only [L.cliffordSpinCandidateAdmissibleExceptionalPlaces_retainedHorizontal_eq S]
        using hv⟩
    exact (x w).1

theorem measurable_retainedExceptionalSpinChartSourceToAdmissibleProduct
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Measurable (L.retainedExceptionalSpinChartSourceToAdmissibleProduct S) := by
  unfold retainedExceptionalSpinChartSourceToAdmissibleProduct
  apply measurable_pi_lambda
  intro v
  exact continuous_subtype_val.measurable.comp (measurable_pi_apply _)

/-- Componentwise, the totalized retained chart recovers a point of
the horizontal exceptional chart source after the source inclusion. -/
theorem retainedExceptionalSpinIdentityChartTotal_sourceToAdmissibleProduct_apply
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (x : let V := L.rationalQuadraticSpaceMatrix
      let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
      let B := E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
      V.CliffordGeneralSpinHorizontalExceptionalSOChartSource B)
    (v : {v // v ∈
      L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S ∪
        L.rationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalIntegralBadPlaces}) :
    L.retainedExceptionalSpinIdentityChartTotal S
        (L.retainedExceptionalSpinChartSourceToAdmissibleProduct S x) v = x v := by
  apply Subtype.ext
  unfold retainedExceptionalSpinIdentityChartTotal retainedExceptionalSpinIdentityChartValue
    retainedExceptionalSpinChartSourceToAdmissibleProduct
  dsimp only
  rw [dif_pos]
  exact (x v).2

/-- The preceding coefficient-one source identity specialized to the retained
horizontal block used in the vertical cylinder. -/
theorem retainedExceptionalSpinSource_restrict_eq_pi_map
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    let V := L.rationalQuadraticSpaceMatrix
    let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
    let B := E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
    (V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalProductMeasure B).restrict
        (V.retainedSpinExceptionalIdentityCarrier B) =
      Measure.pi fun v : {v //
          v ∈ V.cliffordSpinCandidateAdmissibleExceptionalPlaces B} =>
        Measure.map Subtype.val
          (V.padicCliffordSpinCandidateIdentityChartSourceMeasure
            (Rat.HeightOneSpectrum.primesEquiv v.1).1) := by
  exact L.rationalQuadraticSpaceMatrix
    |>.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalProductMeasure_restrict_retainedCarrier_eq_pi_map _

/-- Retained-block specialization of the integral-level exceptional source
change of variables. -/
theorem lintegral_retainedExceptionalSpinSource
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (f : let V := L.rationalQuadraticSpaceMatrix
      let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
      let B := E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
      V.FiniteAdelicCliffordSpinCandidateAdmissibleExceptionalProduct B → ENNReal)
    (hf : Measurable f) :
    let V := L.rationalQuadraticSpaceMatrix
    let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
    let B := E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
    (∫⁻ x, f x
      ∂(V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalProductMeasure B).restrict
        (V.retainedSpinExceptionalIdentityCarrier B)) =
      ∫⁻ x, f (fun v => (x v : V.HeightOnePadicCliffordSpinCandidateGroup v.1))
        ∂Measure.pi fun v : {v //
            v ∈ V.cliffordSpinCandidateAdmissibleExceptionalPlaces B} =>
          V.padicCliffordSpinCandidateIdentityChartSourceMeasure
            (Rat.HeightOneSpectrum.primesEquiv v.1).1 := by
  dsimp only
  exact L.rationalQuadraticSpaceMatrix
    |>.lintegral_finiteAdelicCliffordSpinCandidateAdmissibleExceptionalProductMeasure_restrict_retainedCarrier
      _ f hf

set_option backward.isDefEq.respectTransparency false in
/-- The retained exceptional restriction integrates exactly as the
horizontal exceptional Spin chart source. -/
theorem lintegral_retainedExceptionalSpinSource_to_horizontalChart
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (f : let V := L.rationalQuadraticSpaceMatrix
      let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
      let B := E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
      V.FiniteAdelicCliffordSpinCandidateAdmissibleExceptionalProduct B → ENNReal)
    (hf : Measurable f) :
    let V := L.rationalQuadraticSpaceMatrix
    let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
    let B := E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
    (∫⁻ x, f x
      ∂(V.finiteAdelicCliffordSpinCandidateAdmissibleExceptionalProductMeasure B).restrict
        (V.retainedSpinExceptionalIdentityCarrier B)) =
      ∫⁻ x, f (L.retainedExceptionalSpinChartSourceToAdmissibleProduct S x)
        ∂V.cliffordGeneralSpinHorizontalExceptionalSOChartSourceMeasure B := by
  dsimp only
  let V := L.rationalQuadraticSpaceMatrix
  let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
  let B := E ∪ V.cliffordGeneralSpinHorizontalIntegralBadPlaces
  let A := V.cliffordSpinCandidateAdmissibleExceptionalPlaces B
  let I := {v // v ∈ A}
  let J := {v // v ∈ B}
  have hAB : A = B := by
    simpa only [A, B] using
      L.cliffordSpinCandidateAdmissibleExceptionalPlaces_retainedHorizontal_eq S
  let e : J ≃ I :=
    { toFun := fun v => ⟨v.1, by
        have hv := v.2
        simpa only [hAB] using hv⟩
      invFun := fun v => ⟨v.1, by
        have hv := v.2
        simpa only [hAB] using hv⟩
      left_inv := fun v => Subtype.ext rfl
      right_inv := fun v => Subtype.ext rfl }
  let α : I → Type := fun v =>
    ↥(V.padicCliffordSpinCandidateIdentityChart
      (Rat.HeightOneSpectrum.primesEquiv v.1).1).source
  let μ := fun v : I =>
    V.padicCliffordSpinCandidateIdentityChartSourceMeasure
      (Rat.HeightOneSpectrum.primesEquiv v.1).1
  letI (v : I) : SigmaFinite (μ v) := by
    let p := (Rat.HeightOneSpectrum.primesEquiv v.1).1
    let spinChart := V.padicCliffordSpinCandidateIdentityChart p
    letI : SigmaFinite (V.padicInvariantDifferentialGroupMeasure p) :=
      PositiveDefiniteIntegralLattice.padicCayleySpecialOrthogonalDifferentialMeasure_sigmaFinite
        p (r + 2) V.pairingMatrix V.form_symm V.form_det_ne_zero
    letI : SigmaFinite
        (V.padicCliffordSpinCandidateIdentityChartTargetMeasure p) := by
      apply SigmaFinite.of_map _ continuous_subtype_val.measurable.aemeasurable
      rw [RationalQuadraticSpaceMatrix.padicCliffordSpinCandidateIdentityChartTargetMeasure,
        map_comap_subtype_coe spinChart.open_target.measurableSet]
      infer_instance
    rw [show μ v = V.padicCliffordSpinCandidateIdentityChartSourceMeasure p by rfl,
      RationalQuadraticSpaceMatrix.padicCliffordSpinCandidateIdentityChartSourceMeasure]
    exact spinChart.toHomeomorphSourceTarget.symm.toMeasurableEquiv.sigmaFinite_map
  let reindex := MeasurableEquiv.piCongrLeft α e
  let F : (∀ v, α v) → ENNReal := fun x =>
    f (fun v => (x v : V.HeightOnePadicCliffordSpinCandidateGroup v.1))
  have hambient : Measurable (fun x : ∀ v, α v =>
      fun v => (x v : V.HeightOnePadicCliffordSpinCandidateGroup v.1)) := by
    apply measurable_pi_lambda
    intro v
    exact continuous_subtype_val.measurable.comp (measurable_pi_apply _)
  have hF : Measurable F := hf.comp hambient
  have hreindex :
      (Measure.pi fun v : J => μ (e v)).map reindex = Measure.pi μ :=
    (MeasureTheory.measurePreserving_piCongrLeft μ e).map_eq
  rw [V.lintegral_finiteAdelicCliffordSpinCandidateAdmissibleExceptionalProductMeasure_restrict_retainedCarrier
    B f hf]
  change (∫⁻ x, F x ∂Measure.pi μ) = _
  calc
    (∫⁻ x, F x ∂Measure.pi μ) =
        ∫⁻ x, F x ∂(Measure.pi fun v : J => μ (e v)).map reindex := by
      rw [hreindex]
    _ = ∫⁻ x, F (reindex x) ∂Measure.pi fun v : J => μ (e v) :=
      lintegral_map hF reindex.measurable
    _ = ∫⁻ x, f (L.retainedExceptionalSpinChartSourceToAdmissibleProduct S x)
          ∂V.cliffordGeneralSpinHorizontalExceptionalSOChartSourceMeasure B := by
      congr 1

end PositiveDefiniteIntegralLattice

end
