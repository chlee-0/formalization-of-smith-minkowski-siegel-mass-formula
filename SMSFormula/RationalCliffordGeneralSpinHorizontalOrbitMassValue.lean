import SMSFormula.RationalCliffordGeneralSpinHorizontalOrbitMassLocalDensity
import SMSFormula.RationalSpecialOrthogonalRealPositiveDefiniteMass

/-!
# The value of the orbit mass `N(O)`, and its positivity and finiteness

The orbit-mass identity through local orbit densities reads `N(O) · A = B` with
`A = μ_{SO_W}(univ) · ∏ s_W` and `B = μ_{SO_V}(univ) · ∏ s_V c_v`.  For positive-definite `W`
and `a > 0` both real masses are positive and finite (the evaluation
`μ(univ) · SP(n) = |e(F)| 2^n √|det F|^(n-1)` has positive right side and `SP(n) > 0`), and the
baseline scales are positive and finite.  Hence, for positive finite local densities `c_v`,

`N(O) = B / A`,  `0 < N(O) < ∞`.

This discharges the hypotheses `0 < N(O) < ∞` of the orbit Riesz ratio for the central-cutoff
orbit with integral completion.  Nothing is chosen.
-/

noncomputable section

open MeasureTheory Set PositiveDefiniteIntegralLattice
open scoped ENNReal

/-- A cross-multiplied identity with a positive finite factor determines the other factor. -/
theorem ENNReal.eq_div_of_mul_eq_of_ne {N A B : ℝ≥0∞} (h : N * A = B) (hA0 : A ≠ 0)
    (hAt : A ≠ ⊤) : N = B / A := by
  rw [ENNReal.eq_div_iff hA0 hAt, mul_comm, h]

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

local instance omvDecidableEq : DecidableEq (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  Classical.decEq _

local instance omvPrimeFact (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

/-- The real total mass of a positive-definite form is positive and finite. -/
theorem realInvariantDifferentialGroupMeasure_univ_ne_zero_ne_top
    (V : RationalQuadraticSpaceMatrix n) [NeZero n]
    (hpos : (V.pairingMatrix.map (algebraMap ℚ ℝ)).PosDef) :
    V.realInvariantDifferentialGroupMeasure Set.univ ≠ 0 ∧
      V.realInvariantDifferentialGroupMeasure Set.univ ≠ ⊤ := by
  have h := V.realInvariantDifferentialGroupMeasure_univ_mul_archimedeanFactor hpos
  have hSP : 0 < PositiveDefiniteIntegralLattice.archimedeanMassFactor n :=
    PositiveDefiniteIntegralLattice.archimedeanMassFactor_pos n
  have hX : 0 < |(Matrix.skewAdjointFixedFormElementaryDetScalar
        V.pairingMatrix V.form_symm V.form_det_ne_zero : ℝ)| *
      ((2 : ℝ) ^ n * (Real.sqrt |((V.pairingMatrix.det : ℚ) : ℝ)|) ^ (n - 1)) := by
    have hd := Matrix.skewAdjointFixedFormElementaryDetScalar_ne_zero V.pairingMatrix V.form_symm
      V.form_det_ne_zero
    refine mul_pos (abs_pos.mpr (by exact_mod_cast hd)) (mul_pos (by positivity) (pow_pos ?_ _))
    exact Real.sqrt_pos.mpr (abs_pos.mpr (by exact_mod_cast V.form_det_ne_zero))
  constructor
  · intro h0
    rw [h0, zero_mul] at h
    exact (ENNReal.ofReal_pos.mpr hX).ne h
  · intro ht
    rw [ht, ENNReal.top_mul (ENNReal.ofReal_pos.mpr hSP).ne'] at h
    exact ENNReal.ofReal_ne_top h.symm

variable (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)

/-- The value of the orbit mass: `N(O) = μ_V(univ)∏ s_V c_v / (μ_W(univ)∏ s_W)`, and
`0 < N(O) < ∞`, for positive-definite `W`, `a > 0` and positive finite local densities. -/
theorem fullAdelicNonisotropicLastShellMeasure_cylinderOrbit_badPlaces_eq_div
    [NeZero n]
    {T : Set ℝˣ} (hT : MeasurableSet T) (hneg : ∀ t : ℝˣ, -t ∈ T ↔ t ∈ T)
    (hT0 : (Measure.haar : Measure ℝˣ) T ≠ 0) (hTtop : (Measure.haar : Measure ℝˣ) T ≠ ⊤)
    {S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)}
    (hSB : W.lastExtensionHorizontalBadPlaces a ha ⊆ S)
    (U : ∀ v : {v // v ∈ W.lastExtensionHorizontalBadPlaces a ha},
      Subgroup ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1]ˣ)
    (hU : ∀ (v : {v // v ∈ W.lastExtensionHorizontalBadPlaces a ha}),
      IsOpen (U v : Set ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1]ˣ))
    (hUc : ∀ (v : {v // v ∈ W.lastExtensionHorizontalBadPlaces a ha}),
      IsCompact (U v : Set ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1]ˣ))
    (K : ∀ v : {v // v ∈ W.lastExtensionHorizontalBadPlaces a ha},
      Subgroup ((W.nonisotropicLastExtension a ha).specialOrthogonalMatrixGroup
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1]))
    (hK : ∀ (v : {v // v ∈ W.lastExtensionHorizontalBadPlaces a ha}),
      IsOpen (K v : Set ((W.nonisotropicLastExtension a ha).specialOrthogonalMatrixGroup
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1])))
    (hKc : ∀ (v : {v // v ∈ W.lastExtensionHorizontalBadPlaces a ha}),
      IsCompact (K v : Set ((W.nonisotropicLastExtension a ha).specialOrthogonalMatrixGroup
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1])))
    (hlift : ∀ (v : {v // v ∈ W.lastExtensionHorizontalBadPlaces a ha}), ∀ g ∈ K v,
      ∃ y : (W.nonisotropicLastExtension a ha).CliffordGeneralSpinIntrinsicPoint
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1],
      y.similitude ∈ U v ∧ CliffordGeneralSpinIntrinsicPoint.toSpecialOrthogonalGroupHom _ _ y = g)
    (c : {v // v ∈ W.lastExtensionHorizontalBadPlaces a ha} → ℝ≥0∞)
    (hloc : ∀ (v : {v // v ∈ W.lastExtensionHorizontalBadPlaces a ha}),
      (W.nonisotropicLastExtension a ha).padicInvariantDifferentialGroupMeasure
          (Rat.HeightOneSpectrum.primesEquiv v.1).1
          (K v : Set ((W.nonisotropicLastExtension a ha).specialOrthogonalMatrixGroup
            ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1])) =
        W.padicInvariantDifferentialGroupMeasure (Rat.HeightOneSpectrum.primesEquiv v.1).1
            (W.nonisotropicLastCoordinateFiberEmbedGroup a ha
              ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1] ⁻¹'
                (K v : Set ((W.nonisotropicLastExtension a ha).specialOrthogonalMatrixGroup
                  ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1]))) * c v)
    (hW : (W.pairingMatrix.map (algebraMap ℚ ℝ)).PosDef) (ha0 : 0 < a)
    (hc0 : ∀ v, c v ≠ 0) (hct : ∀ v, c v ≠ ⊤) :
    let N := W.fullAdelicNonisotropicLastShellMeasure a ha
        ((CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap W a ha RationalAdele) ''
          ((W.nonisotropicLastExtension a ha).centralCutoffSubgroup ⊤
            ((W.nonisotropicLastExtension a ha).cliffordGeneralSpinHorizontalCylinderSubgroup S
              (W.integralCompletedLocalSubgroups a ha S
                (fun v ↦ (W.nonisotropicLastExtension a ha).padicCentralCutoffSubgroup v.1 (U v) (K v))))
            : Set _))
    N = ((W.nonisotropicLastExtension a ha).realInvariantDifferentialGroupMeasure Set.univ *
        ∏ v : {v // v ∈ W.lastExtensionHorizontalBadPlaces a ha},
          (W.nonisotropicLastExtension a ha).cliffordGeneralSpinHorizontalBaselineScale v.1 * c v) /
        (W.realInvariantDifferentialGroupMeasure Set.univ *
          ∏ v : {v // v ∈ W.lastExtensionHorizontalBadPlaces a ha},
            W.cliffordGeneralSpinHorizontalBaselineScale v.1) ∧ N ≠ 0 ∧ N ≠ ⊤ := by
  intro N
  have h := W.fullAdelicNonisotropicLastShellMeasure_cylinderOrbit_badPlaces_localDensity a ha hT hneg hT0 hTtop hSB U hU hUc K hK hKc hlift c hloc
  have hWm := W.realInvariantDifferentialGroupMeasure_univ_ne_zero_ne_top hW
  have hVm := (W.nonisotropicLastExtension a ha).realInvariantDifferentialGroupMeasure_univ_ne_zero_ne_top
    (W.posDef_nonisotropicLastExtension_map_real hW ha ha0)
  have hA0 : W.realInvariantDifferentialGroupMeasure Set.univ *
      ∏ v : {v // v ∈ W.lastExtensionHorizontalBadPlaces a ha},
        W.cliffordGeneralSpinHorizontalBaselineScale v.1 ≠ 0 :=
    mul_ne_zero hWm.1 (Finset.prod_ne_zero_iff.2 fun v _ ↦
      W.cliffordGeneralSpinHorizontalBaselineScale_ne_zero v.1)
  have hAt : W.realInvariantDifferentialGroupMeasure Set.univ *
      ∏ v : {v // v ∈ W.lastExtensionHorizontalBadPlaces a ha},
        W.cliffordGeneralSpinHorizontalBaselineScale v.1 ≠ ⊤ :=
    ENNReal.mul_ne_top hWm.2 (ENNReal.prod_ne_top fun v _ ↦
      W.cliffordGeneralSpinHorizontalBaselineScale_ne_top v.1)
  have hB0 : (W.nonisotropicLastExtension a ha).realInvariantDifferentialGroupMeasure Set.univ *
      ∏ v : {v // v ∈ W.lastExtensionHorizontalBadPlaces a ha},
        (W.nonisotropicLastExtension a ha).cliffordGeneralSpinHorizontalBaselineScale v.1 * c v ≠ 0 :=
    mul_ne_zero hVm.1 (Finset.prod_ne_zero_iff.2 fun v _ ↦ mul_ne_zero
      ((W.nonisotropicLastExtension a ha).cliffordGeneralSpinHorizontalBaselineScale_ne_zero v.1)
      (hc0 v))
  have hBt : (W.nonisotropicLastExtension a ha).realInvariantDifferentialGroupMeasure Set.univ *
      ∏ v : {v // v ∈ W.lastExtensionHorizontalBadPlaces a ha},
        (W.nonisotropicLastExtension a ha).cliffordGeneralSpinHorizontalBaselineScale v.1 * c v ≠ ⊤ :=
    ENNReal.mul_ne_top hVm.2 (ENNReal.prod_ne_top fun v _ ↦ ENNReal.mul_ne_top
      ((W.nonisotropicLastExtension a ha).cliffordGeneralSpinHorizontalBaselineScale_ne_top v.1)
      (hct v))
  have hN : N = _ := ENNReal.eq_div_of_mul_eq_of_ne h hA0 hAt
  refine ⟨hN, ?_, ?_⟩
  · rw [hN]; exact ENNReal.div_ne_zero.mpr ⟨hB0, hAt⟩
  · rw [hN]; exact ENNReal.div_ne_top hBt hA0

end RationalQuadraticSpaceMatrix
