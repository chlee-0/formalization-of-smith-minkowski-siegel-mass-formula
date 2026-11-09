import SMSFormula.RationalCliffordGeneralSpinHorizontalCylinderOrbitPadicCentralCutoffCompact
import SMSFormula.RationalCliffordSpinBlockFiberEmbedCompact

/-!
# The orbit mass through local orbit densities

The bad-place orbit identity in special-orthogonal volumes

`N(K•x) · μ_{SO_W}(SO(ℝ)) · ∏_B s_W(v) vol_W(e⁻¹K_v) = μ_{SO_V}(SO(ℝ)) · ∏_B s_V(v) vol_V(K_v)`

and supplied local relations `vol_V(K_v) = vol_W(e⁻¹K_v) · c_v` (e.g. the carrying stabilizer
identity, `c_v = |r_v| ν_v(ℤ_p) glue_v(T_v)`) give, when every lower volume `vol_W(e⁻¹K_v)` is
finite and nonzero, the orbit by orbit cancellation:

`N(K•x) · μ_{SO_W}(SO(ℝ)) · ∏_B s_W(v) = μ_{SO_V}(SO(ℝ)) · ∏_B s_V(v) · c_v`.

The raw bad-place group volumes disappear; only the baseline scales, the real masses and the
local orbit densities `c_v` remain.  Nothing is chosen.
-/

noncomputable section

open MeasureTheory Set Filter Topology PositiveDefiniteIntegralLattice
open scoped ENNReal

/-- Orbit-by-orbit cancellation in `ℝ≥0∞`. -/
theorem ENNReal.mul_mul_prod_eq_of_local {ι : Type*} [Fintype ι] {N μW μV : ℝ≥0∞}
    {sW sV volW volV c : ι → ℝ≥0∞}
    (h : N * (μW * ∏ i, sW i * volW i) = μV * ∏ i, sV i * volV i)
    (hloc : ∀ i, volV i = volW i * c i) (h0 : ∀ i, volW i ≠ 0) (ht : ∀ i, volW i ≠ ⊤) :
    N * (μW * ∏ i, sW i) = μV * ∏ i, sV i * c i := by
  have hP0 : (∏ i, volW i) ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ ↦ h0 i
  have hPt : (∏ i, volW i) ≠ ⊤ := ENNReal.prod_ne_top fun i _ ↦ ht i
  refine (ENNReal.mul_left_inj hP0 hPt).mp ?_
  simp_rw [hloc] at h
  calc N * (μW * ∏ i, sW i) * ∏ i, volW i = N * (μW * ∏ i, sW i * volW i) := by
        rw [Finset.prod_mul_distrib]; ring
    _ = μV * ∏ i, sV i * (volW i * c i) := h
    _ = μV * (∏ i, sV i * c i) * ∏ i, volW i := by
        rw [show (fun i ↦ sV i * (volW i * c i)) = fun i ↦ (sV i * c i) * volW i from
          funext fun i ↦ by ring, Finset.prod_mul_distrib]; ring

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

set_option synthInstance.maxHeartbeats 700000
set_option maxHeartbeats 2400000

local instance omldDecidableEq : DecidableEq (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  Classical.decEq _

local instance omldPrimeFact (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

noncomputable local instance omldSOMeasurableSpace (V : RationalQuadraticSpaceMatrix n)
    (p : ℕ) [Fact (Nat.Prime p)] :
    MeasurableSpace (V.specialOrthogonalMatrixGroup ℚ_[p]) :=
  V.padicSpecialOrthogonalGroupMeasurableSpace_spinorNorm p

noncomputable local instance omldSOBorelSpace (V : RationalQuadraticSpaceMatrix n)
    (p : ℕ) [Fact (Nat.Prime p)] :
    BorelSpace (V.specialOrthogonalMatrixGroup ℚ_[p]) :=
  V.padicSpecialOrthogonalGroupBorelSpace_spinorNorm p

variable (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)

set_option backward.isDefEq.respectTransparency false in
/-- The lower volume of the pullback of an open subgroup is nonzero (it is open and contains `1`). -/
theorem padicInvariantDifferentialGroupMeasure_preimage_embed_ne_zero (p : ℕ) [Fact (Nat.Prime p)]
    (K : Subgroup ((W.nonisotropicLastExtension a ha).specialOrthogonalMatrixGroup ℚ_[p]))
    (hK : IsOpen (K : Set ((W.nonisotropicLastExtension a ha).specialOrthogonalMatrixGroup ℚ_[p]))) :
    W.padicInvariantDifferentialGroupMeasure p
        (W.nonisotropicLastCoordinateFiberEmbedGroup a ha ℚ_[p] ⁻¹'
          (K : Set ((W.nonisotropicLastExtension a ha).specialOrthogonalMatrixGroup ℚ_[p]))) ≠ 0 := by
  haveI := W.padicInvariantDifferentialGroupMeasure_isHaarMeasure p
  haveI : Measure.IsOpenPosMeasure (W.padicInvariantDifferentialGroupMeasure p) :=
    (W.padicInvariantDifferentialGroupMeasure_isHaarMeasure p).toIsOpenPosMeasure
  have hopen := hK.preimage (W.continuous_nonisotropicLastCoordinateFiberEmbedGroup a ha ℚ_[p])
  refine hopen.measure_ne_zero _ ⟨1, ?_⟩
  change W.nonisotropicLastCoordinateFiberEmbedHom a ha ℚ_[p] 1 ∈ K
  rw [map_one]
  exact K.one_mem

set_option backward.isDefEq.respectTransparency false in
/-- The lower volume of the pullback of a compact set is finite (the pullback is compact). -/
theorem padicInvariantDifferentialGroupMeasure_preimage_embed_ne_top (p : ℕ) [Fact (Nat.Prime p)]
    {K : Set ((W.nonisotropicLastExtension a ha).specialOrthogonalMatrixGroup ℚ_[p])}
    (hK : IsCompact K) :
    W.padicInvariantDifferentialGroupMeasure p
        (W.nonisotropicLastCoordinateFiberEmbedGroup a ha ℚ_[p] ⁻¹' K) ≠ ⊤ := by
  haveI := W.padicInvariantDifferentialGroupMeasure_isHaarMeasure p
  haveI : IsFiniteMeasureOnCompacts (W.padicInvariantDifferentialGroupMeasure p) :=
    (W.padicInvariantDifferentialGroupMeasure_isHaarMeasure p).toIsFiniteMeasureOnCompacts
  exact (W.isCompact_preimage_nonisotropicLastCoordinateFiberEmbedGroup a ha ℚ_[p] hK).measure_lt_top.ne

/-- The orbit mass through local orbit densities: for supplied compact open `U_v`, `K_v` with the
lift hypothesis, and supplied local densities `c_v` with `vol_V(K_v) = vol_W(e⁻¹K_v) · c_v` and
no further hypotheses (the lower volumes are automatically finite and nonzero),
`N(K•x) · μ_{SO_W}(SO(ℝ)) · ∏_B s_W(v) = μ_{SO_V}(SO(ℝ)) · ∏_B s_V(v) · c_v`. -/
theorem fullAdelicNonisotropicLastShellMeasure_cylinderOrbit_badPlaces_localDensity
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
                  ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1]))) * c v) :
    W.fullAdelicNonisotropicLastShellMeasure a ha
        ((CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap W a ha RationalAdele) ''
          ((W.nonisotropicLastExtension a ha).centralCutoffSubgroup ⊤
            ((W.nonisotropicLastExtension a ha).cliffordGeneralSpinHorizontalCylinderSubgroup S
              (W.integralCompletedLocalSubgroups a ha S
                (fun v ↦ (W.nonisotropicLastExtension a ha).padicCentralCutoffSubgroup v.1 (U v) (K v))))
            : Set _)) *
      (W.realInvariantDifferentialGroupMeasure Set.univ *
        ∏ v : {v // v ∈ W.lastExtensionHorizontalBadPlaces a ha},
          W.cliffordGeneralSpinHorizontalBaselineScale v.1) =
      (W.nonisotropicLastExtension a ha).realInvariantDifferentialGroupMeasure Set.univ *
        ∏ v : {v // v ∈ W.lastExtensionHorizontalBadPlaces a ha},
          (W.nonisotropicLastExtension a ha).cliffordGeneralSpinHorizontalBaselineScale v.1 * c v :=
  ENNReal.mul_mul_prod_eq_of_local
    (W.fullAdelicNonisotropicLastShellMeasure_cylinderOrbit_badPlaces_padicCentralCutoff_compact a ha
      hT hneg hT0 hTtop hSB U hU hUc K hK hKc hlift) hloc
    (fun v ↦ W.padicInvariantDifferentialGroupMeasure_preimage_embed_ne_zero a ha _ (K v) (hK v))
    (fun v ↦ W.padicInvariantDifferentialGroupMeasure_preimage_embed_ne_top a ha _ (hKc v))

end RationalQuadraticSpaceMatrix
