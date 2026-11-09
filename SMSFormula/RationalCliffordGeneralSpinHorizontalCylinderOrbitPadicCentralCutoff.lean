import SMSFormula.RationalCliffordGeneralSpinHorizontalPadicCentralCutoff
import SMSFormula.RationalCliffordGeneralSpinHorizontalCylinderOrbitSigmaCompact

/-!
# The bad-place orbit identity for p-adic central cutoffs

At each bad place `v ∈ B = bad_V ∪ bad_W` take the supplied local subgroup
`t_v = φ_V⁻¹(U_v × K_v) = {ν ∈ U_v, toSO ∈ K_v}` for supplied open subgroups `U_v ≤ ℚ_p^×` and
`K_v ≤ SO(V)(ℚ_p)` whose points lift with similitude in `U_v`.  The p-adic central factor
evaluates both local `GSpin` volumes at every prime (including `2`):

`Haar_V(t_v) = C_v · μ_{SO_V}(K_v)`, `Haar_W(ι⁻¹t_v) = C_v · μ_{SO_W}(e⁻¹K_v)`,
`C_v = 2 · Haar(U_v ⊓ (ℚ_p^×)²)`,

so the full-SO bad-place orbit identity becomes an identity of special-orthogonal volumes with
the same form-independent central constants on both sides.  Compactness of `t_v` is supplied.
No section, sheet, square class or bad-place subgroup is chosen.
-/

noncomputable section

open MeasureTheory Set PositiveDefiniteIntegralLattice
open scoped ENNReal

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

set_option synthInstance.maxHeartbeats 700000
set_option maxHeartbeats 2400000

local instance cylPadicCutoffDecidableEq :
    DecidableEq (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  Classical.decEq _

local instance cylPadicCutoffPrimeFact (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

local instance cylPadicCutoffGroupMeasurableSpace (V : RationalQuadraticSpaceMatrix n)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    MeasurableSpace (V.HeightOnePadicCliffordGeneralSpinGroup v) :=
  borel _

local instance cylPadicCutoffGroupBorelSpace (V : RationalQuadraticSpaceMatrix n)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    BorelSpace (V.HeightOnePadicCliffordGeneralSpinGroup v) :=
  ⟨rfl⟩

noncomputable local instance cylPadicCutoffUnitMeasurableSpace (p : ℕ) [Fact (Nat.Prime p)] :
    MeasurableSpace ℚ_[p]ˣ := borel _

noncomputable local instance cylPadicCutoffUnitBorelSpace (p : ℕ) [Fact (Nat.Prime p)] :
    BorelSpace ℚ_[p]ˣ := ⟨rfl⟩

noncomputable local instance cylPadicCutoffSOMeasurableSpace (V : RationalQuadraticSpaceMatrix n)
    (p : ℕ) [Fact (Nat.Prime p)] :
    MeasurableSpace (V.specialOrthogonalMatrixGroup ℚ_[p]) :=
  V.padicSpecialOrthogonalGroupMeasurableSpace_spinorNorm p

noncomputable local instance cylPadicCutoffSOBorelSpace (V : RationalQuadraticSpaceMatrix n)
    (p : ℕ) [Fact (Nat.Prime p)] :
    BorelSpace (V.specialOrthogonalMatrixGroup ℚ_[p]) :=
  V.padicSpecialOrthogonalGroupBorelSpace_spinorNorm p

/-- The p-adic central cutoff subgroup `{ν ∈ U, toSO ∈ K}` at a height-one place. -/
def padicCentralCutoffSubgroup (V : RationalQuadraticSpaceMatrix n)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ)
    (U : Subgroup ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]ˣ)
    (K : Subgroup (V.specialOrthogonalMatrixGroup ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1])) :
    Subgroup (V.HeightOnePadicCliffordGeneralSpinGroup v) :=
  (U.prod K).comap (CliffordGeneralSpinIntrinsicPoint.centralFiberGroupHom V _)

theorem coe_padicCentralCutoffSubgroup (V : RationalQuadraticSpaceMatrix n)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ)
    (U : Subgroup ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]ˣ)
    (K : Subgroup (V.specialOrthogonalMatrixGroup ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1])) :
    (V.padicCentralCutoffSubgroup v U K : Set (V.HeightOnePadicCliffordGeneralSpinGroup v)) =
      CliffordGeneralSpinIntrinsicPoint.centralFiberGroupHom V _ ⁻¹' ((U : Set _) ×ˢ (K : Set _)) :=
  rfl

variable (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)

/-- The bad-place orbit identity for p-ADIC central cutoffs: with `t_v = {ν ∈ U_v, toSO ∈ K_v}`
at the bad places (supplied open `U_v`, `K_v`, lifts, compactness),

`N(K•x) · μ_{SO_W}(SO(ℝ)) · ∏_B s_W(v) C_v μ_{SO_W}(e⁻¹K_v)
  = μ_{SO_V}(SO(ℝ)) · ∏_B s_V(v) C_v μ_{SO_V}(K_v)`,  `C_v = 2 · Haar(U_v ⊓ (ℚ_p^×)²)`. -/
theorem fullAdelicNonisotropicLastShellMeasure_cylinderOrbit_badPlaces_padicCentralCutoff
    [NeZero n]
    {T : Set ℝˣ} (hT : MeasurableSet T) (hneg : ∀ t : ℝˣ, -t ∈ T ↔ t ∈ T)
    (hT0 : (Measure.haar : Measure ℝˣ) T ≠ 0) (hTtop : (Measure.haar : Measure ℝˣ) T ≠ ⊤)
    {S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)}
    (hSB : W.lastExtensionHorizontalBadPlaces a ha ⊆ S)
    (U : ∀ v : {v // v ∈ W.lastExtensionHorizontalBadPlaces a ha},
      Subgroup ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1]ˣ)
    (hU : ∀ (v : {v // v ∈ W.lastExtensionHorizontalBadPlaces a ha}), IsOpen (U v : Set ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1]ˣ))
    (K : ∀ v : {v // v ∈ W.lastExtensionHorizontalBadPlaces a ha},
      Subgroup ((W.nonisotropicLastExtension a ha).specialOrthogonalMatrixGroup
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1]))
    (hK : ∀ (v : {v // v ∈ W.lastExtensionHorizontalBadPlaces a ha}), IsOpen (K v : Set ((W.nonisotropicLastExtension a ha).specialOrthogonalMatrixGroup
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1])))
    (hKW : ∀ (v : {v // v ∈ W.lastExtensionHorizontalBadPlaces a ha}), MeasurableSet (W.nonisotropicLastCoordinateFiberEmbedGroup a ha
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1] ⁻¹'
      (K v : Set ((W.nonisotropicLastExtension a ha).specialOrthogonalMatrixGroup
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1]))))
    (hlift : ∀ (v : {v // v ∈ W.lastExtensionHorizontalBadPlaces a ha}), ∀ g ∈ K v, ∃ y : (W.nonisotropicLastExtension a ha).CliffordGeneralSpinIntrinsicPoint
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1],
      y.similitude ∈ U v ∧ CliffordGeneralSpinIntrinsicPoint.toSpecialOrthogonalGroupHom _ _ y = g)
    (htc : ∀ (v : {v // v ∈ W.lastExtensionHorizontalBadPlaces a ha}), IsCompact ((W.nonisotropicLastExtension a ha).padicCentralCutoffSubgroup v.1 (U v) (K v) :
      Set ((W.nonisotropicLastExtension a ha).HeightOnePadicCliffordGeneralSpinGroup v.1))) :
    W.fullAdelicNonisotropicLastShellMeasure a ha
        ((CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap W a ha RationalAdele) ''
          ((W.nonisotropicLastExtension a ha).centralCutoffSubgroup ⊤
            ((W.nonisotropicLastExtension a ha).cliffordGeneralSpinHorizontalCylinderSubgroup S
              (W.integralCompletedLocalSubgroups a ha S
                (fun v ↦ (W.nonisotropicLastExtension a ha).padicCentralCutoffSubgroup v.1 (U v) (K v))))
            : Set _)) *
      (W.realInvariantDifferentialGroupMeasure Set.univ *
        ∏ v : {v // v ∈ W.lastExtensionHorizontalBadPlaces a ha},
          W.cliffordGeneralSpinHorizontalBaselineScale v.1 *
            (2 * (Measure.haar : Measure ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1]ˣ)
                ((U v ⊓ Subgroup.square _ : Subgroup _) : Set _) *
              W.padicInvariantDifferentialGroupMeasure (Rat.HeightOneSpectrum.primesEquiv v.1).1
                (W.nonisotropicLastCoordinateFiberEmbedGroup a ha
                  ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1] ⁻¹' (K v : Set ((W.nonisotropicLastExtension a ha).specialOrthogonalMatrixGroup
                  ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1]))))) =
      (W.nonisotropicLastExtension a ha).realInvariantDifferentialGroupMeasure Set.univ *
        ∏ v : {v // v ∈ W.lastExtensionHorizontalBadPlaces a ha},
          (W.nonisotropicLastExtension a ha).cliffordGeneralSpinHorizontalBaselineScale v.1 *
            (2 * (Measure.haar : Measure ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1]ˣ)
                ((U v ⊓ Subgroup.square _ : Subgroup _) : Set _) *
              (W.nonisotropicLastExtension a ha).padicInvariantDifferentialGroupMeasure
                (Rat.HeightOneSpectrum.primesEquiv v.1).1 (K v : Set ((W.nonisotropicLastExtension a ha).specialOrthogonalMatrixGroup
                  ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1]))) := by
  have hopen : ∀ v : {v // v ∈ W.lastExtensionHorizontalBadPlaces a ha},
      IsOpen ((W.nonisotropicLastExtension a ha).padicCentralCutoffSubgroup v.1 (U v) (K v) :
        Set ((W.nonisotropicLastExtension a ha).HeightOnePadicCliffordGeneralSpinGroup v.1)) := fun v ↦
    ((W.nonisotropicLastExtension a ha).continuous_centralFiberGroupHom_padic _).isOpen_preimage _
      ((hU v).prod (hK v))
  have ht : ∀ v : {v // v ∈ W.lastExtensionHorizontalBadPlaces a ha},
      MeasurableSet ((W.nonisotropicLastExtension a ha).padicCentralCutoffSubgroup v.1 (U v) (K v) :
        Set ((W.nonisotropicLastExtension a ha).HeightOnePadicCliffordGeneralSpinGroup v.1)) :=
    fun v ↦ (hopen v).measurableSet
  have htW : ∀ v : {v // v ∈ W.lastExtensionHorizontalBadPlaces a ha},
      MeasurableSet (W.nonisotropicLastComplementGeneralSpinPoint a ha _ ⁻¹'
        ((W.nonisotropicLastExtension a ha).padicCentralCutoffSubgroup v.1 (U v) (K v) :
          Set ((W.nonisotropicLastExtension a ha).HeightOnePadicCliffordGeneralSpinGroup v.1))) :=
    fun v ↦ ((hopen v).preimage
      (W.continuous_nonisotropicLastComplementGeneralSpinPoint a ha _)).measurableSet
  have hV : ∀ v : {v // v ∈ W.lastExtensionHorizontalBadPlaces a ha},
      (W.nonisotropicLastExtension a ha).heightOnePadicCliffordGeneralSpinHorizontalHaarMeasure v.1
          ((W.nonisotropicLastExtension a ha).padicCentralCutoffSubgroup v.1 (U v) (K v) :
            Set ((W.nonisotropicLastExtension a ha).HeightOnePadicCliffordGeneralSpinGroup v.1)) =
        2 * (Measure.haar : Measure ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1]ˣ)
            ((U v ⊓ Subgroup.square _ : Subgroup _) : Set _) *
          (W.nonisotropicLastExtension a ha).padicInvariantDifferentialGroupMeasure
            (Rat.HeightOneSpectrum.primesEquiv v.1).1 (K v : Set ((W.nonisotropicLastExtension a ha).specialOrthogonalMatrixGroup
                  ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1])) := fun v ↦
    (W.nonisotropicLastExtension a ha).padicCliffordGeneralSpinHorizontalDifferentialHaarMeasure_centralFiber
      _ (U v) (hU v).measurableSet _ (hK v).measurableSet (hlift v)
  have hW : ∀ v : {v // v ∈ W.lastExtensionHorizontalBadPlaces a ha},
      W.heightOnePadicCliffordGeneralSpinHorizontalHaarMeasure v.1
          (W.nonisotropicLastComplementGeneralSpinPoint a ha _ ⁻¹'
            ((W.nonisotropicLastExtension a ha).padicCentralCutoffSubgroup v.1 (U v) (K v) :
              Set ((W.nonisotropicLastExtension a ha).HeightOnePadicCliffordGeneralSpinGroup v.1))) =
        2 * (Measure.haar : Measure ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1]ˣ)
            ((U v ⊓ Subgroup.square _ : Subgroup _) : Set _) *
          W.padicInvariantDifferentialGroupMeasure (Rat.HeightOneSpectrum.primesEquiv v.1).1
            (W.nonisotropicLastCoordinateFiberEmbedGroup a ha
              ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1] ⁻¹' (K v : Set ((W.nonisotropicLastExtension a ha).specialOrthogonalMatrixGroup
                  ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1]))) := fun v ↦
    W.padicCliffordGeneralSpinHorizontalDifferentialHaarMeasure_preimage_block_centralFiber a ha _
      (U v) (hU v).measurableSet _ (hKW v) (hlift v)
  have main := W.fullAdelicNonisotropicLastShellMeasure_cylinderOrbit_badPlaces_top_of_isCompact a ha
    hT hneg hT0 hTtop hSB
    (fun v ↦ (W.nonisotropicLastExtension a ha).padicCentralCutoffSubgroup v.1 (U v) (K v)) ht htW htc
  simp only [hV, hW] at main
  exact main

/-- The bad-place orbit identity in special-orthogonal volumes: when the central constants
`Haar(U_v ⊓ (ℚ_p^×)²)` are finite (they are automatically nonzero), they cancel:

`N(K•x) · μ_{SO_W}(SO(ℝ)) · ∏_B s_W(v) μ_{SO_W}(e⁻¹K_v) = μ_{SO_V}(SO(ℝ)) · ∏_B s_V(v) μ_{SO_V}(K_v)`. -/
theorem fullAdelicNonisotropicLastShellMeasure_cylinderOrbit_badPlaces_padicCentralCutoff_cancel
    [NeZero n]
    {T : Set ℝˣ} (hT : MeasurableSet T) (hneg : ∀ t : ℝˣ, -t ∈ T ↔ t ∈ T)
    (hT0 : (Measure.haar : Measure ℝˣ) T ≠ 0) (hTtop : (Measure.haar : Measure ℝˣ) T ≠ ⊤)
    {S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)}
    (hSB : W.lastExtensionHorizontalBadPlaces a ha ⊆ S)
    (U : ∀ v : {v // v ∈ W.lastExtensionHorizontalBadPlaces a ha},
      Subgroup ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1]ˣ)
    (hU : ∀ (v : {v // v ∈ W.lastExtensionHorizontalBadPlaces a ha}), IsOpen (U v : Set ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1]ˣ))
    (K : ∀ v : {v // v ∈ W.lastExtensionHorizontalBadPlaces a ha},
      Subgroup ((W.nonisotropicLastExtension a ha).specialOrthogonalMatrixGroup
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1]))
    (hK : ∀ (v : {v // v ∈ W.lastExtensionHorizontalBadPlaces a ha}), IsOpen (K v : Set ((W.nonisotropicLastExtension a ha).specialOrthogonalMatrixGroup
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1])))
    (hKW : ∀ (v : {v // v ∈ W.lastExtensionHorizontalBadPlaces a ha}), MeasurableSet (W.nonisotropicLastCoordinateFiberEmbedGroup a ha
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1] ⁻¹'
      (K v : Set ((W.nonisotropicLastExtension a ha).specialOrthogonalMatrixGroup
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1]))))
    (hlift : ∀ (v : {v // v ∈ W.lastExtensionHorizontalBadPlaces a ha}), ∀ g ∈ K v, ∃ y : (W.nonisotropicLastExtension a ha).CliffordGeneralSpinIntrinsicPoint
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1],
      y.similitude ∈ U v ∧ CliffordGeneralSpinIntrinsicPoint.toSpecialOrthogonalGroupHom _ _ y = g)
    (htc : ∀ (v : {v // v ∈ W.lastExtensionHorizontalBadPlaces a ha}), IsCompact ((W.nonisotropicLastExtension a ha).padicCentralCutoffSubgroup v.1 (U v) (K v) :
      Set ((W.nonisotropicLastExtension a ha).HeightOnePadicCliffordGeneralSpinGroup v.1)))
    (hCtop : ∀ (v : {v // v ∈ W.lastExtensionHorizontalBadPlaces a ha}),
      (Measure.haar : Measure ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1]ˣ)
        ((U v ⊓ Subgroup.square _ : Subgroup _) : Set _) ≠ ⊤) :
    W.fullAdelicNonisotropicLastShellMeasure a ha
        ((CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap W a ha RationalAdele) ''
          ((W.nonisotropicLastExtension a ha).centralCutoffSubgroup ⊤
            ((W.nonisotropicLastExtension a ha).cliffordGeneralSpinHorizontalCylinderSubgroup S
              (W.integralCompletedLocalSubgroups a ha S
                (fun v ↦ (W.nonisotropicLastExtension a ha).padicCentralCutoffSubgroup v.1 (U v) (K v))))
            : Set _)) *
      (W.realInvariantDifferentialGroupMeasure Set.univ *
        ∏ v : {v // v ∈ W.lastExtensionHorizontalBadPlaces a ha},
          W.cliffordGeneralSpinHorizontalBaselineScale v.1 *
            (W.padicInvariantDifferentialGroupMeasure (Rat.HeightOneSpectrum.primesEquiv v.1).1
                (W.nonisotropicLastCoordinateFiberEmbedGroup a ha
                  ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1] ⁻¹' (K v : Set ((W.nonisotropicLastExtension a ha).specialOrthogonalMatrixGroup
                  ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1]))))) =
      (W.nonisotropicLastExtension a ha).realInvariantDifferentialGroupMeasure Set.univ *
        ∏ v : {v // v ∈ W.lastExtensionHorizontalBadPlaces a ha},
          (W.nonisotropicLastExtension a ha).cliffordGeneralSpinHorizontalBaselineScale v.1 *
            ((W.nonisotropicLastExtension a ha).padicInvariantDifferentialGroupMeasure
                (Rat.HeightOneSpectrum.primesEquiv v.1).1 (K v : Set ((W.nonisotropicLastExtension a ha).specialOrthogonalMatrixGroup
                  ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1]))) := by
  have main := W.fullAdelicNonisotropicLastShellMeasure_cylinderOrbit_badPlaces_padicCentralCutoff a ha
    hT hneg hT0 hTtop hSB U hU K hK hKW hlift htc
  set C : {v // v ∈ W.lastExtensionHorizontalBadPlaces a ha} → ℝ≥0∞ := fun v ↦
    2 * (Measure.haar : Measure ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1]ˣ)
      ((U v ⊓ Subgroup.square _ : Subgroup _) : Set _) with hC
  have hC0 : ∀ v, C v ≠ 0 := fun v ↦ mul_ne_zero two_ne_zero
    ((((hU v).inter (Rat.isOpen_square_padicUnitsSubgroup _)).measure_ne_zero _
      ⟨1, (U v ⊓ Subgroup.square _).one_mem⟩))
  have hCt : ∀ v, C v ≠ ⊤ := fun v ↦ ENNReal.mul_ne_top ENNReal.ofNat_ne_top (hCtop v)
  have hsplit : ∀ (f g : {v // v ∈ W.lastExtensionHorizontalBadPlaces a ha} → ℝ≥0∞),
      ∏ v, f v * (C v * g v) = (∏ v, C v) * ∏ v, f v * g v := by
    intro f g
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun v _ ↦ mul_left_comm _ _ _
  rw [hsplit, hsplit] at main
  have hP0 : (∏ v, C v) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun v _ ↦ hC0 v
  have hPt : (∏ v, C v) ≠ ⊤ := ENNReal.prod_ne_top fun v _ ↦ hCt v
  refine (ENNReal.mul_right_inj hP0 hPt).mp ?_
  calc _ = _ * (_ * ((∏ v, C v) * _)) := by ring
    _ = _ := main
    _ = _ := by ring

end RationalQuadraticSpaceMatrix
