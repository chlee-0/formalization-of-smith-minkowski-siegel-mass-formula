import SMSFormula.RationalCliffordGeneralSpinPadicUnitSimilitudeImage
import SMSFormula.RationalCliffordGeneralSpinHorizontalOrbitMassLocalDensity
import SMSFormula.RationalQuadraticIsometrySpinCandidateGeneralSpecialOrthogonal

/-!
# Existence of local orbit-mass data at every place

For a presentation `P` of the anisotropic complement of `x` and a finite place `v`:

* `Kst` = the stabilizer, in the block `SO(ℚ_p)`, of the presentation lattice `E⁻¹ ℤ_p^N`: the
  pullback of the ambient integral `SO` subgroup along the isometry transport of `SO`
  groups.  It is compact open, and each of its elements preserves `E⁻¹ ℤ_p^N` (`hKlat`).
* `K_v` = the unit-similitude image inside `Kst`: compact open, with unit-similitude `GSpin` lifts
  (`hlift`, `U_v = ℤ_p^×`).
* `c_v = vol_block(K_v) / vol_W(e⁻¹ K_v)`: positive and finite (Haar measures, compact open), with
  `vol_block(K_v) = vol_W(e⁻¹ K_v) · c_v` (`hloc`).

These are exactly the local orbit-mass inputs at `v` of the adelic Gaussian assembly.
-/

noncomputable section

open MeasureTheory Matrix

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

set_option synthInstance.maxHeartbeats 700000
set_option maxHeartbeats 2400000

noncomputable local instance clomdSOMeasurableSpace (V : RationalQuadraticSpaceMatrix n)
    (p : ℕ) [Fact (Nat.Prime p)] :
    MeasurableSpace (V.specialOrthogonalMatrixGroup ℚ_[p]) :=
  V.padicSpecialOrthogonalGroupMeasurableSpace_spinorNorm p

noncomputable local instance clomdSOBorelSpace (V : RationalQuadraticSpaceMatrix n)
    (p : ℕ) [Fact (Nat.Prime p)] :
    BorelSpace (V.specialOrthogonalMatrixGroup ℚ_[p]) :=
  V.padicSpecialOrthogonalGroupBorelSpace_spinorNorm p

namespace AnisotropicComplementPresentation

variable {m : ℕ} {V : RationalQuadraticSpaceMatrix n} {x : Fin n → ℚ}
variable (P : V.AnisotropicComplementPresentation x m)
variable (hx : V.nativeRationalQuadraticForm x ≠ 0)

/-- The stabilizer of the presentation lattice `E⁻¹ ℤ_p^N` in the block `SO(ℚ_p)`. -/
def padicPresentationLatticeStabilizer (p : ℕ) [Fact p.Prime] :
    Subgroup ((P.blockSpace hx).specialOrthogonalMatrixGroup ℚ_[p]) :=
  (V.padicSpecialOrthogonalIntegralSubgroup p).comap
    (rationalIsometrySpecialOrthogonalGroupContinuousMulEquiv (P.blockSpace hx) V
      (P.blockToAmbientIsometryEquiv hx) ℚ_[p]).toMonoidHom

theorem isCompact_padicPresentationLatticeStabilizer (p : ℕ) [Fact p.Prime] :
    IsCompact (P.padicPresentationLatticeStabilizer hx p :
      Set ((P.blockSpace hx).specialOrthogonalMatrixGroup ℚ_[p])) :=
  (rationalIsometrySpecialOrthogonalGroupContinuousMulEquiv (P.blockSpace hx) V
    (P.blockToAmbientIsometryEquiv hx) ℚ_[p]).toHomeomorph.isCompact_preimage.2
    (V.isCompact_padicSpecialOrthogonalIntegralSubgroup p)

theorem isOpen_padicPresentationLatticeStabilizer (p : ℕ) [Fact p.Prime] :
    IsOpen (P.padicPresentationLatticeStabilizer hx p :
      Set ((P.blockSpace hx).specialOrthogonalMatrixGroup ℚ_[p])) :=
  (V.isOpen_padicSpecialOrthogonalIntegralSubgroup p).preimage
    (rationalIsometrySpecialOrthogonalGroupContinuousMulEquiv (P.blockSpace hx) V
      (P.blockToAmbientIsometryEquiv hx) ℚ_[p]).continuous

/-- The stabilizer preserves the presentation lattice (`hKlat`). -/
theorem blockToAmbient_mulVec_mem_of_mem_padicPresentationLatticeStabilizer (p : ℕ) [Fact p.Prime]
    {g : (P.blockSpace hx).specialOrthogonalMatrixGroup ℚ_[p]}
    (hg : g ∈ P.padicPresentationLatticeStabilizer hx p) (w : Fin (m + 1) → ℚ_[p])
    (hw : ∀ i, P.blockToAmbientBaseChangeIsometryEquiv hx ℚ_[p] w i ∈ PadicInt.subring p) (i : Fin n) :
    P.blockToAmbientBaseChangeIsometryEquiv hx ℚ_[p]
        ((g.1.1.1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ_[p]) *ᵥ w) i ∈ PadicInt.subring p := by
  set φ := rationalIsometrySpecialOrthogonalGroupContinuousMulEquiv (P.blockSpace hx) V
    (P.blockToAmbientIsometryEquiv hx) ℚ_[p] with hφdef
  have hint : ∀ i j, (φ g).1.1.1 i j ∈ PadicInt.subring p :=
    ((V.mem_padicSpecialOrthogonalIntegralSubgroup_iff p (φ g)).1 hg).1
  have hmul := rationalIsometrySpecialOrthogonalMatrixPoint_mulVec (P.blockSpace hx) V
    (P.blockToAmbientIsometryEquiv hx) ℚ_[p]
    ((P.blockSpace hx).specialOrthogonalMatrixPointOfGroup ℚ_[p] g)
    (P.blockToAmbientBaseChangeIsometryEquiv hx ℚ_[p] w)
  have hsymm : (rationalIsometryBaseChangeIsometryEquiv (P.blockSpace hx) V
      (P.blockToAmbientIsometryEquiv hx) ℚ_[p]).symm
        (P.blockToAmbientBaseChangeIsometryEquiv hx ℚ_[p] w) = w :=
    (P.blockToAmbientBaseChangeIsometryEquiv hx ℚ_[p]).symm_apply_apply w
  rw [hsymm] at hmul
  have hE : P.blockToAmbientBaseChangeIsometryEquiv hx ℚ_[p]
      ((g.1.1.1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ_[p]) *ᵥ w) =
      (φ g).1.1.1 *ᵥ P.blockToAmbientBaseChangeIsometryEquiv hx ℚ_[p] w := hmul.symm
  rw [hE]
  simp only [Matrix.mulVec, dotProduct]
  exact Subring.sum_mem _ fun j _ ↦ Subring.mul_mem _ (hint i j) (hw j)

end AnisotropicComplementPresentation

set_option backward.isDefEq.respectTransparency false in
/-- A compact open subgroup has positive finite volume for the block Haar measure. -/
theorem padicInvariantDifferentialGroupMeasure_ne_zero_ne_top_of_compactOpen
    (U : RationalQuadraticSpaceMatrix n) (p : ℕ) [Fact (Nat.Prime p)]
    (K : Subgroup (U.specialOrthogonalMatrixGroup ℚ_[p]))
    (hKo : IsOpen (K : Set (U.specialOrthogonalMatrixGroup ℚ_[p])))
    (hKc : IsCompact (K : Set (U.specialOrthogonalMatrixGroup ℚ_[p]))) :
    U.padicInvariantDifferentialGroupMeasure p (K : Set (U.specialOrthogonalMatrixGroup ℚ_[p])) ≠ 0 ∧
      U.padicInvariantDifferentialGroupMeasure p (K : Set (U.specialOrthogonalMatrixGroup ℚ_[p])) ≠ ⊤ := by
  haveI := U.padicInvariantDifferentialGroupMeasure_isHaarMeasure p
  haveI : Measure.IsOpenPosMeasure (U.padicInvariantDifferentialGroupMeasure p) :=
    (U.padicInvariantDifferentialGroupMeasure_isHaarMeasure p).toIsOpenPosMeasure
  haveI : IsFiniteMeasureOnCompacts (U.padicInvariantDifferentialGroupMeasure p) :=
    (U.padicInvariantDifferentialGroupMeasure_isHaarMeasure p).toIsFiniteMeasureOnCompacts
  exact ⟨hKo.measure_ne_zero _ ⟨1, K.one_mem⟩, hKc.measure_lt_top.ne⟩

local instance clomdPrimeFact (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

namespace AnisotropicComplementPresentation

variable {m : ℕ} {V : RationalQuadraticSpaceMatrix n} {x : Fin n → ℚ}
variable (P : V.AnisotropicComplementPresentation x m)
variable (hx : V.nativeRationalQuadraticForm x ≠ 0)

/-- Existence of the local orbit-mass data at a finite place `v`. -/
theorem exists_capstoneLocalOrbitMassData (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    ∃ (U : Subgroup ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]ˣ)
      (K : Subgroup ((P.blockSpace hx).specialOrthogonalMatrixGroup
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1])) (c : ENNReal),
      IsOpen (U : Set ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]ˣ) ∧
      IsCompact (U : Set ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]ˣ) ∧
      IsOpen (K : Set ((P.blockSpace hx).specialOrthogonalMatrixGroup
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1])) ∧
      IsCompact (K : Set ((P.blockSpace hx).specialOrthogonalMatrixGroup
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1])) ∧
      (∀ g ∈ K, ∃ y : (P.blockSpace hx).CliffordGeneralSpinIntrinsicPoint
          ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1],
        y.similitude ∈ U ∧ CliffordGeneralSpinIntrinsicPoint.toSpecialOrthogonalGroupHom _ _ y = g) ∧
      (P.blockSpace hx).padicInvariantDifferentialGroupMeasure (Rat.HeightOneSpectrum.primesEquiv v).1
          (K : Set ((P.blockSpace hx).specialOrthogonalMatrixGroup
            ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1])) =
        P.lowerSpace.padicInvariantDifferentialGroupMeasure (Rat.HeightOneSpectrum.primesEquiv v).1
          (P.lowerSpace.nonisotropicLastCoordinateFiberEmbedGroup (V.nativeRationalQuadraticForm x) hx
            ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1] ⁻¹'
              (K : Set ((P.blockSpace hx).specialOrthogonalMatrixGroup
                ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]))) * c ∧
      c ≠ 0 ∧ c ≠ ⊤ ∧
      (∀ g ∈ K, ∀ w : Fin (m + 1) → ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1],
        (∀ i, P.blockToAmbientBaseChangeIsometryEquiv hx ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1] w i ∈
          PadicInt.subring (Rat.HeightOneSpectrum.primesEquiv v).1) →
        ∀ i, P.blockToAmbientBaseChangeIsometryEquiv hx ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]
          ((g.1.1.1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]) *ᵥ w) i ∈
            PadicInt.subring (Rat.HeightOneSpectrum.primesEquiv v).1) := by
  let p := (Rat.HeightOneSpectrum.primesEquiv v).1
  let Kst := P.padicPresentationLatticeStabilizer hx p
  let K := (P.blockSpace hx).padicUnitSimilitudeImage v Kst
  have hKo : IsOpen (K : Set ((P.blockSpace hx).specialOrthogonalMatrixGroup ℚ_[p])) :=
    isOpen_padicUnitSimilitudeImage (P.isOpen_padicPresentationLatticeStabilizer hx p)
  have hKc : IsCompact (K : Set ((P.blockSpace hx).specialOrthogonalMatrixGroup ℚ_[p])) :=
    isCompact_padicUnitSimilitudeImage (P.isCompact_padicPresentationLatticeStabilizer hx p)
  obtain ⟨hV0, hVt⟩ :=
    padicInvariantDifferentialGroupMeasure_ne_zero_ne_top_of_compactOpen (P.blockSpace hx) p K hKo hKc
  have hW0 := P.lowerSpace.padicInvariantDifferentialGroupMeasure_preimage_embed_ne_zero
    (V.nativeRationalQuadraticForm x) hx p K hKo
  have hWt := P.lowerSpace.padicInvariantDifferentialGroupMeasure_preimage_embed_ne_top
    (V.nativeRationalQuadraticForm x) hx p hKc
  refine ⟨padicIntegralUnitsSubgroup p, K,
    (P.blockSpace hx).padicInvariantDifferentialGroupMeasure p
        (K : Set ((P.blockSpace hx).specialOrthogonalMatrixGroup ℚ_[p])) /
      P.lowerSpace.padicInvariantDifferentialGroupMeasure p
        (P.lowerSpace.nonisotropicLastCoordinateFiberEmbedGroup (V.nativeRationalQuadraticForm x) hx
          ℚ_[p] ⁻¹' (K : Set ((P.blockSpace hx).specialOrthogonalMatrixGroup ℚ_[p]))),
    isOpen_padicIntegralUnitsSubgroup p, isCompact_padicIntegralUnitsSubgroup p, hKo, hKc,
    fun g hg ↦ exists_lift_of_mem_padicUnitSimilitudeImage Kst g hg, ?_, ?_, ?_, ?_⟩
  · exact (ENNReal.mul_div_cancel hW0 hWt).symm
  · exact ENNReal.div_ne_zero.2 ⟨hV0, hWt⟩
  · exact ENNReal.div_ne_top hVt hW0
  · intro g hg w hw i
    exact P.blockToAmbient_mulVec_mem_of_mem_padicPresentationLatticeStabilizer hx p
      (padicUnitSimilitudeImage_le Kst hg) w hw i

end AnisotropicComplementPresentation

end RationalQuadraticSpaceMatrix
