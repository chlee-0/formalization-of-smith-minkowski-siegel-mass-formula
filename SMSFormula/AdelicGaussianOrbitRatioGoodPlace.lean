import SMSFormula.AdelicGaussianOrbitRatioCapstone
import SMSFormula.RationalCliffordGeneralSpinFiniteAdelicShell

/-!
# The good places of the orbit Riesz ratio

At a place `v` outside the bad set `B`, the local subgroup of the orbit ratio is the
integral `GSpin` subgroup.  Where `v` is not an odd-unimodular bad place and `a` is a unit, its
orbit on the block shell is exactly the set of integral block shell points (the integral lift
argument, stated here for a local block shell point).  If moreover `p_v ∤ D_P`, the presentation is
integral in both directions, so the presentation image of the orbit has the integral lattice
shell as trace: the good-orbit trace hypothesis of the orbit-ratio theorem holds.  Nothing is chosen.
-/

noncomputable section

open PositiveDefiniteIntegralLattice RationalQuadraticSpaceMatrix Rat.HeightOneSpectrum MeasureTheory
open scoped ENNReal Matrix

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

local instance goodPlacePrimeFact (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

set_option synthInstance.maxHeartbeats 500000
set_option maxHeartbeats 1600000

/-- The local integral lift: an integral block shell point at a good place is the orbit of an
integral `GSpin` point. -/
theorem exists_integral_padic_nonisotropicLastShellOrbitMap_eq
    (W : RationalQuadraticSpaceMatrix n) [NeZero n] (a : ℚ) (ha : a ≠ 0)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ)
    (hvOdd : v ∉ (W.nonisotropicLastExtension a ha).cliffordSpinCandidateOddUnimodularBadPlaces)
    (hvStructure : (W.nonisotropicLastExtension a ha).CliffordGeneralSpinIntegralStructureAt v)
    (yv : W.nonisotropicLastQuadraticShell a ha ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1])
    (hyIntegral : ∀ i, yv.1 i ∈ PadicInt.subring (Rat.HeightOneSpectrum.primesEquiv v).1)
    (haIntegral : finiteAdelicUnitHeightOneComponentHom v
          (Units.map (algebraMap ℚ RationalFiniteAdele).toMonoidHom (Units.mk0 a ha)) ∈
        padicIntegralUnitsSubgroup (Rat.HeightOneSpectrum.primesEquiv v).1) :
    ∃ z : (W.nonisotropicLastExtension a ha).HeightOnePadicCliffordGeneralSpinGroup v,
      (W.nonisotropicLastExtension a ha).PadicCliffordGeneralSpinIsIntegral
          (Rat.HeightOneSpectrum.primesEquiv v).1 z ∧
        CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap
            W a ha ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1] z = yv := by
  let V := W.nonisotropicLastExtension a ha
  let p := (Rat.HeightOneSpectrum.primesEquiv v).1
  have hnpos : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  let P := V.cliffordSpinCandidateIntegralSpinorRangeGoodPlace_of_not_mem_badPlaces
    (by omega : 2 ≤ n + 1) v hvOdd
  let xInt : Fin (n + 1) → ℤ_[p] := lastCoordinateVector
  let yInt : Fin (n + 1) → ℤ_[p] := fun i =>
    ⟨yv.1 i, (PadicInt.mem_subring_iff p).mp (hyIntegral i)⟩
  have hxCast : (fun i => (xInt i : ℚ_[p])) =
      (lastCoordinateVector : Fin (n + 1) → ℚ_[p]) := by
    funext i
    cases i using Fin.lastCases <;> simp [xInt, lastCoordinateVector]
  have hyCast : (fun i => (yInt i : ℚ_[p])) = yv.1 := by
    rfl
  have hxy : P.unimodularForm.quadraticForm yInt =
      P.unimodularForm.quadraticForm xInt := by
    apply PadicInt.ext
    rw [P.coe_unimodularForm_quadraticForm,
      P.coe_unimodularForm_quadraticForm, hyCast, hxCast]
    exact yv.2.trans
      (W.lastCoordinateVector_mem_nonisotropicLastQuadraticShell a ha ℚ_[p]).symm
  let au : ℤ_[p]ˣ :=
    PositiveDefiniteIntegralLattice.padicIntUnitOfPadicIntegralUnit p
      (finiteAdelicUnitHeightOneComponentHom v
        (Units.map (algebraMap ℚ RationalFiniteAdele).toMonoidHom
          (Units.mk0 a ha))) haIntegral
  have hxUnit : IsUnit (P.unimodularForm.quadraticForm xInt) := by
    have hxa : P.unimodularForm.quadraticForm xInt = (au : ℤ_[p]) := by
      apply PadicInt.ext
      rw [P.coe_unimodularForm_quadraticForm, hxCast]
      rw [show V.commutativeScalarExtensionQuadraticForm ℚ_[p]
          (lastCoordinateVector : Fin (n + 1) → ℚ_[p]) =
            algebraMap ℚ ℚ_[p] a from
        W.lastCoordinateVector_mem_nonisotropicLastQuadraticShell a ha ℚ_[p]]
      change algebraMap ℚ ℚ_[p] a = _
      rw [PositiveDefiniteIntegralLattice.coe_padicIntUnitOfPadicIntegralUnit]
      exact (finiteAdelicCliffordGeneralSpinHeightOneAlgHom v).commutes a |>.symm
    rw [hxa]
    exact Units.isUnit au
  letI : NeZero (P.unimodularForm.orthogonalUnimodularForm xInt hxUnit).rank :=
    ⟨by
      have hr := P.unimodularForm.orthogonalUnimodularForm_rank_add_one
        xInt hxUnit
      change (P.unimodularForm.orthogonalUnimodularForm xInt hxUnit).rank + 1 =
        n + 1 at hr
      omega⟩
  obtain ⟨z, hzIntegral, hz⟩ :=
    P.exists_integral_padicCliffordGeneralSpin_mulVec_eq_of_unit_shell
      hvStructure xInt yInt hxy hxUnit
  refine ⟨z, hzIntegral, Subtype.ext ?_⟩
  dsimp only [CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap]
  simpa only [hxCast, hyCast] using hz


/-- The orbit of an integral `GSpin` point is integral. -/
theorem integral_of_padic_nonisotropicLastShellOrbitMap
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ)
    (z : (W.nonisotropicLastExtension a ha).HeightOnePadicCliffordGeneralSpinGroup v)
    (hz : (W.nonisotropicLastExtension a ha).PadicCliffordGeneralSpinIsIntegral
      (Rat.HeightOneSpectrum.primesEquiv v).1 z) (i : Fin (n + 1)) :
    (CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap
        W a ha ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1] z).1 i ∈
      PadicInt.subring (Rat.HeightOneSpectrum.primesEquiv v).1 := by
  change (z.matrixGroup.1.1.1 *ᵥ lastCoordinateVector) i ∈ _
  have hmat := ((W.nonisotropicLastExtension a ha).mem_padicSpecialOrthogonalIntegralSubgroup_iff
    _ z.matrixGroup).1 hz.2.2.2
  simpa [lastCoordinateVector, Matrix.mulVec_single_one] using hmat.1 i (Fin.last n)

end RationalQuadraticSpaceMatrix

namespace PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase

variable {n m : ℕ} (L : PositiveDefiniteIntegralLattice (n + 1)) {x : Fin (n + 1) → ℚ}
variable (P : L.rationalQuadraticSpaceMatrix.AnisotropicComplementPresentation x m) [NeZero m]
variable (hx : L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x ≠ 0)

local instance goodPlaceDecidableEq : DecidableEq (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  Classical.decEq _

local instance goodPlacePrimeFact' (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

set_option maxHeartbeats 1600000 in
/-- The good-orbit trace: off the bad places, at a place that is not odd-unimodular bad, where `a`
is a unit and `p_v ∤ D_P`, the presentation image of the local integral orbit has the integral
lattice shell as trace. -/
theorem goodOrbitTrace_of_goodPlace (M : ℤ)
    (hM : L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x = ((M : ℤ) : ℚ))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (Uv : ∀ v : {v // v ∈ P.lowerSpace.lastExtensionHorizontalBadPlaces (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx}, Subgroup ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1]ˣ)
    (Kv : ∀ v : {v // v ∈ P.lowerSpace.lastExtensionHorizontalBadPlaces (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx}, Subgroup ((P.blockSpace hx).specialOrthogonalMatrixGroup
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1]))
    (v : IsDedekindDomain.HeightOneSpectrum ℤ)
    (h : v ∈ S ∪ (P.blockSpace hx).cliffordGeneralSpinHorizontalIntegralBadPlaces) (hvB : v ∉ P.lowerSpace.lastExtensionHorizontalBadPlaces (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx)
    (hvOdd : v ∉ (P.blockSpace hx).cliffordSpinCandidateOddUnimodularBadPlaces)
    (hvUnit : finiteAdelicUnitHeightOneComponentHom v
          (Units.map (algebraMap ℚ RationalFiniteAdele).toMonoidHom (Units.mk0 (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx)) ∈
        padicIntegralUnitsSubgroup (primesEquiv v).1)
    (hvDen : ¬ (primesEquiv v : ℕ) ∣ P.presentationDenominator hx) :
    ∀ w : Fin (n + 1) → ℚ_[(primesEquiv v).1], (((L.pairingMatrix.map (Int.castRingHom ℤ_[(primesEquiv v).1])).map (PadicInt.Coe.ringHom : ℤ_[(primesEquiv v).1] →+* ℚ_[(primesEquiv v).1])).toQuadraticMap') w = (((M : ℤ) : ℤ_[(primesEquiv v).1]) : ℚ_[(primesEquiv v).1]) →
      (w ∈ (P.blockToAmbientPadicContinuousLinearEquiv hx (primesEquiv v).1) '' (Subtype.val '' ((CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap
        P.lowerSpace (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx ℚ_[(primesEquiv v).1]) '' ((P.lowerSpace.integralCompletedLocalSubgroups (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx S
          (fun v ↦ (P.blockSpace hx).padicCentralCutoffSubgroup v.1 (Uv v) (Kv v))) ⟨v, h⟩ : Set _))) ↔ ‖w‖ ≤ 1) := by
  have hbad : v ∉ (P.blockSpace hx).cliffordGeneralSpinHorizontalIntegralBadPlaces :=
    fun hb ↦ hvB (Finset.mem_union_left _ hb)
  have hs : ((P.lowerSpace.integralCompletedLocalSubgroups (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx S
          (fun v ↦ (P.blockSpace hx).padicCentralCutoffSubgroup v.1 (Uv v) (Kv v))) ⟨v, h⟩ : Set ((P.blockSpace hx).HeightOnePadicCliffordGeneralSpinGroup v)) =
      {g | (P.blockSpace hx).PadicCliffordGeneralSpinIsIntegral (primesEquiv v).1 g} := by
    unfold integralCompletedLocalSubgroups
    rw [dif_neg hvB]
    rfl
  have hunimod := P.blockToAmbientBaseChangeIsometryEquiv_mem_subring_iff hx (primesEquiv v).1 hvDen
  have hMx : algebraMap ℚ ℚ_[(primesEquiv v).1] (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) = (((M : ℤ) : ℤ_[(primesEquiv v).1]) : ℚ_[(primesEquiv v).1]) := by
    rw [hM]; exact (padicIntCast_intCast_eq_algebraMap _ M).symm
  intro w hw
  rw [hs]
  constructor
  · rintro ⟨_, ⟨z, ⟨g, hg, rfl⟩, rfl⟩, rfl⟩
    refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i ↦ ?_
    exact (hunimod _).mpr (fun j ↦ P.lowerSpace.integral_of_padic_nonisotropicLastShellOrbitMap
      (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx v g hg j) i
  · intro hw1
    set z₀ := (P.blockToAmbientPadicContinuousLinearEquiv hx (primesEquiv v).1).symm w with hz₀
    have hEz : (P.blockToAmbientPadicContinuousLinearEquiv hx (primesEquiv v).1) z₀ = w := (P.blockToAmbientPadicContinuousLinearEquiv hx (primesEquiv v).1).apply_symm_apply w
    have hz₀Q : (P.blockSpace hx).commutativeScalarExtensionQuadraticForm ℚ_[(primesEquiv v).1] z₀ =
        algebraMap ℚ ℚ_[(primesEquiv v).1] (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) := by
      rw [← latticeGram_blockToAmbient L P hx (primesEquiv v).1, hEz, hw, hMx]
    have hz₀int : ∀ i, z₀ i ∈ PadicInt.subring (primesEquiv v).1 := by
      refine (hunimod z₀).mp fun i ↦ ?_
      change (P.blockToAmbientPadicContinuousLinearEquiv hx (primesEquiv v).1) z₀ i ∈ _
      rw [hEz]
      exact (norm_le_pi_norm w i).trans hw1
    obtain ⟨g, hg, hgz⟩ := P.lowerSpace.exists_integral_padic_nonisotropicLastShellOrbitMap_eq (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx
      v hvOdd ((P.blockSpace hx).cliffordGeneralSpinIntegralStructureAt_of_not_mem_horizontalBadPlaces
        v hbad) ⟨z₀, hz₀Q⟩ hz₀int hvUnit
    exact ⟨z₀, ⟨⟨z₀, hz₀Q⟩, ⟨g, hg, hgz⟩, rfl⟩, hEz⟩

end PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase

namespace PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase

variable {n m : ℕ} (L : PositiveDefiniteIntegralLattice (n + 1)) {x : Fin (n + 1) → ℚ}
variable (P : L.rationalQuadraticSpaceMatrix.AnisotropicComplementPresentation x m) [NeZero m]
variable (hx : L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x ≠ 0)

local instance goodPlaceDecidableEq2 : DecidableEq (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  Classical.decEq _

local instance goodPlacePrimeFact2 (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

local instance gpPadicMeasurableSpace (p : ℕ) [Fact p.Prime] : MeasurableSpace ℚ_[p] := borel _
local instance gpPadicBorelSpace (p : ℕ) [Fact p.Prime] : BorelSpace ℚ_[p] := ⟨rfl⟩

section Ratio

local instance : MeasurableSpace (P.lowerSpace.nonisotropicLastQuadraticShell
    (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx RationalAdele) := borel _
local instance : BorelSpace (P.lowerSpace.nonisotropicLastQuadraticShell
    (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx RationalAdele) := ⟨rfl⟩

variable (hn : 4 < n + 1) {b : ℝ} (hb : 0 < b)
variable (x₀ : adelicValueFiber L (algebraMap ℚ RationalAdele
  (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x)))
variable (K : Subgroup L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalGroup)
variable (hc : IsCompact (K : Set L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalGroup))
variable (ho : IsOpen (K : Set L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalGroup))
include hn hc ho

set_option maxHeartbeats 4000000 in
/-- The orbit Riesz ratio with the local densities cancelled, with the good-orbit traces
discharged from local good-place conditions on `S \ B`. -/
theorem exists_div_nativeShellMeasure_eq_localScale_eulerProduct_of_goodPlaces
    (M : ℤ) (hM : L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x = ((M : ℤ) : ℚ))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (hodd : (P.blockSpace hx).cliffordSpinCandidateOddUnimodularBadPlaces ⊆
      S ∪ (P.blockSpace hx).cliffordGeneralSpinHorizontalIntegralBadPlaces)
    (haunit : ∀ v, v ∉ S ∪ (P.blockSpace hx).cliffordGeneralSpinHorizontalIntegralBadPlaces →
      finiteAdelicUnitHeightOneComponentHom v
          (Units.map (algebraMap ℚ RationalFiniteAdele).toMonoidHom
            (Units.mk0 (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx)) ∈
        padicIntegralUnitsSubgroup (primesEquiv v).1)
    (hden : ∀ v : IsDedekindDomain.HeightOneSpectrum ℤ,
      v ∉ S ∪ (P.blockSpace hx).cliffordGeneralSpinHorizontalIntegralBadPlaces →
      ¬ (primesEquiv v : ℕ) ∣ P.presentationDenominator hx)
    {T : Set ℝˣ} (hT : MeasurableSet T) (hneg : ∀ t : ℝˣ, -t ∈ T ↔ t ∈ T)
    (hT0 : (Measure.haar : Measure ℝˣ) T ≠ 0) (hTtop : (Measure.haar : Measure ℝˣ) T ≠ ⊤)
    (hSB : P.lowerSpace.lastExtensionHorizontalBadPlaces (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx ⊆ S)
    (Uv : ∀ v : {v // v ∈ P.lowerSpace.lastExtensionHorizontalBadPlaces (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx},
      Subgroup ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1]ˣ)
    (hU : ∀ (v : {v // v ∈ P.lowerSpace.lastExtensionHorizontalBadPlaces (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx}),
      IsOpen (Uv v : Set ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1]ˣ))
    (hUc : ∀ (v : {v // v ∈ P.lowerSpace.lastExtensionHorizontalBadPlaces (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx}),
      IsCompact (Uv v : Set ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1]ˣ))
    (Kv : ∀ v : {v // v ∈ P.lowerSpace.lastExtensionHorizontalBadPlaces (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx},
      Subgroup ((P.blockSpace hx).specialOrthogonalMatrixGroup
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1]))
    (hK : ∀ (v : {v // v ∈ P.lowerSpace.lastExtensionHorizontalBadPlaces (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx}),
      IsOpen (Kv v : Set ((P.blockSpace hx).specialOrthogonalMatrixGroup
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1])))
    (hKc : ∀ (v : {v // v ∈ P.lowerSpace.lastExtensionHorizontalBadPlaces (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx}),
      IsCompact (Kv v : Set ((P.blockSpace hx).specialOrthogonalMatrixGroup
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1])))
    (hlift : ∀ (v : {v // v ∈ P.lowerSpace.lastExtensionHorizontalBadPlaces (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx}), ∀ g ∈ Kv v,
      ∃ y : (P.blockSpace hx).CliffordGeneralSpinIntrinsicPoint
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1],
      y.similitude ∈ Uv v ∧ CliffordGeneralSpinIntrinsicPoint.toSpecialOrthogonalGroupHom _ _ y = g)
    (c : {v // v ∈ P.lowerSpace.lastExtensionHorizontalBadPlaces (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx} → ℝ≥0∞)
    (hloc : ∀ (v : {v // v ∈ P.lowerSpace.lastExtensionHorizontalBadPlaces (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx}),
      (P.blockSpace hx).padicInvariantDifferentialGroupMeasure
          (Rat.HeightOneSpectrum.primesEquiv v.1).1
          (Kv v : Set ((P.blockSpace hx).specialOrthogonalMatrixGroup
            ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1])) =
        P.lowerSpace.padicInvariantDifferentialGroupMeasure (Rat.HeightOneSpectrum.primesEquiv v.1).1
            (P.lowerSpace.nonisotropicLastCoordinateFiberEmbedGroup (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx
              ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1] ⁻¹'
                (Kv v : Set ((P.blockSpace hx).specialOrthogonalMatrixGroup
                  ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1]))) * c v)
    (hW : (P.lowerSpace.pairingMatrix.map (algebraMap ℚ ℝ)).PosDef) (ha0 : 0 < (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x))
    (hc0 : ∀ v, c v ≠ 0) (hct : ∀ v, c v ≠ ⊤)
    (hOint : ∀ (v : IsDedekindDomain.HeightOneSpectrum ℤ)
      (h : v ∈ S ∪ (P.blockSpace hx).cliffordGeneralSpinHorizontalIntegralBadPlaces),
      ∀ z ∈ (CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap P.lowerSpace
        (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx
        ℚ_[(primesEquiv v).1]) '' ((P.lowerSpace.integralCompletedLocalSubgroups (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx S
        (fun v ↦ (P.blockSpace hx).padicCentralCutoffSubgroup v.1 (Uv v) (Kv v))) ⟨v, h⟩ : Set _), ∀ i,
        P.blockToAmbientBaseChangeIsometryEquiv hx ℚ_[(primesEquiv v).1] z.1 i ∈
          PadicInt.subring (primesEquiv v).1)
    (r : {v // v ∈ P.lowerSpace.lastExtensionHorizontalBadPlaces (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx} → ℝ≥0∞) (hr0 : ∀ v, r v ≠ 0) (hrt : ∀ v, r v ≠ ⊤)
    (hstab : ∀ (v : {v // v ∈ P.lowerSpace.lastExtensionHorizontalBadPlaces (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx}) (point₁ : ℕ → Fin (m + 1) → ℚ_[(primesEquiv v.1).1])
      (hpoint₁ : ∀ i, ((P.blockSpace hx).commutativeScalarExtensionQuadraticForm ℚ_[(primesEquiv v.1).1]) (point₁ i) ≠ 0),
      {w | ((P.blockSpace hx).commutativeScalarExtensionQuadraticForm ℚ_[(primesEquiv v.1).1]) w ≠ 0} ⊆ ⋃ i, ((P.blockSpace hx).commutativeScalarExtensionQuadraticForm ℚ_[(primesEquiv v.1).1]).padicSquareBranchAtlasRegion (primesEquiv v.1).1 point₁ hpoint₁ i →
      ∀ Tb : Set (Fin (m + 1) → ℚ_[(primesEquiv v.1).1]), MeasurableSet Tb →
        Tb ∩ {z | ((P.blockSpace hx).commutativeScalarExtensionQuadraticForm ℚ_[(primesEquiv v.1).1]) z = (((M : ℤ) : ℤ_[(primesEquiv v.1).1]) : ℚ_[(primesEquiv v.1).1])} = Subtype.val '' ((CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap P.lowerSpace (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx ℚ_[(primesEquiv v.1).1]) '' ((P.lowerSpace.integralCompletedLocalSubgroups (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx S
          (fun v ↦ (P.blockSpace hx).padicCentralCutoffSubgroup v.1 (Uv v) (Kv v))) ⟨v.1, Finset.mem_union_left _ (hSB v.2)⟩ : Set _)) →
        (P.blockSpace hx).padicInvariantDifferentialGroupMeasure (primesEquiv v.1).1
            (Kv v : Set ((P.blockSpace hx).specialOrthogonalMatrixGroup ℚ_[(primesEquiv v.1).1])) =
          r v * P.lowerSpace.padicInvariantDifferentialGroupMeasure (primesEquiv v.1).1
            (P.lowerSpace.nonisotropicLastCoordinateFiberEmbedGroup (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx ℚ_[(primesEquiv v.1).1] ⁻¹'
              (Kv v : Set ((P.blockSpace hx).specialOrthogonalMatrixGroup ℚ_[(primesEquiv v.1).1]))) *
            ((Measure.addHaar : Measure ℚ_[(primesEquiv v.1).1]) (Metric.closedBall 0 1) * ((P.blockSpace hx).commutativeScalarExtensionQuadraticForm ℚ_[(primesEquiv v.1).1]).padicSquareBranchAtlasGlue (primesEquiv v.1).1 point₁ hpoint₁ (fun _ ↦ Measure.addHaar) Measure.addHaar (Padic.unitHaar (primesEquiv v.1).1 (Fin (m + 1))) (((M : ℤ) : ℤ_[(primesEquiv v.1).1]) : ℚ_[(primesEquiv v.1).1]) (Subtype.val ⁻¹' Tb)))
    (hgp : ∀ v ∈ S, v ∉ P.lowerSpace.lastExtensionHorizontalBadPlaces (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx →
      v ∉ (P.blockSpace hx).cliffordSpinCandidateOddUnimodularBadPlaces ∧
      finiteAdelicUnitHeightOneComponentHom v
          (Units.map (algebraMap ℚ RationalFiniteAdele).toMonoidHom (Units.mk0 (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx)) ∈
        padicIntegralUnitsSubgroup (primesEquiv v).1 ∧
      ¬ (primesEquiv v : ℕ) ∣ P.presentationDenominator hx) :
    ∃ (e : ℕ → ℕ) (R : ∀ p : ℕ, Set (Fin (n + 1) → ZMod (p ^ e p))) (gF gR : ℕ → ℝ≥0∞)
      (D : IsDedekindDomain.HeightOneSpectrum ℤ → ℝ≥0∞),
      (∀ p ∈ placeBlockPrimes (S ∪ (P.blockSpace hx).cliffordGeneralSpinHorizontalIntegralBadPlaces), p.Prime ∧ 1 ≤ e p) ∧
      (∀ p ∈ placeBlockPrimes (S ∪ (P.blockSpace hx).cliffordGeneralSpinHorizontalIntegralBadPlaces), ∀ᶠ v : ℕ in Filter.atTop,
        (L.restrictedResidueCount M (placeBlockPrimes (S ∪ (P.blockSpace hx).cliffordGeneralSpinHorizontalIntegralBadPlaces)) e R (p ^ v) : ℝ≥0∞) * gF p =
          (L.fullResidueCount M (p ^ v) : ℝ≥0∞) * gR p) ∧
      (∀ (v : IsDedekindDomain.HeightOneSpectrum ℤ) (h : v ∈ P.lowerSpace.lastExtensionHorizontalBadPlaces (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx), D v ≠ 0 ∧ D v ≠ ⊤ ∧
        ∀ (point₁ : ℕ → Fin (m + 1) → ℚ_[(primesEquiv v).1]) (hpoint₁ : ∀ i, ((P.blockSpace hx).commutativeScalarExtensionQuadraticForm ℚ_[(primesEquiv v).1]) (point₁ i) ≠ 0),
          {w | ((P.blockSpace hx).commutativeScalarExtensionQuadraticForm ℚ_[(primesEquiv v).1]) w ≠ 0} ⊆ ⋃ i, ((P.blockSpace hx).commutativeScalarExtensionQuadraticForm ℚ_[(primesEquiv v).1]).padicSquareBranchAtlasRegion (primesEquiv v).1 point₁ hpoint₁ i →
          D v = r ⟨v, h⟩ * ((Measure.addHaar : Measure ℚ_[(primesEquiv v).1]) (Metric.closedBall 0 1) * ((P.blockSpace hx).commutativeScalarExtensionQuadraticForm ℚ_[(primesEquiv v).1]).padicSquareBranchAtlasGlue (primesEquiv v).1 point₁ hpoint₁ (fun _ ↦ Measure.addHaar) Measure.addHaar (Padic.unitHaar (primesEquiv v).1 (Fin (m + 1))) (((M : ℤ) : ℤ_[(primesEquiv v).1]) : ℚ_[(primesEquiv v).1]) (Subtype.val ⁻¹' ((P.blockToAmbientPadicContinuousLinearEquiv hx (primesEquiv v).1) ⁻¹' Metric.closedBall 0 1)))) ∧
      let a := algebraMap ℚ RationalAdele (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x)
      let σ := gaussianFiberMeasure L hn hb a
      let Mn := nativeShellMeasureOnValueFiber L P hx
      let U := (fun g ↦ g • x₀) ''
        (K : Set L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalGroup)
      σ U / Mn U =
        (P.blockToAmbientFullAdelicGeneralSpinHorizontalHaarScalar hx : ℝ≥0∞) *
          (ENNReal.ofReal ((L.rationalQuadraticSpaceMatrix.realLocalValueDensity
                (gaussianOrbitTestRealFactor L b a) (rationalAdeleRealScalar a)).re *
                  ∏' p : Nat.Primes, L.localResidueDensity M p) *
              (P.lowerSpace.realInvariantDifferentialGroupMeasure Set.univ *
                ∏ v : {v // v ∈ P.lowerSpace.lastExtensionHorizontalBadPlaces (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx}, P.lowerSpace.cliffordGeneralSpinHorizontalBaselineScale v.1) /
            ((∏ v ∈ P.lowerSpace.lastExtensionHorizontalBadPlaces (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx, D v) *
              ((P.blockSpace hx).realInvariantDifferentialGroupMeasure Set.univ *
                ∏ v : {v // v ∈ P.lowerSpace.lastExtensionHorizontalBadPlaces (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx},
                  (P.blockSpace hx).cliffordGeneralSpinHorizontalBaselineScale v.1))) :=
  exists_div_nativeShellMeasure_eq_localScale_eulerProduct L P hx hn hb x₀ K hc ho M hM S hodd haunit
    hden hT hneg hT0 hTtop hSB Uv hU hUc Kv hK hKc hlift c hloc hW ha0 hc0 hct hOint r hr0 hrt hstab
    (fun v h hvB ↦ by
      have hvS : v ∈ S := by
        rcases Finset.mem_union.1 h with hS | hb
        · exact hS
        · exact (hvB (Finset.mem_union_left _ hb)).elim
      obtain ⟨h1, h2, h3⟩ := hgp v hvS hvB
      exact goodOrbitTrace_of_goodPlace L P hx M hM S Uv Kv v h hvB h1 h2 h3)

end Ratio

end PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase
