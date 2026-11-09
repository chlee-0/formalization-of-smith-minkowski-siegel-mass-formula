import SMSFormula.RationalCliffordGeneralSpinPadicShellOrbitOpen
import SMSFormula.RationalCliffordGeneralSpinHorizontalCylinderOrbitPadicCentralCutoffCompact
import SMSFormula.RationalCliffordGeneralSpinFieldSurjectivity
import SMSFormula.RationalCliffordGeneralSpinAdelicTopology
import SMSFormula.RationalCliffordSpinCandidatePlacewiseImageOpennessPrecursor

/-!
# Compact open subgroups of `SO(ℚ_p)` with unit-similitude `GSpin` lifts

Over `ℚ_p` the `GSpin → SO` map is surjective (Cartan--Dieudonné field surjectivity) and
continuous. The source is `σ`-compact (local compactness plus a second-countable closed coordinate
embedding) and the target is locally compact Hausdorff, so Mathlib's open-mapping theorem makes it
open.

Hence for every compact open subgroup `K ≤ SO(ℚ_p)` the image
`K' = toSO {y : ν(y) ∈ ℤ_p^×, toSO(y) ∈ K} ≤ K`
is a compact open subgroup. Every element of `K'` lifts to `GSpin` with unit similitude. These are
exactly the "orbit-mass inputs" `U_v = ℤ_p^×`, `K_v`, `hlift` of the central-cutoff chain.
Nothing is chosen.
-/

noncomputable section

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

/-- The `ℚ_p` `GSpin → SO` map is open (Mathlib open mapping; surjectivity). -/
theorem isOpenMap_padicCliffordGeneralSpinToSpecialOrthogonalHom (p : ℕ) [Fact p.Prime] :
    IsOpenMap (V.padicCliffordGeneralSpinToSpecialOrthogonalHom p) := by
  letI : LocallyCompactSpace (V.CliffordGeneralSpinIntrinsicPoint ℚ_[p]) :=
    V.padicCliffordGeneralSpinGroupLocallyCompactSpace p
  letI : SecondCountableTopology (V.CliffordGeneralSpinIntrinsicPoint ℚ_[p]) :=
    (V.cliffordGeneralSpinClosedCoordinateMap_isClosedEmbedding ℚ_[p]).isEmbedding
      |>.secondCountableTopology
  exact MonoidHom.isOpenMap_of_sigmaCompact _
    (CliffordGeneralSpinIntrinsicPoint.toSpecialOrthogonalGroupHom_surjective V ℚ_[p])
    (V.continuous_padicCliffordGeneralSpinToSpecialOrthogonalHom p)

variable (v : IsDedekindDomain.HeightOneSpectrum ℤ)

local instance pusiPrimeFact : Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

/-- The unit-similitude image subgroup over a supplied subgroup `K ≤ SO(ℚ_p)`. -/
def padicUnitSimilitudeImage
    (K : Subgroup (V.specialOrthogonalMatrixGroup ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1])) :
    Subgroup (V.specialOrthogonalMatrixGroup ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]) :=
  (V.padicCentralCutoffSubgroup v (padicIntegralUnitsSubgroup (Rat.HeightOneSpectrum.primesEquiv v).1)
    K).map (V.padicCliffordGeneralSpinToSpecialOrthogonalHom (Rat.HeightOneSpectrum.primesEquiv v).1)

variable {V v}

theorem padicUnitSimilitudeImage_le
    (K : Subgroup (V.specialOrthogonalMatrixGroup ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1])) :
    V.padicUnitSimilitudeImage v K ≤ K := by
  rintro _ ⟨y, hy, rfl⟩
  exact hy.2

/-- Every element of the image lifts with unit similitude. -/
theorem exists_lift_of_mem_padicUnitSimilitudeImage
    (K : Subgroup (V.specialOrthogonalMatrixGroup ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]))
    (g : V.specialOrthogonalMatrixGroup ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1])
    (hg : g ∈ V.padicUnitSimilitudeImage v K) :
    ∃ y : V.CliffordGeneralSpinIntrinsicPoint ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1],
      y.similitude ∈ padicIntegralUnitsSubgroup (Rat.HeightOneSpectrum.primesEquiv v).1 ∧
        CliffordGeneralSpinIntrinsicPoint.toSpecialOrthogonalGroupHom _ _ y = g := by
  obtain ⟨y, hy, rfl⟩ := hg
  exact ⟨y, hy.1, rfl⟩

theorem isCompact_padicUnitSimilitudeImage
    {K : Subgroup (V.specialOrthogonalMatrixGroup ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1])}
    (hK : IsCompact (K : Set (V.specialOrthogonalMatrixGroup ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]))) :
    IsCompact (V.padicUnitSimilitudeImage v K :
      Set (V.specialOrthogonalMatrixGroup ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1])) := by
  rw [padicUnitSimilitudeImage, Subgroup.coe_map]
  exact (V.isCompact_padicCentralCutoffSubgroup v _ K
    (isCompact_padicIntegralUnitsSubgroup _) hK).image
    (V.continuous_padicCliffordGeneralSpinToSpecialOrthogonalHom _)

theorem isOpen_padicUnitSimilitudeImage
    {K : Subgroup (V.specialOrthogonalMatrixGroup ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1])}
    (hK : IsOpen (K : Set (V.specialOrthogonalMatrixGroup ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]))) :
    IsOpen (V.padicUnitSimilitudeImage v K :
      Set (V.specialOrthogonalMatrixGroup ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1])) := by
  rw [padicUnitSimilitudeImage, Subgroup.coe_map]
  refine V.isOpenMap_padicCliffordGeneralSpinToSpecialOrthogonalHom _ _ ?_
  rw [coe_padicCentralCutoffSubgroup]
  exact ((isOpen_padicIntegralUnitsSubgroup _).prod hK).preimage
    (V.continuous_centralFiberGroupHom_padic _)

end RationalQuadraticSpaceMatrix
