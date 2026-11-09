import SMSFormula.RationalCliffordGeneralSpinHorizontalCylinderOrbitPadicCentralCutoff

/-!
# Compactness of p-adic central cutoff subgroups

A continuous group homomorphism `φ : G → H` of a weakly locally compact group into a Hausdorff
group, which is open at the identity and has finite kernel, pulls compact sets back to compact
sets: an ultrafilter on `φ⁻¹C` pushes forward to a limit `c = φ g` in the closed open image, and
then lives eventually in the compact set `g · N · ker φ` for a compact neighbourhood `N` of `1`.

The p-adic central fiber map `φ = (ν, toSO)` has kernel `{1, z}` and is open at `1` (old
identity chart), so `{ν ∈ U, toSO ∈ K}` is compact for compact `U` and `K`.  This discharges the
compactness hypothesis of the bad-place orbit identity for compact open `U_v`, `K_v`, and the
finiteness of `Haar(U_v ⊓ (ℚ_p^×)²)`.
-/

noncomputable section

open MeasureTheory Set Filter Topology PositiveDefiniteIntegralLattice
open scoped ENNReal

/-- A continuous hom, open at the identity with finite kernel, from a weakly locally compact
group to a Hausdorff group pulls compact sets back to compact sets. -/
theorem MonoidHom.isCompact_preimage_of_image_mem_nhds_one_of_finite_ker
    {G H : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [WeaklyLocallyCompactSpace G] [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [T2Space H] (φ : G →* H) (hφ : Continuous φ)
    (hopen : ∀ U ∈ 𝓝 (1 : G), φ '' U ∈ 𝓝 (1 : H)) (hker : (φ.ker : Set G).Finite)
    {C : Set H} (hC : IsCompact C) : IsCompact (φ ⁻¹' C) := by
  rw [isCompact_iff_ultrafilter_le_nhds]
  intro f hf
  obtain ⟨N, hNc, hN⟩ := exists_compact_mem_nhds (1 : G)
  have hR : IsClosed (φ.range : Set H) := by
    have hmem : (φ.range : Set H) ∈ 𝓝 (1 : H) :=
      mem_of_superset (hopen N hN) (by rintro _ ⟨x, -, rfl⟩; exact ⟨x, rfl⟩)
    exact Subgroup.isClosed_of_isOpen _ (Subgroup.isOpen_of_mem_nhds _ hmem)
  have hfC : (f.map φ : Filter H) ≤ 𝓟 C := by
    rw [Ultrafilter.coe_map]
    refine (Filter.map_mono hf).trans ?_
    rw [Filter.map_principal]
    exact Filter.principal_mono.mpr (Set.image_preimage_subset φ C)
  obtain ⟨c, -, hc⟩ := hC.ultrafilter_le_nhds (f.map φ) hfC
  rw [Ultrafilter.coe_map] at hc
  have hcR : c ∈ (φ.range : Set H) :=
    hR.mem_of_tendsto hc (Eventually.of_forall fun x ↦ ⟨x, rfl⟩)
  obtain ⟨g, rfl⟩ := hcR
  let A : Set G := (fun q : G × G ↦ g * q.1 * q.2) '' (N ×ˢ (φ.ker : Set G))
  have hA : IsCompact A :=
    (hNc.prod hker.isCompact).image (by fun_prop)
  have hev : ∀ᶠ x in (f : Filter G), x ∈ A := by
    have h1 : (fun h ↦ (φ g)⁻¹ * h) ⁻¹' (φ '' N) ∈ 𝓝 (φ g) := by
      apply (continuous_const.mul continuous_id).continuousAt.preimage_mem_nhds
      simpa using hopen N hN
    filter_upwards [hc h1] with x hx
    obtain ⟨m, hmN, hm⟩ := hx
    refine ⟨(m, m⁻¹ * g⁻¹ * x), ⟨hmN, ?_⟩, by group⟩
    change m⁻¹ * g⁻¹ * x ∈ φ.ker
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_inv, map_inv, hm]
    group
  obtain ⟨x, -, hx⟩ := hA.ultrafilter_le_nhds f (Filter.le_principal_iff.mpr hev)
  exact ⟨x, (hC.isClosed.preimage hφ).mem_of_tendsto (tendsto_id'.mpr hx)
    (Filter.le_principal_iff.mp hf), hx⟩

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

set_option synthInstance.maxHeartbeats 700000
set_option maxHeartbeats 2400000

local instance cylPadicCompactDecidableEq :
    DecidableEq (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  Classical.decEq _

local instance cylPadicCompactPrimeFact (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

noncomputable local instance cylPadicCompactSOMeasurableSpace (V : RationalQuadraticSpaceMatrix n)
    (p : ℕ) [Fact (Nat.Prime p)] :
    MeasurableSpace (V.specialOrthogonalMatrixGroup ℚ_[p]) :=
  V.padicSpecialOrthogonalGroupMeasurableSpace_spinorNorm p

noncomputable local instance cylPadicCompactSOBorelSpace (V : RationalQuadraticSpaceMatrix n)
    (p : ℕ) [Fact (Nat.Prime p)] :
    BorelSpace (V.specialOrthogonalMatrixGroup ℚ_[p]) :=
  V.padicSpecialOrthogonalGroupBorelSpace_spinorNorm p

/-- The p-adic central fiber map pulls compact sets back to compact sets. -/
theorem isCompact_preimage_centralFiberGroupHom_padic (V : RationalQuadraticSpaceMatrix n)
    (p : ℕ) [Fact (Nat.Prime p)] {C : Set (ℚ_[p]ˣ × V.specialOrthogonalMatrixGroup ℚ_[p])}
    (hC : IsCompact C) :
    IsCompact (CliffordGeneralSpinIntrinsicPoint.centralFiberGroupHom V ℚ_[p] ⁻¹' C) := by
  letI : LocallyCompactSpace (V.CliffordGeneralSpinIntrinsicPoint ℚ_[p]) :=
    V.padicCliffordGeneralSpinGroupLocallyCompactSpace p
  refine MonoidHom.isCompact_preimage_of_image_mem_nhds_one_of_finite_ker _
    (V.continuous_centralFiberGroupHom_padic p) ?_ ?_ hC
  · intro U hU
    have hone := V.one_mem_padicCliffordGeneralSpinCentralFiberIdentityChart_source p
    have h := (V.padicCliffordGeneralSpinCentralFiberIdentityChart p).image_mem_nhds hone hU
    rw [← V.padicCliffordGeneralSpinCentralFiberIdentityChart_coe p, map_one] at h
    exact h
  · rw [CliffordGeneralSpinIntrinsicPoint.centralFiberGroupHom_ker_eq_pair]
    exact Set.toFinite _

/-- The p-adic central cutoff subgroup `{ν ∈ U, toSO ∈ K}` is compact for compact `U`, `K`. -/
theorem isCompact_padicCentralCutoffSubgroup (V : RationalQuadraticSpaceMatrix n)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ)
    (U : Subgroup ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]ˣ)
    (K : Subgroup (V.specialOrthogonalMatrixGroup ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]))
    (hU : IsCompact (U : Set ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]ˣ))
    (hK : IsCompact (K : Set (V.specialOrthogonalMatrixGroup ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]))) :
    IsCompact (V.padicCentralCutoffSubgroup v U K : Set (V.HeightOnePadicCliffordGeneralSpinGroup v)) := by
  rw [coe_padicCentralCutoffSubgroup]
  exact V.isCompact_preimage_centralFiberGroupHom_padic _ (hU.prod hK)

/-- The fixed-last-coordinate embedding `e : SO(W) → SO(W ⊕ ⟨a⟩)` is continuous. -/
theorem continuous_nonisotropicLastCoordinateFiberEmbedGroup
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (A : Type*) [CommRing A] [Algebra ℚ A] [TopologicalSpace A] [IsTopologicalRing A] :
    Continuous (W.nonisotropicLastCoordinateFiberEmbedGroup a ha A) := by
  have hval : Continuous (fun h : W.specialOrthogonalMatrixGroup A ↦ h.1.1) :=
    continuous_subtype_val.comp continuous_subtype_val
  have hU : Continuous (fun h : W.specialOrthogonalMatrixGroup A ↦
      (W.nonisotropicLastCoordinateFiberEmbedGroup a ha A h).1.1) := by
    refine Units.continuous_iff.2 ⟨?_, ?_⟩
    · exact continuous_fixLastBlockMatrix.comp (Units.continuous_val.comp hval)
    · have hinv : ∀ h : W.specialOrthogonalMatrixGroup A,
          (((W.nonisotropicLastCoordinateFiberEmbedGroup a ha A h).1.1)⁻¹ : _) =
            fixLastBlockMatrix ((h.1.1⁻¹).1) := fun h ↦ by
        have := congrArg (fun g : (W.nonisotropicLastExtension a ha).specialOrthogonalMatrixGroup A ↦
          g.1.1.1) (map_inv (W.nonisotropicLastCoordinateFiberEmbedHom a ha A) h)
        exact this.symm
      simp_rw [hinv]
      exact continuous_fixLastBlockMatrix.comp (Units.continuous_coe_inv.comp hval)
  exact continuous_induced_rng.2 (continuous_induced_rng.2 hU)

variable (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)

/-- The bad-place orbit identity in special-orthogonal volumes for supplied compact open
`U_v ≤ ℚ_p^×` and `K_v ≤ SO(V)(ℚ_p)` whose points lift with similitude in `U_v`:

`N(K•x) · μ_{SO_W}(SO(ℝ)) · ∏_B s_W(v) μ_{SO_W}(e⁻¹K_v) = μ_{SO_V}(SO(ℝ)) · ∏_B s_V(v) μ_{SO_V}(K_v)`.

Compactness of the cutoff subgroups, measurability of `e⁻¹K_v` (continuity of `e`) and finiteness of
the central constants are discharged; only the spinor-norm lift hypothesis remains. -/
theorem fullAdelicNonisotropicLastShellMeasure_cylinderOrbit_badPlaces_padicCentralCutoff_compact
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
      y.similitude ∈ U v ∧ CliffordGeneralSpinIntrinsicPoint.toSpecialOrthogonalGroupHom _ _ y = g) :
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
                  ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1] ⁻¹'
                    (K v : Set ((W.nonisotropicLastExtension a ha).specialOrthogonalMatrixGroup
                      ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1]))))) =
      (W.nonisotropicLastExtension a ha).realInvariantDifferentialGroupMeasure Set.univ *
        ∏ v : {v // v ∈ W.lastExtensionHorizontalBadPlaces a ha},
          (W.nonisotropicLastExtension a ha).cliffordGeneralSpinHorizontalBaselineScale v.1 *
            ((W.nonisotropicLastExtension a ha).padicInvariantDifferentialGroupMeasure
                (Rat.HeightOneSpectrum.primesEquiv v.1).1
                  (K v : Set ((W.nonisotropicLastExtension a ha).specialOrthogonalMatrixGroup
                    ℚ_[(Rat.HeightOneSpectrum.primesEquiv v.1).1]))) :=
  W.fullAdelicNonisotropicLastShellMeasure_cylinderOrbit_badPlaces_padicCentralCutoff_cancel a ha
    hT hneg hT0 hTtop hSB U hU K hK
    (fun v ↦ ((hK v).preimage
      (W.continuous_nonisotropicLastCoordinateFiberEmbedGroup a ha _)).measurableSet) hlift
    (fun v ↦ (W.nonisotropicLastExtension a ha).isCompact_padicCentralCutoffSubgroup v.1 (U v) (K v)
      (hUc v) (hKc v))
    (fun v ↦ ((hUc v).measure_lt_top.trans_le' (measure_mono inf_le_left)).ne)

end RationalQuadraticSpaceMatrix
