import SMSFormula.RationalCliffordGeneralSpinVerticalPositiveOrbitalRetainedOuterCarrierRestriction

/-!
# Retained orbital source substitution

The retained-base disintegration fixes a square-root coordinate before the
Spin orbital integral is evaluated.  This file records the
source-level compatibility: on the chosen local identity sheet, a
fixed scalar from the square-chart source does not change which Spin points
land in the intrinsic `GSpin` identity carrier.

Only the square and Spin identity charts are used.
-/

noncomputable section

open MeasureTheory
open PositiveDefiniteIntegralLattice

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

set_option synthInstance.maxHeartbeats 700000
set_option maxHeartbeats 2400000

/-- Central scalar points commute with intrinsic general-Spin points. -/
theorem scalarGroupHom_mul_comm
    (A : Type*) [CommRing A] [Algebra ℚ A]
    (a : Aˣ) (g : V.CliffordGeneralSpinIntrinsicPoint A) :
    CliffordGeneralSpinIntrinsicPoint.scalarGroupHom V A a * g =
      g * CliffordGeneralSpinIntrinsicPoint.scalarGroupHom V A a := by
  apply CliffordGeneralSpinIntrinsicPoint.ext_cliffordUnit V A
  apply Units.ext
  change algebraMap A (V.cliffordCoordinateBaseChangeAlgebra A) (a : A) *
      (g.cliffordUnit : V.cliffordCoordinateBaseChangeAlgebra A) =
    (g.cliffordUnit : V.cliffordCoordinateBaseChangeAlgebra A) *
      algebraMap A (V.cliffordCoordinateBaseChangeAlgebra A) (a : A)
  exact Algebra.commutes (a : A) _

/-- On the real identity sheet, fixing a scalar in the chosen square branch
leaves exactly the existing Spin-chart source. -/
theorem scalar_mul_spin_mem_realCentralFiberIdentityChart_iff
    (a : ℝˣ) (ha : a ∈ (Rat.unitSquareIdentityChart ℝ).source)
    (s : V.RealCliffordSpinCandidateGroup) :
    CliffordGeneralSpinIntrinsicPoint.scalarGroupHom V ℝ a *
          V.cliffordSpinCandidateToCliffordGeneralSpinHom ℝ s ∈
        V.realCliffordGeneralSpinCentralFiberIdentityChart.source ↔
      s ∈ V.realCliffordSpinCandidateIdentityChart.source := by
  let c := V.realCliffordGeneralSpinCentralSpinIdentityChart
  change V.cliffordGeneralSpinCentralSpinMultiplication ℝ (a, s) ∈ c.target ↔ _
  constructor
  · rintro ⟨y, hy, hya⟩
    have hsq : (y.1 : ℝ) ^ 2 = (a : ℝ) ^ 2 := by
      simpa using congrArg
        (fun z : V.RealCliffordGeneralSpinGroup => (z.similitude : ℝ)) hya
    rcases (sq_eq_sq_iff_eq_or_eq_neg.mp hsq) with hsame | hneg
    · have hy1 : y.1 = a := Units.ext hsame
      have hspin :
          V.cliffordSpinCandidateToCliffordGeneralSpinHom ℝ y.2 =
            V.cliffordSpinCandidateToCliffordGeneralSpinHom ℝ s := by
        have h := hya
        change
          CliffordGeneralSpinIntrinsicPoint.scalarGroupHom V ℝ y.1 *
              V.cliffordSpinCandidateToCliffordGeneralSpinHom ℝ y.2 =
            CliffordGeneralSpinIntrinsicPoint.scalarGroupHom V ℝ a *
              V.cliffordSpinCandidateToCliffordGeneralSpinHom ℝ s at h
        rw [hy1] at h
        exact mul_left_cancel h
      have hy2 : y.2 = s :=
        V.cliffordSpinCandidateToCliffordGeneralSpinHom_injective ℝ hspin
      simpa [hy2] using hy.2
    · have hy1 : y.1 = -a := Units.ext hneg
      have hnegSource : -a ∈ (Rat.unitSquareIdentityChart ℝ).source := by
        simpa [hy1] using hy.1
      have hunit : (-a : ℝˣ) = a :=
        (Rat.unitSquareIdentityChart ℝ).injOn hnegSource ha (by simp)
      have hnegone : (-1 : ℝˣ) = 1 := by
        calc
          (-1 : ℝˣ) = (-a) * a⁻¹ := by simp
          _ = a * a⁻¹ := by rw [hunit]
          _ = 1 := by simp
      have hval := congrArg Units.val hnegone
      norm_num at hval
  · intro hs
    change V.cliffordGeneralSpinCentralSpinMultiplication ℝ (a, s) ∈ c.target
    exact c.map_source ⟨ha, hs⟩

/-- The same fixed-square-source statement at every p-adic place. -/
theorem scalar_mul_spin_mem_padicCentralFiberIdentityChart_iff
    (p : ℕ) [Fact (Nat.Prime p)]
    (a : ℚ_[p]ˣ) (ha : a ∈ (Rat.unitSquareIdentityChart ℚ_[p]).source)
    (s : V.PadicCliffordSpinCandidateGroup p) :
    CliffordGeneralSpinIntrinsicPoint.scalarGroupHom V ℚ_[p] a *
          V.cliffordSpinCandidateToCliffordGeneralSpinHom ℚ_[p] s ∈
        (V.padicCliffordGeneralSpinCentralFiberIdentityChart p).source ↔
      s ∈ (V.padicCliffordSpinCandidateIdentityChart p).source := by
  let c := V.padicCliffordGeneralSpinCentralSpinIdentityChart p
  change V.cliffordGeneralSpinCentralSpinMultiplication ℚ_[p] (a, s) ∈ c.target ↔ _
  constructor
  · rintro ⟨y, hy, hya⟩
    have hsq : (y.1 : ℚ_[p]) ^ 2 = (a : ℚ_[p]) ^ 2 := by
      simpa using congrArg
        (fun z : V.PadicCliffordGeneralSpinGroup p => (z.similitude : ℚ_[p])) hya
    rcases (sq_eq_sq_iff_eq_or_eq_neg.mp hsq) with hsame | hneg
    · have hy1 : y.1 = a := Units.ext hsame
      have hspin :
          V.cliffordSpinCandidateToCliffordGeneralSpinHom ℚ_[p] y.2 =
            V.cliffordSpinCandidateToCliffordGeneralSpinHom ℚ_[p] s := by
        have h := hya
        change
          CliffordGeneralSpinIntrinsicPoint.scalarGroupHom V ℚ_[p] y.1 *
              V.cliffordSpinCandidateToCliffordGeneralSpinHom ℚ_[p] y.2 =
            CliffordGeneralSpinIntrinsicPoint.scalarGroupHom V ℚ_[p] a *
              V.cliffordSpinCandidateToCliffordGeneralSpinHom ℚ_[p] s at h
        rw [hy1] at h
        exact mul_left_cancel h
      have hy2 : y.2 = s :=
        V.cliffordSpinCandidateToCliffordGeneralSpinHom_injective ℚ_[p] hspin
      simpa [hy2] using hy.2
    · have hy1 : y.1 = -a := Units.ext hneg
      have hnegSource : -a ∈ (Rat.unitSquareIdentityChart ℚ_[p]).source := by
        simpa [hy1] using hy.1
      have hunit : (-a : ℚ_[p]ˣ) = a :=
        (Rat.unitSquareIdentityChart ℚ_[p]).injOn hnegSource ha (by simp)
      have hnegone : (-1 : ℚ_[p]ˣ) = 1 := by
        calc
          (-1 : ℚ_[p]ˣ) = (-a) * a⁻¹ := by simp
          _ = a * a⁻¹ := by rw [hunit]
          _ = 1 := by simp
      have hval := congrArg Units.val hnegone
      have hrat : (-1 : ℚ) = 1 := by
        apply (algebraMap ℚ ℚ_[p]).injective
        simpa using hval
      norm_num at hrat
  · intro hs
    change V.cliffordGeneralSpinCentralSpinMultiplication ℚ_[p] (a, s) ∈ c.target
    exact c.map_source ⟨ha, hs⟩

/-- Orbit form of the real fixed-square-source identity. -/
theorem spin_mul_scalar_mul_one_mem_realCentralFiberIdentityChart_iff
    (a : ℝˣ) (ha : a ∈ (Rat.unitSquareIdentityChart ℝ).source)
    (s : V.RealCliffordSpinCandidateGroup) :
    V.cliffordSpinCandidateToCliffordGeneralSpinHom ℝ s *
          (CliffordGeneralSpinIntrinsicPoint.scalarGroupHom V ℝ a *
            V.cliffordSpinCandidateToCliffordGeneralSpinHom ℝ 1) ∈
        V.realCliffordGeneralSpinCentralFiberIdentityChart.source ↔
      s ∈ V.realCliffordSpinCandidateIdentityChart.source := by
  rw [map_one, mul_one, ← V.scalarGroupHom_mul_comm]
  exact V.scalar_mul_spin_mem_realCentralFiberIdentityChart_iff a ha s

/-- Orbit form of the p-adic fixed-square-source identity. -/
theorem spin_mul_scalar_mul_one_mem_padicCentralFiberIdentityChart_iff
    (p : ℕ) [Fact (Nat.Prime p)]
    (a : ℚ_[p]ˣ) (ha : a ∈ (Rat.unitSquareIdentityChart ℚ_[p]).source)
    (s : V.PadicCliffordSpinCandidateGroup p) :
    V.cliffordSpinCandidateToCliffordGeneralSpinHom ℚ_[p] s *
          (CliffordGeneralSpinIntrinsicPoint.scalarGroupHom V ℚ_[p] a *
            V.cliffordSpinCandidateToCliffordGeneralSpinHom ℚ_[p] 1) ∈
        (V.padicCliffordGeneralSpinCentralFiberIdentityChart p).source ↔
      s ∈ (V.padicCliffordSpinCandidateIdentityChart p).source := by
  rw [map_one, mul_one, ← V.scalarGroupHom_mul_comm]
  exact V.scalar_mul_spin_mem_padicCentralFiberIdentityChart_iff p a ha s

end RationalQuadraticSpaceMatrix

namespace PositiveDefiniteIntegralLattice

variable {r : ℕ}

local instance retainedOrbitalSourceDecidableEq :
    DecidableEq (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  Classical.decEq _

local instance retainedOrbitalSourceRealSpinMeasurableSpace
    (L : PositiveDefiniteIntegralLattice (r + 2)) :
    MeasurableSpace L.rationalQuadraticSpaceMatrix.RealCliffordSpinCandidateGroup :=
  borel _

local instance retainedOrbitalSourceRealSpinBorelSpace
    (L : PositiveDefiniteIntegralLattice (r + 2)) :
    BorelSpace L.rationalQuadraticSpaceMatrix.RealCliffordSpinCandidateGroup :=
  ⟨rfl⟩

local instance retainedOrbitalSourceFiniteSpinMeasurableSpace
    (L : PositiveDefiniteIntegralLattice (r + 2)) :
    MeasurableSpace L.rationalQuadraticSpaceMatrix.FiniteAdelicCliffordSpinCandidateGroup :=
  borel _

local instance retainedOrbitalSourceFiniteSpinBorelSpace
    (L : PositiveDefiniteIntegralLattice (r + 2)) :
    BorelSpace L.rationalQuadraticSpaceMatrix.FiniteAdelicCliffordSpinCandidateGroup :=
  ⟨rfl⟩

/-- Every point of the retained real orbit preimage has its literal
translated identity-chart source coordinate.  This pointwise formulation
avoids forcing Lean to normalize a global subtype image. -/
theorem exists_retainedRealSpinSourceToOrbitPreimage_eq
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (x : L.rationalQuadraticSpaceMatrix.CliffordGeneralSpinHorizontalFullSOChartSource
      (L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S ∪
        L.rationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalIntegralBadPlaces))
    (y : L.rationalQuadraticSpaceMatrix.RealCliffordSpinCandidateGroup)
    (hy : y ∈ L.cliffordGeneralSpinHorizontalRetainedRealSpinOrbitPreimage S x) :
    ∃ u : L.rationalQuadraticSpaceMatrix.realCliffordSpinCandidateIdentityChart.source,
      L.retainedRealSpinSourceToOrbitPreimage S x u = y := by
  rw [L.cliffordGeneralSpinHorizontalRetainedRealSpinOrbitPreimage_eq_preimage_mul S x]
    at hy
  refine ⟨⟨y * (x.1 :
    L.rationalQuadraticSpaceMatrix.RealCliffordSpinCandidateGroup), hy⟩, ?_⟩
  change (y * (x.1 :
    L.rationalQuadraticSpaceMatrix.RealCliffordSpinCandidateGroup)) *
      (x.1 : L.rationalQuadraticSpaceMatrix.RealCliffordSpinCandidateGroup)⁻¹ = y
  simp [mul_assoc]

/-- Range form recovered from the two pointwise source statements without
normalizing the dependent subtype image. -/
theorem range_retainedRealSpinSourceToOrbitPreimage
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (x : L.rationalQuadraticSpaceMatrix.CliffordGeneralSpinHorizontalFullSOChartSource
      (L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S ∪
        L.rationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalIntegralBadPlaces)) :
    Set.range (L.retainedRealSpinSourceToOrbitPreimage S x) =
      L.cliffordGeneralSpinHorizontalRetainedRealSpinOrbitPreimage S x := by
  apply Set.Subset.antisymm
  · rintro y ⟨u, rfl⟩
    have hpre := Set.ext_iff.mp
      (L.preimage_retainedRealSpinSourceToOrbitPreimage S x) u
    exact hpre.mpr (Set.mem_univ u)
  · intro y hy
    obtain ⟨u, hu⟩ := L.exists_retainedRealSpinSourceToOrbitPreimage_eq S x y hy
    exact ⟨u, hu⟩

/-- The paired-source comap recovers the complete raw real--finite
restriction after mapping back.  Surjectivity is needed only on the retained
carrier, where it follows from the pointwise real source recovery and the
finite block image theorem. -/
theorem map_comap_cliffordSpinCandidateRealFiniteRawMeasure_restrict_retainedOrbitPreimage
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (D : L.rationalQuadraticSpaceMatrix.CliffordSpinCandidateRawOnoTamagawaData)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (x : L.rationalQuadraticSpaceMatrix.CliffordGeneralSpinHorizontalFullSOChartSource
      (L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S ∪
        L.rationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalIntegralBadPlaces)) :
    let j := Prod.map (L.retainedRealSpinSourceToOrbitPreimage S x)
      (L.retainedSpinBlockSourceToOrbitPreimage S x)
    let C := L.cliffordGeneralSpinHorizontalRetainedRealSpinOrbitPreimage S x ×ˢ
      L.cliffordGeneralSpinHorizontalRetainedFiniteSpinOrbitPreimage S x
    Measure.map j (((L.cliffordSpinCandidateRealFiniteRawMeasure D).restrict C).comap j) =
      (L.cliffordSpinCandidateRealFiniteRawMeasure D).restrict C := by
  dsimp only
  let jR := L.retainedRealSpinSourceToOrbitPreimage S x
  let jF := L.retainedSpinBlockSourceToOrbitPreimage S x
  let j := Prod.map jR jF
  let C := L.cliffordGeneralSpinHorizontalRetainedRealSpinOrbitPreimage S x ×ˢ
    L.cliffordGeneralSpinHorizontalRetainedFiniteSpinOrbitPreimage S x
  let μ := L.cliffordSpinCandidateRealFiniteRawMeasure D
  have hj : MeasurableEmbedding j :=
    (L.measurableEmbedding_retainedRealSpinSourceToOrbitPreimage S x).prodMap
      (L.measurableEmbedding_retainedSpinBlockSourceToOrbitPreimage S x)
  have hsubset : C ⊆ Set.range j := by
    rintro y ⟨hyR, hyF⟩
    obtain ⟨uR, huR⟩ :=
      L.exists_retainedRealSpinSourceToOrbitPreimage_eq S x y.1 hyR
    have hyF' := hyF
    rw [L.cliffordGeneralSpinHorizontalRetainedFiniteSpinOrbitPreimage_eq_image_orbitPreimageSource
      S x] at hyF'
    rcases hyF' with ⟨uF, huF, huFy⟩
    refine ⟨(uR, uF), ?_⟩
    apply Prod.ext
    · exact huR
    · exact huFy
  change Measure.map j ((μ.restrict C).comap j) = μ.restrict C
  calc
    Measure.map j ((μ.restrict C).comap j) =
        (μ.restrict C).restrict (Set.range j) := hj.map_comap _
    _ = μ.restrict C := by
      rw [Measure.restrict_restrict hj.measurableSet_range]
      congr 1
      exact Set.inter_eq_right.mpr hsubset

/-- Restricting raw adelic Spin Haar to the inverse image of a measurable
real--finite set is exactly the inverse-equivalence pushforward of the
corresponding raw real--finite restriction. -/
theorem spinData_adelicMeasure_restrict_realFinite_preimage
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (D : L.rationalQuadraticSpaceMatrix.CliffordSpinCandidateRawOnoTamagawaData)
    (C : Set (L.rationalQuadraticSpaceMatrix.RealCliffordSpinCandidateGroup ×
      L.rationalQuadraticSpaceMatrix.FiniteAdelicCliffordSpinCandidateGroup)) :
    let V := L.rationalQuadraticSpaceMatrix
    let e := V.fullAdelicCliffordSpinCandidateGroupRealFiniteContinuousEquiv
    D.spinData.adelicMeasure.restrict (e ⁻¹' C) =
      Measure.map e.symm ((L.cliffordSpinCandidateRealFiniteRawMeasure D).restrict C) := by
  dsimp only
  let V := L.rationalQuadraticSpaceMatrix
  let e := V.fullAdelicCliffordSpinCandidateGroupRealFiniteContinuousEquiv
  let μ := V.fullAdelicCliffordSpinCandidateRawDifferentialGroupMeasure D.spinFiniteScale
  let ν := L.cliffordSpinCandidateRealFiniteRawMeasure D
  have hmap : Measure.map e μ = ν := by
    exact V.map_fullAdelicCliffordSpinCandidateRawDifferentialGroupMeasure_realFinite
      D.spinFiniteScale
  have hadelic : D.spinData.adelicMeasure = Measure.map e.symm ν := by
    rw [D.spinRaw.adelicMeasure_eq]
    change μ = Measure.map e.symm ν
    calc
      μ = Measure.map e.symm (Measure.map e μ) := by
        symm
        exact e.toMeasurableEquiv.symm.map_map_symm
      _ = Measure.map e.symm ν := by rw [hmap]
  rw [hadelic]
  have hpre : e ⁻¹' C = e.symm '' C := by
    ext y
    constructor
    · intro hy
      exact ⟨e y, hy, e.symm_apply_apply y⟩
    · rintro ⟨z, hz, hzy⟩
      change e y ∈ C
      rw [← hzy, e.apply_symm_apply]
      exact hz
  rw [hpre]
  change (Measure.map e.symm.toHomeomorph ν).restrict (e.symm '' C) =
    Measure.map e.symm.toHomeomorph (ν.restrict C)
  rw [e.symm.measurableEmbedding.restrict_map]
  have hpreimage :
      e.symm.toHomeomorph ⁻¹' (e.symm '' C) = C :=
    Set.preimage_image_eq _ e.symm.injective
  rw [hpreimage]

/-- At an existing retained horizontal origin, the full adelic raw Spin
restriction is exactly the inverse real--finite pushforward of the retained
real and finite orbit-preimage restriction. -/
theorem spinData_adelicMeasure_restrict_fullSOChartGSpinOrigin_preimage
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (D : L.rationalQuadraticSpaceMatrix.CliffordSpinCandidateRawOnoTamagawaData)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (x : L.rationalQuadraticSpaceMatrix.CliffordGeneralSpinHorizontalFullSOChartSource
      (L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S ∪
        L.rationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalIntegralBadPlaces)) :
    let V := L.rationalQuadraticSpaceMatrix
    let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
    let e := V.fullAdelicCliffordSpinCandidateGroupRealFiniteContinuousEquiv
    let g := L.cliffordGeneralSpinHorizontalFullSOChartGSpinOrigin S x
    let C := L.cliffordGeneralSpinHorizontalRetainedRealSpinOrbitPreimage S x ×ˢ
      L.cliffordGeneralSpinHorizontalRetainedFiniteSpinOrbitPreimage S x
    D.spinData.adelicMeasure.restrict
        ((fun y : V.FullAdelicCliffordSpinCandidateGroup =>
          V.fullAdelicCliffordSpinCandidateToGeneralSpinHom y * g) ⁻¹'
          V.cliffordGeneralSpinHorizontalIdentityChartFullAdelicCarrier E) =
      Measure.map e.symm ((L.cliffordSpinCandidateRealFiniteRawMeasure D).restrict C) := by
  dsimp only
  let V := L.rationalQuadraticSpaceMatrix
  let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
  let e := V.fullAdelicCliffordSpinCandidateGroupRealFiniteContinuousEquiv
  let g := L.cliffordGeneralSpinHorizontalFullSOChartGSpinOrigin S x
  let C := L.cliffordGeneralSpinHorizontalRetainedRealSpinOrbitPreimage S x ×ˢ
    L.cliffordGeneralSpinHorizontalRetainedFiniteSpinOrbitPreimage S x
  rw [V.preimage_fullAdelicCliffordSpinCandidateOrbit_identityChart E g]
  rw [L.preimage_cliffordSpinCandidateRealFiniteOrbitAt_fullSOChartGSpinOrigin S x]
  exact L.spinData_adelicMeasure_restrict_realFinite_preimage D C

/-- Pushing the retained-origin raw adelic restriction through its
Spin orbit is exactly the pushforward of the paired translated
real--finite source.  This is a source-preserving identity, not merely an
equality of total masses. -/
theorem map_spinOrbit_spinData_restrict_fullSOChartGSpinOrigin_preimage
    (L : PositiveDefiniteIntegralLattice (r + 2))
    (D : L.rationalQuadraticSpaceMatrix.CliffordSpinCandidateRawOnoTamagawaData)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (x : L.rationalQuadraticSpaceMatrix.CliffordGeneralSpinHorizontalFullSOChartSource
      (L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S ∪
        L.rationalQuadraticSpaceMatrix.cliffordGeneralSpinHorizontalIntegralBadPlaces)) :
    let V := L.rationalQuadraticSpaceMatrix
    let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
    let g := L.cliffordGeneralSpinHorizontalFullSOChartGSpinOrigin S x
    let orbit := fun y : V.FullAdelicCliffordSpinCandidateGroup =>
      V.fullAdelicCliffordSpinCandidateToGeneralSpinHom y * g
    let j := Prod.map (L.retainedRealSpinSourceToOrbitPreimage S x)
      (L.retainedSpinBlockSourceToOrbitPreimage S x)
    let C := L.cliffordGeneralSpinHorizontalRetainedRealSpinOrbitPreimage S x ×ˢ
      L.cliffordGeneralSpinHorizontalRetainedFiniteSpinOrbitPreimage S x
    let source := ((L.cliffordSpinCandidateRealFiniteRawMeasure D).restrict C).comap j
    Measure.map orbit
        (D.spinData.adelicMeasure.restrict
          (orbit ⁻¹' V.cliffordGeneralSpinHorizontalIdentityChartFullAdelicCarrier E)) =
      Measure.map
        (fun u => V.fullAdelicCliffordGeneralSpinRealFiniteContinuousEquiv.symm
          (L.retainedRealFiniteSpinSourceOrbit S x u)) source := by
  dsimp only
  let V := L.rationalQuadraticSpaceMatrix
  let E := L.cliffordGeneralSpinHorizontalCentralExtensionExceptionalPlaces S
  let e := V.fullAdelicCliffordSpinCandidateGroupRealFiniteContinuousEquiv
  let g := L.cliffordGeneralSpinHorizontalFullSOChartGSpinOrigin S x
  let orbit := fun y : V.FullAdelicCliffordSpinCandidateGroup =>
    V.fullAdelicCliffordSpinCandidateToGeneralSpinHom y * g
  let j := Prod.map (L.retainedRealSpinSourceToOrbitPreimage S x)
    (L.retainedSpinBlockSourceToOrbitPreimage S x)
  let C := L.cliffordGeneralSpinHorizontalRetainedRealSpinOrbitPreimage S x ×ˢ
    L.cliffordGeneralSpinHorizontalRetainedFiniteSpinOrbitPreimage S x
  let source := ((L.cliffordSpinCandidateRealFiniteRawMeasure D).restrict C).comap j
  have horbit : Measurable orbit :=
    (V.continuous_cliffordSpinCandidateToCliffordGeneralSpinHom RationalAdele).mul
      continuous_const |>.measurable
  have heSymm : Measurable e.symm := e.symm.continuous.measurable
  have hj : Measurable j :=
    ((L.measurableEmbedding_retainedRealSpinSourceToOrbitPreimage S x).prodMap
      (L.measurableEmbedding_retainedSpinBlockSourceToOrbitPreimage S x)).measurable
  rw [L.spinData_adelicMeasure_restrict_fullSOChartGSpinOrigin_preimage D S x]
  have hsource : Measure.map j source =
      (L.cliffordSpinCandidateRealFiniteRawMeasure D).restrict C :=
    L.map_comap_cliffordSpinCandidateRealFiniteRawMeasure_restrict_retainedOrbitPreimage
      D S x
  change Measure.map orbit
      (Measure.map e.symm ((L.cliffordSpinCandidateRealFiniteRawMeasure D).restrict C)) =
    Measure.map
      (fun u => V.fullAdelicCliffordGeneralSpinRealFiniteContinuousEquiv.symm
        (L.retainedRealFiniteSpinSourceOrbit S x u)) source
  calc
    Measure.map orbit
        (Measure.map e.symm ((L.cliffordSpinCandidateRealFiniteRawMeasure D).restrict C)) =
        Measure.map orbit (Measure.map e.symm (Measure.map j source)) := by rw [hsource]
    _ = Measure.map orbit (Measure.map (e.symm ∘ j) source) := by
      congr 1
      exact Measure.map_map heSymm hj
    _ = Measure.map (orbit ∘ e.symm ∘ j) source := by
      exact Measure.map_map horbit (heSymm.comp hj)
    _ = Measure.map
        (fun u => V.fullAdelicCliffordGeneralSpinRealFiniteContinuousEquiv.symm
          (L.retainedRealFiniteSpinSourceOrbit S x u)) source := by
      congr 1
      funext u
      exact
        (L.fullAdelicCliffordGeneralSpinRealFinite_symm_retainedSpinSourceOrbit S x u).symm

end PositiveDefiniteIntegralLattice

end
