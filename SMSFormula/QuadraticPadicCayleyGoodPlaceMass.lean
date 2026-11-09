import SMSFormula.QuadraticPadicCayleyStabilizerAtlasGlueMass
import SMSFormula.QuadraticPadicCayleyIntegralOrbit
import SMSFormula.QuadraticPadicSquareBranchAtlasGlueScalar

/-! The good-place factor of the stabilizer volume identity. The atlas glue
does not depend on the covering atlas on commonly covered sets. At a good place
(`p` odd, the Gram matrix of `W ⊕ ⟨a⟩` integral with unit determinant, `a` a
unit, `n ≥ 1`) the integral subgroup `K` is compact open and
`K · x_old = X_a(ℤ_p)`, so at the identity-centred chart

`vol_G(K) = |r| · vol_H(K ∩ H) · ν(ℤ_p) · λ(X_a(ℤ_p))`,

with `λ` the glue of any atlas covering the nonisotropic vectors. By the tube
formula, for every measurable value set `B` in an open neighbourhood of `a`,

`vol_G(K) · ν(B) = |r| · vol_H(K ∩ H) · ν(ℤ_p) · vol(ℤ_p^(n+1) ∩ Q⁻¹B)`,

i.e. `λ(X_a(ℤ_p)) = d_p(a)` is the value-density quotient. The good-place
conditions and the atlas are supplied; no chart, section, cutoff or Haar
normalization is chosen. -/
noncomputable section
open MeasureTheory Matrix PositiveDefiniteIntegralLattice Metric Set Filter QuadraticMap
open scoped Matrix.Norms.Operator ENNReal NNReal Topology

namespace QuadraticMap

variable (prime : ℕ) [Fact prime.Prime]

local instance padicGoodPlaceMeasurableSpace : MeasurableSpace ℚ_[prime] := borel _
local instance padicGoodPlaceBorelSpace : BorelSpace ℚ_[prime] := ⟨rfl⟩

variable {space : Type*} [NormedAddCommGroup space] [NormedSpace ℚ_[prime] space]
  [FiniteDimensional ℚ_[prime] space] [MeasurableSpace space] [BorelSpace space]
  [SecondCountableTopology space] [LocallyCompactSpace space]

/-- Atlas independence: two atlas glues agree on every measurable set covered by
both atlases. -/
theorem padicSquareBranchAtlasGlue_apply_eq_of_cover (form : QuadraticForm ℚ_[prime] space)
    (point : ℕ → space) (hpoint : ∀ i, form (point i) ≠ 0)
    (transverseHaar : ∀ i, Measure (form.anisotropicOrthogonal (point i)))
    [∀ i, (transverseHaar i).IsAddHaarMeasure]
    (point' : ℕ → space) (hpoint' : ∀ i, form (point' i) ≠ 0)
    (transverseHaar' : ∀ i, Measure (form.anisotropicOrthogonal (point' i)))
    [∀ i, (transverseHaar' i).IsAddHaarMeasure]
    (scalarHaar : Measure ℚ_[prime]) (vectorHaar : Measure space)
    [scalarHaar.IsAddHaarMeasure] [vectorHaar.IsAddHaarMeasure] (value : ℚ_[prime])
    {S : Set {vector : space // form vector = value}} (hS : MeasurableSet S)
    (hcov : S ⊆ ⋃ i, Set.range (form.padicSquareBranchFiberMap prime (point i) (hpoint i) value))
    (hcov' : S ⊆ ⋃ i, Set.range (form.padicSquareBranchFiberMap prime (point' i) (hpoint' i) value)) :
    form.padicSquareBranchAtlasGlue prime point hpoint transverseHaar scalarHaar vectorHaar value S =
      form.padicSquareBranchAtlasGlue prime point' hpoint' transverseHaar' scalarHaar vectorHaar
        value S := by
  set R' : ℕ → Set {vector : space // form vector = value} := fun j ↦
    Set.range (form.padicSquareBranchFiberMap prime (point' j) (hpoint' j) value) with hR'def
  have hR' : ∀ j, MeasurableSet (R' j) := fun j ↦
    (form.isOpenEmbedding_padicSquareBranchFiberMap prime (point' j) (hpoint' j)
      value).isOpen_range.measurableSet
  set P : ℕ → Set {vector : space // form vector = value} := fun j ↦ S ∩ disjointed R' j
    with hPdef
  have hP : ∀ j, MeasurableSet (P j) := fun j ↦ hS.inter (MeasurableSet.disjointed hR' j)
  have hPdisj : Pairwise (Function.onFun Disjoint P) := fun i j hij ↦
    (disjoint_disjointed R' hij).mono Set.inter_subset_right Set.inter_subset_right
  have hSP : S = ⋃ j, P j := by
    rw [hPdef, ← Set.inter_iUnion, iUnion_disjointed]
    exact (Set.inter_eq_left.mpr hcov').symm
  rw [hSP, measure_iUnion hPdisj hP, measure_iUnion hPdisj hP]
  refine tsum_congr fun j ↦ ?_
  have hPR : P j ⊆ R' j := Set.inter_subset_right.trans (disjointed_subset R' j)
  have hsub : P j ⊆ Set.range (form.padicSquareBranchFiberMap prime (point' j) (hpoint' j) value) ∩
      ⋃ i, Set.range (form.padicSquareBranchFiberMap prime (point i)
      (hpoint i) value) := fun y hy ↦ ⟨hPR hy, hcov hy.1⟩
  have h := congrArg (fun m : Measure {vector : space // form vector = value} ↦ m (P j))
    (form.padicSquareBranchAtlasGlue_restrict_of_point prime point hpoint transverseHaar
      scalarHaar vectorHaar value (point' j) (hpoint' j) (transverseHaar' j))
  dsimp only at h
  rw [Measure.restrict_apply (hP j), Measure.restrict_apply (hP j),
    Set.inter_eq_left.mpr hsub] at h
  rw [h, form.padicSquareBranchAtlasGlue_apply_of_subset prime point' hpoint' transverseHaar'
    scalarHaar vectorHaar value j (hP j) hPR]

end QuadraticMap

namespace RationalQuadraticSpaceMatrix
variable {n : ℕ} (W : RationalQuadraticSpaceMatrix n) (p : ℕ) [Fact (Nat.Prime p)]
variable (a : ℚ) (ha : a ≠ 0)

local instance gpPadicMeasurableSpace : MeasurableSpace ℚ_[p] := borel _
local instance gpPadicBorelSpace : BorelSpace ℚ_[p] := ⟨rfl⟩
local instance gpGroupMeasurableSpace (F : Matrix (Fin (n+1)) (Fin (n+1)) ℚ) :
    MeasurableSpace (specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℚ_[p]))) :=
  borel _
local instance gpGroupBorelSpace (F : Matrix (Fin (n+1)) (Fin (n+1)) ℚ) :
    BorelSpace (specialFormPreservingMatrixSubgroup (F.map (algebraMap ℚ ℚ_[p]))) :=
  ⟨rfl⟩
local instance gpLowerGroupMeasurableSpace :
    MeasurableSpace (specialFormPreservingMatrixSubgroup (W.pairingMatrix.map (algebraMap ℚ ℚ_[p]))) :=
  borel _
local instance gpLowerGroupBorelSpace :
    BorelSpace (specialFormPreservingMatrixSubgroup (W.pairingMatrix.map (algebraMap ℚ ℚ_[p]))) :=
  ⟨rfl⟩

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℚ_[p] E]
    (S : E → Matrix (Fin (n+1)) (Fin (n+1)) ℚ_[p])
    (dS : E →L[ℚ_[p]] Matrix (Fin (n+1)) (Fin (n+1)) ℚ_[p])
    (z : E) (hSs : HasStrictFDerivAt S dS z)
    (hSO : ∀ᶠ u in 𝓝 z, S u ∈ specialOrthogonalMatrixSet
      ((W.nonisotropicLastExtension a ha).specialOrthogonalMappedFormMatrix ℚ_[p]))
    (Y : skewAdjointMatricesLieSubalgebra (W.specialOrthogonalMappedFormMatrix ℚ_[p]))
    (hY : Y ∈ skewAdjointPadicCayleySource W.pairingMatrix p)
    (X : skewAdjointMatricesLieSubalgebra
      ((W.nonisotropicLastExtension a ha).specialOrthogonalMappedFormMatrix ℚ_[p]))
    (hX : X ∈ skewAdjointPadicCayleySource (W.nonisotropicLastExtension a ha).pairingMatrix p)
    (hproduct : S z * fixLastBlockMatrix (skewAdjointPadicCayleyForwardMatrix W.pairingMatrix p Y) =
      skewAdjointPadicCayleyForwardMatrix (W.nonisotropicLastExtension a ha).pairingMatrix p X)
    (v : Fin n → E)
    (hs : ((W.nonisotropicLastExtension a ha).cayleyOrbitVectorEquiv p X hX
      lastCoordinateVector) (Fin.last n) ≠ 0)
    (hv : (Pi.basisFun ℚ_[p] (Fin n)).det
      (fun i j ↦ (dS (v i) *ᵥ lastCoordinateVector) j.castSucc) ≠ 0)

variable (ν : Measure ℚ_[p]) [ν.IsAddHaarMeasure]

include hSs hSO hY hproduct hs hv in
/-- Good-place stabilizer identity: at the identity-centred chart and a good place,
for the integral subgroup `K` and every atlas covering the nonisotropic
vectors, `vol_G(K) = |r| · vol_H(K ∩ H) · ν(ℤ_p) · λ(X_a(ℤ_p))`. -/
theorem lastCayleyProduct_measure_padicIntegral_eq_integralPoints
    (hbase : (skewAdjointPadicCayleyTranslatedHomeomorph
        (W.nonisotropicLastExtension a ha).pairingMatrix p
        (W.nonisotropicLastExtension a ha).form_det_ne_zero 1 ⟨X, hX⟩).1 = 1)
    (hp : p ≠ 2) (hn : 1 ≤ n)
    (hint : ∀ i j, ‖((W.nonisotropicLastExtension a ha).pairingMatrix.map (algebraMap ℚ ℚ_[p])) i j‖ ≤ 1)
    (hdet : ‖((W.nonisotropicLastExtension a ha).pairingMatrix.map (algebraMap ℚ ℚ_[p])).det‖ = 1)
    (ha1 : ‖(algebraMap ℚ ℚ_[p] a)‖ = 1)
    (point : ℕ → Fin (n+1) → ℚ_[p])
    (hpoint : ∀ i, (W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm ℚ_[p] (point i) ≠ 0)
    (tH : ∀ i, Measure (((W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm ℚ_[p]).anisotropicOrthogonal (point i)))
    [∀ i, (tH i).IsAddHaarMeasure]
    (hcover : {y | (W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm ℚ_[p] y ≠ 0} ⊆
      ⋃ i, ((W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm ℚ_[p]).padicSquareBranchAtlasRegion p point hpoint i) :
    padicCayleySpecialOrthogonalDifferentialMeasure p (n+1)
        (W.nonisotropicLastExtension a ha).pairingMatrix
        (W.nonisotropicLastExtension a ha).form_det_ne_zero
        (padicIntegralSpecialSubgroup ((W.nonisotropicLastExtension a ha).pairingMatrix.map (algebraMap ℚ ℚ_[p]))) =
      (‖W.lastOrbitGaugeRatio a ha ℚ_[p]‖₊ : ℝ≥0∞) *
        padicCayleySpecialOrthogonalDifferentialMeasure p n W.pairingMatrix W.form_det_ne_zero
          ((padicIntegralSpecialSubgroup ((W.nonisotropicLastExtension a ha).pairingMatrix.map (algebraMap ℚ ℚ_[p]))).comap (W.lastFiberEmbedHom p a ha)) *
        (ν (closedBall 0 1) *
          ((W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm ℚ_[p]).padicSquareBranchAtlasGlue p point hpoint tH ν
            (Padic.unitHaar p (Fin (n+1))) (algebraMap ℚ ℚ_[p] a) {y | ‖y.1‖ ≤ 1}) := by
  have hKc := isCompact_padicIntegralSpecialSubgroup ((W.nonisotropicLastExtension a ha).pairingMatrix.map (algebraMap ℚ ℚ_[p]))
  have hKo := isOpen_padicIntegralSpecialSubgroup ((W.nonisotropicLastExtension a ha).pairingMatrix.map (algebraMap ℚ ℚ_[p]))
  obtain ⟨pts, -, hpts⟩ := W.exists_lastFiberOrbit_branchCover p a ha _ hKc
  let tH' : ∀ i, Measure (((W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm ℚ_[p]).anisotropicOrthogonal (pts i).1) := fun _ ↦ Measure.addHaar
  haveI : ∀ i, (tH' i).IsAddHaarMeasure := fun _ ↦ by simp only [tH']; infer_instance
  have hmain := W.lastCayleyProduct_measure_compactOpen_eq_atlasGlue p a ha S dS z hSs hSO Y hY
    X hX hproduct v hs hv ν hbase _ hKc hKo pts tH' hpts
  have horbit := W.range_smul_lastFiberBasePoint_padicIntegral p a ha hp hn hint hdet ha1
  rw [hmain, horbit]
  rw [horbit] at hpts
  have hmeas : MeasurableSet {y : {y : Fin (n+1) → ℚ_[p] // ((W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm ℚ_[p]) y = algebraMap ℚ ℚ_[p] a} | ‖y.1‖ ≤ 1} :=
    (isClosed_le (continuous_norm.comp continuous_subtype_val) continuous_const).measurableSet
  have hcov : {y : {y : Fin (n+1) → ℚ_[p] // ((W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm ℚ_[p]) y = algebraMap ℚ ℚ_[p] a} | ‖y.1‖ ≤ 1} ⊆
      ⋃ i, Set.range (((W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm ℚ_[p]).padicSquareBranchFiberMap p (point i) (hpoint i) (algebraMap ℚ ℚ_[p] a)) := by
    intro y _
    have hy : y.1 ∈ {y | ((W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm ℚ_[p]) y ≠ 0} := by
      change ((W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm ℚ_[p]) y.1 ≠ 0
      rw [y.2]; exact (map_ne_zero _).mpr ha
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcover hy)
    refine Set.mem_iUnion.mpr ⟨i, ?_⟩
    rw [((W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm ℚ_[p]).range_padicSquareBranchFiberMap p (point i) (hpoint i)]
    exact hi
  rw [((W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm ℚ_[p]).padicSquareBranchAtlasGlue_apply_eq_of_cover p (fun i ↦ (pts i).1)
    (fun i ↦ by rw [(pts i).2]; exact (map_ne_zero _).mpr ha) tH'
    point hpoint tH ν (Padic.unitHaar p (Fin (n+1))) (algebraMap ℚ ℚ_[p] a) hmeas hpts hcov]

include hSs hSO hY hproduct hs hv in
/-- Good-place local density form: there is an open neighbourhood `B₀` of `a` such
that for every measurable `B ⊆ B₀`,
`vol_G(K) · ν(B) = |r| · vol_H(K ∩ H) · ν(ℤ_p) · vol(ℤ_p^(n+1) ∩ Q⁻¹B)`. -/
theorem lastCayleyProduct_measure_padicIntegral_mul_eq_tube
    (hbase : (skewAdjointPadicCayleyTranslatedHomeomorph
        (W.nonisotropicLastExtension a ha).pairingMatrix p
        (W.nonisotropicLastExtension a ha).form_det_ne_zero 1 ⟨X, hX⟩).1 = 1)
    (hp : p ≠ 2) (hn : 1 ≤ n)
    (hint : ∀ i j, ‖((W.nonisotropicLastExtension a ha).pairingMatrix.map (algebraMap ℚ ℚ_[p])) i j‖ ≤ 1)
    (hdet : ‖((W.nonisotropicLastExtension a ha).pairingMatrix.map (algebraMap ℚ ℚ_[p])).det‖ = 1)
    (ha1 : ‖(algebraMap ℚ ℚ_[p] a)‖ = 1) :
    ∃ B₀ : Set ℚ_[p], IsOpen B₀ ∧ algebraMap ℚ ℚ_[p] a ∈ B₀ ∧ ∀ B ⊆ B₀, MeasurableSet B →
      padicCayleySpecialOrthogonalDifferentialMeasure p (n+1)
          (W.nonisotropicLastExtension a ha).pairingMatrix
          (W.nonisotropicLastExtension a ha).form_det_ne_zero
          (padicIntegralSpecialSubgroup ((W.nonisotropicLastExtension a ha).pairingMatrix.map (algebraMap ℚ ℚ_[p]))) * ν B =
        (‖W.lastOrbitGaugeRatio a ha ℚ_[p]‖₊ : ℝ≥0∞) *
          padicCayleySpecialOrthogonalDifferentialMeasure p n W.pairingMatrix W.form_det_ne_zero
            ((padicIntegralSpecialSubgroup ((W.nonisotropicLastExtension a ha).pairingMatrix.map (algebraMap ℚ ℚ_[p]))).comap (W.lastFiberEmbedHom p a ha)) *
          (ν (closedBall 0 1) *
            Padic.unitHaar p (Fin (n+1)) ({y : Fin (n+1) → ℚ_[p] | ‖y‖ ≤ 1} ∩
              (W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm ℚ_[p] ⁻¹' B)) := by
  set Q := (W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm ℚ_[p] with hQdef
  have hQ : ∃ y, Q y ≠ 0 := ⟨lastCoordinateVector, by
    rw [hQdef, W.nonisotropicLastExtension_quadratic_last]; exact (map_ne_zero _).mpr ha⟩
  obtain ⟨point, hpoint, hcover⟩ := Q.exists_padicSquareBranchAtlas_cover p hQ
  let tH : ∀ i, Measure (Q.anisotropicOrthogonal (point i)) := fun _ ↦ Measure.addHaar
  haveI : ∀ i, (tH i).IsAddHaarMeasure := fun _ ↦ by simp only [tH]; infer_instance
  have hval : algebraMap ℚ ℚ_[p] a ≠ 0 := (map_ne_zero _).mpr ha
  obtain ⟨B₀, hB₀o, hB₀a, hB₀⟩ := Q.exists_isOpen_padicSquareBranchAtlasGlue_integralPoints_mul p
    point hpoint tH ν (Padic.unitHaar p (Fin (n+1))) hcover
    (algebraMap ℚ ℚ_[p] a) hval
  refine ⟨B₀, hB₀o, hB₀a, fun B hB hBm ↦ ?_⟩
  rw [W.lastCayleyProduct_measure_padicIntegral_eq_integralPoints p a ha S dS z hSs hSO Y hY X hX
    hproduct v hs hv ν hbase hp hn hint hdet ha1 point hpoint tH hcover,
    hB₀ B hB hBm]
  ring

end RationalQuadraticSpaceMatrix
