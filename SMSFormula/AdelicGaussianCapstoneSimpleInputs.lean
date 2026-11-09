import SMSFormula.AdelicGaussianIntegralPresentationDenominator
import SMSFormula.SpecialOrthogonalFullAdelicDifferentialHaar
import SMSFormula.SpecialOrthogonalFullAdelicRealFiniteOpenStabilizer

/-!
# Existence of the elementary inputs of the theta–Tamagawa identity

Each of the elementary inputs of `representedNormTheta_mul_spinTamagawa_eq_core` exists:

* a real central cutoff `T ⊆ ℝˣ` (measurable, `-`-stable, positive finite Haar mass);
* a compact open subgroup `K` of the full-adelic `SO` (the real/finite lattice stabilizer,
  transported along the carrier identification);
* the rational diagonal basepoint `x₀ = diag x` in the adelic value fiber;
* positive definiteness of every lattice's rational form over `ℝ`, and positivity of `Q(x)`;
* a finite place set `T` containing any supplied finite place set, the dyadic place and the support
  of one supplied rational, and avoiding (off `T`) the primes of a supplied nonzero natural number,
  of a supplied nonzero integer, a supplied finite prime set and the supports of two supplied
  rationals.

The place set is an existence statement over supplied finite data (enlarging a place set is
harmless).
-/

noncomputable section

open MeasureTheory

namespace PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase

open Rat.HeightOneSpectrum RationalQuadraticSpaceMatrix

/-- A real central cutoff exists: `T = {t : 1 ≤ |t| ≤ 2}`. -/
theorem exists_realUnitCentralCutoffSet :
    ∃ T : Set ℝˣ, MeasurableSet T ∧ (∀ t : ℝˣ, -t ∈ T ↔ t ∈ T) ∧
      (Measure.haar : Measure ℝˣ) T ≠ 0 ∧ (Measure.haar : Measure ℝˣ) T ≠ ⊤ := by
  let T : Set ℝˣ := {t | |(t : ℝ)| ∈ Set.Icc (1 : ℝ) 2}
  let U : Set ℝˣ := {t | |(t : ℝ)| ∈ Set.Ioo (1 : ℝ) 2}
  have hval : Continuous (fun t : ℝˣ ↦ |(t : ℝ)|) := continuous_abs.comp Units.continuous_val
  have hclosed : IsClosed T := isClosed_Icc.preimage hval
  have hUT : U ⊆ T := fun t ht ↦ Set.Ioo_subset_Icc_self ht
  have hUo : IsOpen U := isOpen_Ioo.preimage hval
  have hUne : U.Nonempty := ⟨Units.mk0 (3 / 2) (by norm_num), by
    change |((3 / 2 : ℝ))| ∈ Set.Ioo (1 : ℝ) 2
    rw [abs_of_pos (by norm_num)]
    constructor <;> norm_num⟩
  have hcompact : IsCompact T := by
    rw [Units.isEmbedding_val₀.isCompact_iff]
    have himage : ((↑) : ℝˣ → ℝ) '' T = {y : ℝ | |y| ∈ Set.Icc (1 : ℝ) 2} := by
      ext y
      constructor
      · rintro ⟨t, ht, rfl⟩
        exact ht
      · intro hy
        have hy0 : y ≠ 0 := by
          rintro rfl
          norm_num at hy
        exact ⟨Units.mk0 y hy0, hy, rfl⟩
    rw [himage]
    refine (isCompact_closedBall (0 : ℝ) 2).of_isClosed_subset
      (isClosed_Icc.preimage continuous_abs) fun y hy ↦ ?_
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero]
    exact hy.2
  refine ⟨T, hclosed.measurableSet, fun t ↦ ?_, fun h ↦ ?_, hcompact.measure_lt_top.ne⟩
  · simp only [T, Set.mem_setOf_eq, Units.val_neg, abs_neg]
  · exact hUo.measure_ne_zero _ hUne (measure_mono_null hUT h)

end PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- The real/finite lattice stabilizer on the matrix carrier of the full-adelic `SO`. -/
def fullAdelicLatticeStabilizerOnMatrixCarrier (L : PositiveDefiniteIntegralLattice n) :
    Subgroup L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalGroup :=
  L.fullAdelicRealFiniteLatticeStabilizerSubgroup.comap
    L.rationalQuadraticSpaceMatrixFullAdelicSpecialOrthogonalContinuousEquiv.toMonoidHom

theorem coe_fullAdelicLatticeStabilizerOnMatrixCarrier (L : PositiveDefiniteIntegralLattice n) :
    (L.fullAdelicLatticeStabilizerOnMatrixCarrier :
      Set L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalGroup) =
      L.rationalQuadraticSpaceMatrixFullAdelicSpecialOrthogonalContinuousEquiv ⁻¹'
        (L.fullAdelicRealFiniteLatticeStabilizerSubgroup :
          Set L.ConcreteFullAdelicSpecialOrthogonalGroup) :=
  rfl

theorem isCompact_fullAdelicLatticeStabilizerOnMatrixCarrier (L : PositiveDefiniteIntegralLattice n) :
    IsCompact (L.fullAdelicLatticeStabilizerOnMatrixCarrier :
      Set L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalGroup) := by
  rw [coe_fullAdelicLatticeStabilizerOnMatrixCarrier]
  exact L.rationalQuadraticSpaceMatrixFullAdelicSpecialOrthogonalContinuousEquiv.toHomeomorph
    |>.isCompact_preimage.2 L.isCompact_fullAdelicRealFiniteLatticeStabilizerSubgroup

theorem isOpen_fullAdelicLatticeStabilizerOnMatrixCarrier (L : PositiveDefiniteIntegralLattice n) :
    IsOpen (L.fullAdelicLatticeStabilizerOnMatrixCarrier :
      Set L.rationalQuadraticSpaceMatrix.FullAdelicSpecialOrthogonalGroup) := by
  rw [coe_fullAdelicLatticeStabilizerOnMatrixCarrier]
  exact L.isOpen_fullAdelicRealFiniteLatticeStabilizerSubgroup.preimage
    L.rationalQuadraticSpaceMatrixFullAdelicSpecialOrthogonalContinuousEquiv.continuous

/-- The rational diagonal basepoint of the adelic value fiber. -/
def rationalDiagonalValueFiberPoint (L : PositiveDefiniteIntegralLattice n) (x : Fin n → ℚ) :
    IntegralFiniteAdelePhase.adelicValueFiber L (algebraMap ℚ RationalAdele
      (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x)) :=
  ⟨fun i ↦ algebraMap ℚ RationalAdele (x i),
    L.rationalQuadraticSpaceMatrix.fullAdelicQuadraticFormValue_rationalDiagonal x⟩

/-- Every lattice's rational form is positive definite over `ℝ`. -/
theorem posDef_rationalQuadraticSpaceMatrix_pairingMatrix_map_real (L : PositiveDefiniteIntegralLattice n) :
    (L.rationalQuadraticSpaceMatrix.pairingMatrix.map (algebraMap ℚ ℝ)).PosDef := by
  have h : L.rationalQuadraticSpaceMatrix.pairingMatrix.map (algebraMap ℚ ℝ) =
      L.pairingMatrix.map (Int.cast : ℤ → ℝ) := by
    ext i j
    simp [rationalQuadraticSpaceMatrix_pairingMatrix, PositiveDefiniteIntegralLattice.rationalFormMatrix]
  rw [h]
  exact L.form_posDef

/-- A nonzero value of a lattice form is positive. -/
theorem nativeRationalQuadraticForm_pos_of_ne_zero (L : PositiveDefiniteIntegralLattice n) {x : Fin n → ℚ}
    (hx : L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x ≠ 0) :
    0 < L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x := by
  refine L.rationalQuadraticSpaceMatrix_nativeRationalQuadraticForm_pos fun h ↦ hx ?_
  rw [h, map_zero]

end PositiveDefiniteIntegralLattice

namespace PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase

open Rat.HeightOneSpectrum RationalQuadraticSpaceMatrix

local instance csiDecidableEq : DecidableEq (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  Classical.decEq _

/-- A finite place set with the tail conditions of
`representedNormTheta_mul_spinTamagawa_eq_core` exists over supplied finite data. -/
theorem exists_capstoneTailPlaces (D : ℕ) (hD : D ≠ 0) (M : ℤ) (hM : M ≠ 0) (G : Finset ℕ)
    (c₁ c₂ c₃ : ℚ) (A : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    ∃ T : Finset (IsDedekindDomain.HeightOneSpectrum ℤ),
      A ⊆ T ∧ rationalIdeleDyadicPlace ∈ T ∧
      Rat.padicNormPrimeSupport c₃ ⊆ T.map Rat.HeightOneSpectrum.primesEquiv.toEmbedding ∧
      ∀ q ∉ T.map Rat.HeightOneSpectrum.primesEquiv.toEmbedding,
        ¬ q.1 ∣ D ∧ q.1 ≠ 2 ∧ ¬ (q.1 : ℤ) ∣ M ∧ q.1 ∉ G ∧
          q ∉ Rat.padicNormPrimeSupport c₁ ∧ q ∉ Rat.padicNormPrimeSupport c₂ := by
  classical
  let E : Finset Nat.Primes :=
    (D.primeFactors ∪ {2} ∪ M.natAbs.primeFactors ∪ G).subtype Nat.Prime ∪
      Rat.padicNormPrimeSupport c₁ ∪ Rat.padicNormPrimeSupport c₂ ∪ Rat.padicNormPrimeSupport c₃
  let T := A ∪ {rationalIdeleDyadicPlace} ∪ E.map primesEquiv.symm.toEmbedding
  have hE : ∀ q : Nat.Primes, q ∈ E → q ∈ T.map primesEquiv.toEmbedding := by
    intro q hq
    rw [Finset.mem_map_equiv]
    exact Finset.mem_union_right _ (Finset.mem_map_equiv.2 (by simpa using hq))
  have hsub : ∀ q : Nat.Primes, q.1 ∈ D.primeFactors ∪ {2} ∪ M.natAbs.primeFactors ∪ G →
      q ∈ T.map primesEquiv.toEmbedding := fun q hq ↦
    hE q (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
      (Finset.mem_subtype.2 hq))))
  refine ⟨T, fun v hv ↦ by simp [T, hv], by simp [T],
    fun q hq ↦ hE q (Finset.mem_union_right _ hq), ?_⟩
  intro q hq
  refine ⟨fun h ↦ hq (hsub q ?_), fun h ↦ hq (hsub q ?_), fun h ↦ hq (hsub q ?_),
    fun h ↦ hq (hsub q ?_),
    fun h ↦ hq (hE q (Finset.mem_union_left _ (Finset.mem_union_left _
      (Finset.mem_union_right _ h)))),
    fun h ↦ hq (hE q (Finset.mem_union_left _ (Finset.mem_union_right _ h)))⟩
  · simp [Nat.mem_primeFactors, q.2, h, hD]
  · simp [h]
  · have : q.1 ∣ M.natAbs := Int.natCast_dvd.1 h
    simp [Nat.mem_primeFactors, q.2, this, hM]
  · simp [h]

end PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase
