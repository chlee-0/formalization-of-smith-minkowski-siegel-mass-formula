import SMSFormula.RationalCliffordGeneralSpinFullAdelicShellOrbitCentralCutoff
import SMSFormula.RationalCliffordGeneralSpinHorizontalFullCentralOrbitChart

/-!
# A central-cutoff subgroup and the discharged relative orbit identity

For a supplied subgroup `S` of the real block `SO` and a supplied subgroup `K_f` of the finite
block `GSpin`, the subgroup

`K = {g : ν(g_∞)² = 1, toSO(g_∞) ∈ S, g_f ∈ K_f}`

and, for a supplied `-1`-stable `T ⊆ ℝˣ`, the cutoff set

`A = {g : ν(g_∞) ∈ T, toSO(g_∞) ∈ S, g_f ∈ K_f}`

satisfy the two hypotheses of the central-cutoff orbit identity: `A` is left `K`-stable, and
every `g ∈ A` factors as `g = k · z` with `k ∈ K` and `z` the adelic central scalar with real
component `√|ν(g_∞)|` and finite component `1`.  Central scalars are block images of lower
scalars, hence lie in the stabilizer, so `g • x_old = k • x_old`.  Consequently

```text
N(K • x_old) · μ_{SO_W}(e⁻¹ S) · μ_{W,f}(ι_f⁻¹ K_f) = μ_{SO_V}(S) · μ_{V,f}(K_f).
```

The square root is the positive real square root of a positive real number, a value, not a
chosen section.  Negative scope: no volume is evaluated and no measurability of the orbit is
derived here.
-/

noncomputable section

open MeasureTheory Set PositiveDefiniteIntegralLattice
open scoped ENNReal

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

set_option synthInstance.maxHeartbeats 300000

local instance orbitCentralSubgroupInfiniteT2Space :
    T2Space RationalInfiniteAdele :=
  rationalInfiniteAdeleHomeomorphReal.symm.t2Space

local instance orbitCentralSubgroupFiniteT2Space :
    T2Space RationalFiniteAdele :=
  RestrictedProduct.instT2Space

local instance orbitCentralSubgroupT2Space : T2Space RationalAdele := by
  change T2Space (RationalInfiniteAdele × RationalFiniteAdele)
  infer_instance

noncomputable local instance orbitCentralSubgroupSourceSecondCountable
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    SecondCountableTopology
      (W.nonisotropicLastExtension a ha).FullAdelicCliffordGeneralSpinGroup :=
  (W.nonisotropicLastExtension a ha)
    |>.fullAdelicCliffordGeneralSpinGroupSecondCountableTopology

noncomputable local instance orbitCentralSubgroupSourceLocallyCompact
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    LocallyCompactSpace
      (W.nonisotropicLastExtension a ha).FullAdelicCliffordGeneralSpinGroup :=
  (W.nonisotropicLastExtension a ha)
    |>.fullAdelicCliffordGeneralSpinGroupLocallyCompactSpace

noncomputable local instance orbitCentralSubgroupSourceMeasurableSpace
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    MeasurableSpace
      (W.nonisotropicLastExtension a ha).FullAdelicCliffordGeneralSpinGroup :=
  borel _

noncomputable local instance orbitCentralSubgroupSourceBorelSpace
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    BorelSpace
      (W.nonisotropicLastExtension a ha).FullAdelicCliffordGeneralSpinGroup :=
  ⟨rfl⟩

noncomputable local instance orbitCentralSubgroupStabilizerClosed
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    IsClosed
      (W.nonisotropicLastComplementGeneralSpinStabilizerSubgroup
        a ha RationalAdele :
        Set ((W.nonisotropicLastExtension a ha)
          |>.FullAdelicCliffordGeneralSpinGroup)) :=
  W.isClosed_nonisotropicLastComplementGeneralSpinStabilizerSubgroup
    a ha RationalAdele

noncomputable local instance orbitCentralSubgroupQuotientT2Space
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    T2Space (W.FullAdelicNonisotropicLastShellHomogeneousSpace a ha) :=
  QuotientGroup.instT2Space

noncomputable local instance orbitCentralSubgroupQuotientSecondCountable
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    SecondCountableTopology
      (W.FullAdelicNonisotropicLastShellHomogeneousSpace a ha) :=
  QuotientGroup.instSecondCountableTopology
    (W.nonisotropicLastComplementGeneralSpinStabilizerSubgroup
      a ha RationalAdele)

noncomputable local instance orbitCentralSubgroupQuotientLocallyCompact
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    LocallyCompactSpace
      (W.FullAdelicNonisotropicLastShellHomogeneousSpace a ha) :=
  QuotientGroup.instLocallyCompactSpace
    (W.nonisotropicLastComplementGeneralSpinStabilizerSubgroup
      a ha RationalAdele)

noncomputable local instance orbitCentralSubgroupQuotientMeasurableSpace
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    MeasurableSpace (W.FullAdelicNonisotropicLastShellHomogeneousSpace a ha) :=
  borel _

noncomputable local instance orbitCentralSubgroupQuotientBorelSpace
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    BorelSpace (W.FullAdelicNonisotropicLastShellHomogeneousSpace a ha) :=
  ⟨rfl⟩

noncomputable local instance orbitCentralSubgroupTargetMeasurableSpace
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    MeasurableSpace (W.nonisotropicLastQuadraticShell a ha RationalAdele) :=
  borel _

noncomputable local instance orbitCentralSubgroupTargetBorelSpace
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    BorelSpace (W.nonisotropicLastQuadraticShell a ha RationalAdele) :=
  ⟨rfl⟩

noncomputable local instance orbitCentralSubgroupLowerMeasurableSpace
    (V : RationalQuadraticSpaceMatrix n) : MeasurableSpace V.FullAdelicCliffordGeneralSpinGroup :=
  borel _

noncomputable local instance orbitCentralSubgroupLowerBorelSpace
    (V : RationalQuadraticSpaceMatrix n) : BorelSpace V.FullAdelicCliffordGeneralSpinGroup :=
  ⟨rfl⟩

noncomputable local instance orbitCentralSubgroupFiniteMeasurableSpace
    (V : RationalQuadraticSpaceMatrix n) : MeasurableSpace V.FiniteAdelicCliffordGeneralSpinGroup :=
  borel _

noncomputable local instance orbitCentralSubgroupFiniteBorelSpace
    (V : RationalQuadraticSpaceMatrix n) : BorelSpace V.FiniteAdelicCliffordGeneralSpinGroup :=
  ⟨rfl⟩

noncomputable local instance orbitCentralSubgroupUnitMeasurableSpace : MeasurableSpace ℝˣ := borel _
noncomputable local instance orbitCentralSubgroupUnitBorelSpace : BorelSpace ℝˣ := ⟨rfl⟩

noncomputable local instance orbitCentralSubgroupSOMeasurableSpace (V : RationalQuadraticSpaceMatrix n) :
    MeasurableSpace (V.specialOrthogonalMatrixGroup ℝ) :=
  V.realSpecialOrthogonalGroupMeasurableSpace_spinorNorm

noncomputable local instance orbitCentralSubgroupSOBorelSpace (V : RationalQuadraticSpaceMatrix n) :
    BorelSpace (V.specialOrthogonalMatrixGroup ℝ) :=
  V.realSpecialOrthogonalGroupBorelSpace_spinorNorm

/-- The real sign subgroup `{t : t² = 1}` of `ℝˣ`. -/
def realSignUnitsSubgroup : Subgroup ℝˣ := (powMonoidHom 2 : ℝˣ →* ℝˣ).ker

theorem mem_realSignUnitsSubgroup_iff (t : ℝˣ) : t ∈ realSignUnitsSubgroup ↔ t ^ 2 = 1 :=
  MonoidHom.mem_ker

theorem eq_one_or_eq_neg_one_of_mem_realSignUnitsSubgroup {t : ℝˣ}
    (ht : t ∈ realSignUnitsSubgroup) : t = 1 ∨ t = -1 := by
  rw [mem_realSignUnitsSubgroup_iff] at ht
  have h : (t : ℝ) * t = 1 := by
    have := congrArg Units.val ht
    simpa [sq] using this
  rcases mul_self_eq_one_iff.1 h with h1 | h1
  · exact Or.inl (Units.ext h1)
  · exact Or.inr (Units.ext (by simpa using h1))

/-- The central-cutoff subgroup `{ν(g_∞)² = 1, toSO(g_∞) ∈ S, g_f ∈ K_f}`. -/
def centralCutoffSubgroup (V : RationalQuadraticSpaceMatrix n)
    (S : Subgroup (V.specialOrthogonalMatrixGroup ℝ))
    (Kf : Subgroup V.FiniteAdelicCliffordGeneralSpinGroup) :
    Subgroup V.FullAdelicCliffordGeneralSpinGroup :=
  (((realSignUnitsSubgroup.prod S).comap
      (CliffordGeneralSpinIntrinsicPoint.centralFiberGroupHom V ℝ)).prod Kf).comap
    V.fullAdelicCliffordGeneralSpinRealFiniteContinuousEquiv.toMulEquiv.toMonoidHom

/-- The central cutoff set `{ν(g_∞) ∈ T, toSO(g_∞) ∈ S, g_f ∈ K_f}`. -/
def centralCutoffSet (V : RationalQuadraticSpaceMatrix n) (T : Set ℝˣ)
    (S : Set (V.specialOrthogonalMatrixGroup ℝ)) (Kf : Set V.FiniteAdelicCliffordGeneralSpinGroup) :
    Set V.FullAdelicCliffordGeneralSpinGroup :=
  V.fullAdelicCliffordGeneralSpinRealFiniteContinuousEquiv ⁻¹'
    ((CliffordGeneralSpinIntrinsicPoint.centralFiberGroupHom V ℝ ⁻¹' (T ×ˢ S)) ×ˢ Kf)

theorem mem_centralCutoffSubgroup_iff (V : RationalQuadraticSpaceMatrix n)
    (S : Subgroup (V.specialOrthogonalMatrixGroup ℝ))
    (Kf : Subgroup V.FiniteAdelicCliffordGeneralSpinGroup) (g : V.FullAdelicCliffordGeneralSpinGroup) :
    g ∈ V.centralCutoffSubgroup S Kf ↔
      (CliffordGeneralSpinIntrinsicPoint.centralFiberGroupHom V ℝ
          (V.fullAdelicCliffordGeneralSpinRealFiniteContinuousEquiv g).1).1 ∈ realSignUnitsSubgroup ∧
        (CliffordGeneralSpinIntrinsicPoint.centralFiberGroupHom V ℝ
          (V.fullAdelicCliffordGeneralSpinRealFiniteContinuousEquiv g).1).2 ∈ S ∧
        (V.fullAdelicCliffordGeneralSpinRealFiniteContinuousEquiv g).2 ∈ Kf := by
  simp only [centralCutoffSubgroup, Subgroup.mem_comap, Subgroup.mem_prod, and_assoc]
  rfl

theorem mem_centralCutoffSet_iff (V : RationalQuadraticSpaceMatrix n) (T : Set ℝˣ)
    (S : Set (V.specialOrthogonalMatrixGroup ℝ)) (Kf : Set V.FiniteAdelicCliffordGeneralSpinGroup)
    (g : V.FullAdelicCliffordGeneralSpinGroup) :
    g ∈ V.centralCutoffSet T S Kf ↔
      (CliffordGeneralSpinIntrinsicPoint.centralFiberGroupHom V ℝ
          (V.fullAdelicCliffordGeneralSpinRealFiniteContinuousEquiv g).1).1 ∈ T ∧
        (CliffordGeneralSpinIntrinsicPoint.centralFiberGroupHom V ℝ
          (V.fullAdelicCliffordGeneralSpinRealFiniteContinuousEquiv g).1).2 ∈ S ∧
        (V.fullAdelicCliffordGeneralSpinRealFiniteContinuousEquiv g).2 ∈ Kf := by
  simp only [centralCutoffSet, Set.mem_preimage, Set.mem_prod, and_assoc]

/-- Left stability: the cutoff set is stable under left multiplication by the cutoff subgroup. -/
theorem mul_mem_centralCutoffSet_iff (V : RationalQuadraticSpaceMatrix n) {T : Set ℝˣ}
    (hneg : ∀ t : ℝˣ, -t ∈ T ↔ t ∈ T) (S : Subgroup (V.specialOrthogonalMatrixGroup ℝ))
    (Kf : Subgroup V.FiniteAdelicCliffordGeneralSpinGroup) {k : V.FullAdelicCliffordGeneralSpinGroup}
    (hk : k ∈ V.centralCutoffSubgroup S Kf) (g : V.FullAdelicCliffordGeneralSpinGroup) :
    k * g ∈ V.centralCutoffSet T S Kf ↔ g ∈ V.centralCutoffSet T S Kf := by
  rw [mem_centralCutoffSubgroup_iff] at hk
  obtain ⟨hν, hS, hf⟩ := hk
  rw [mem_centralCutoffSet_iff, mem_centralCutoffSet_iff, map_mul, Prod.fst_mul, Prod.snd_mul,
    map_mul, Prod.fst_mul, Prod.snd_mul]
  refine and_congr ?_ (and_congr (S.mul_mem_cancel_left hS) (Kf.mul_mem_cancel_left hf))
  rcases eq_one_or_eq_neg_one_of_mem_realSignUnitsSubgroup hν with h1 | h1
  · rw [h1, one_mul]
  · rw [h1, neg_one_mul]
    exact hneg _

private theorem sq_mul_inv_sq_sq_eq_one {t s : ℝ} (ht : t ≠ 0) (hs : s ^ 2 = |t|) :
    t ^ 2 * (s ^ 2)⁻¹ ^ 2 = 1 := by
  have hs4 : (s ^ 2) ^ 2 = t ^ 2 := by rw [hs, sq_abs]
  rw [inv_pow, hs4]
  exact mul_inv_cancel₀ (pow_ne_zero 2 ht)

/-- The central scalar decomposition: every point of the cutoff set is a point of the cutoff
subgroup times the adelic central scalar with real component `√|ν(g_∞)|` and finite
component `1`. -/
theorem exists_mem_centralCutoffSubgroup_mul_scalar (V : RationalQuadraticSpaceMatrix n)
    (T : Set ℝˣ) (S : Subgroup (V.specialOrthogonalMatrixGroup ℝ))
    (Kf : Subgroup V.FiniteAdelicCliffordGeneralSpinGroup) {g : V.FullAdelicCliffordGeneralSpinGroup}
    (hg : g ∈ V.centralCutoffSet T S Kf) :
    ∃ k ∈ V.centralCutoffSubgroup S Kf, ∃ u : RationalAdeleˣ,
      g = k * CliffordGeneralSpinIntrinsicPoint.scalarGroupHom V RationalAdele u := by
  rw [mem_centralCutoffSet_iff] at hg
  obtain ⟨-, hS, hf⟩ := hg
  have ht0 : (0 : ℝ) < |((CliffordGeneralSpinIntrinsicPoint.centralFiberGroupHom V ℝ
      (V.fullAdelicCliffordGeneralSpinRealFiniteContinuousEquiv g).1).1 : ℝ)| :=
    abs_pos.2 (Units.ne_zero _)
  let s : ℝˣ := Units.mk0 (Real.sqrt |((CliffordGeneralSpinIntrinsicPoint.centralFiberGroupHom V ℝ
      (V.fullAdelicCliffordGeneralSpinRealFiniteContinuousEquiv g).1).1 : ℝ)|)
    (Real.sqrt_pos.2 ht0).ne'
  have hs2 : ((s : ℝ)) ^ 2 = |((CliffordGeneralSpinIntrinsicPoint.centralFiberGroupHom V ℝ
      (V.fullAdelicCliffordGeneralSpinRealFiniteContinuousEquiv g).1).1 : ℝ)| :=
    Real.sq_sqrt ht0.le
  let u : RationalAdeleˣ := rationalAdeleUnitsRealFiniteContinuousEquiv.symm (s, 1)
  have hez : V.fullAdelicCliffordGeneralSpinRealFiniteContinuousEquiv
      (CliffordGeneralSpinIntrinsicPoint.scalarGroupHom V RationalAdele u) =
        (CliffordGeneralSpinIntrinsicPoint.scalarGroupHom V ℝ s, 1) := by
    rw [V.fullAdelicCliffordGeneralSpinRealFiniteContinuousEquiv_scalarGroupHom u]
    simp only [u, ContinuousMulEquiv.apply_symm_apply, map_one]
  refine ⟨g * (CliffordGeneralSpinIntrinsicPoint.scalarGroupHom V RationalAdele u)⁻¹, ?_, u,
    (inv_mul_cancel_right _ _).symm⟩
  rw [mem_centralCutoffSubgroup_iff]
  have hscal : CliffordGeneralSpinIntrinsicPoint.centralFiberGroupHom V ℝ
      (CliffordGeneralSpinIntrinsicPoint.scalarGroupHom V ℝ s) = (s ^ 2, 1) := by
    rw [CliffordGeneralSpinIntrinsicPoint.centralFiberGroupHom_apply]
    exact Prod.ext rfl (CliffordGeneralSpinIntrinsicPoint.ofScalar_matrixGroup V ℝ s)
  rw [map_mul, map_inv, hez, Prod.fst_mul, Prod.snd_mul, Prod.fst_inv, Prod.snd_inv, inv_one,
    mul_one, map_mul, map_inv, hscal]
  simp only [Prod.fst_mul, Prod.snd_mul, Prod.fst_inv, Prod.snd_inv, inv_one, mul_one]
  refine ⟨?_, hS, hf⟩
  rw [mem_realSignUnitsSubgroup_iff]
  apply Units.ext
  simp only [Units.val_pow_eq_pow_val, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_one,
    mul_pow]
  exact sq_mul_inv_sq_sq_eq_one (Units.ne_zero _) hs2

/-- On the shell, every point of the cutoff set is the image of a point of the cutoff subgroup:
central scalars are block images of lower scalars and fix `x_old`. -/
theorem nonisotropicLastShellOrbitMap_mem_image_centralCutoffSubgroup
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) (T : Set ℝˣ)
    (S : Subgroup ((W.nonisotropicLastExtension a ha).specialOrthogonalMatrixGroup ℝ))
    (Kf : Subgroup (W.nonisotropicLastExtension a ha).FiniteAdelicCliffordGeneralSpinGroup)
    {g : (W.nonisotropicLastExtension a ha).FullAdelicCliffordGeneralSpinGroup}
    (hg : g ∈ (W.nonisotropicLastExtension a ha).centralCutoffSet T S Kf) :
    CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap W a ha RationalAdele g ∈
      (CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap W a ha RationalAdele) ''
        ((W.nonisotropicLastExtension a ha).centralCutoffSubgroup S Kf : Set _) := by
  obtain ⟨k, hk, u, rfl⟩ :=
    (W.nonisotropicLastExtension a ha).exists_mem_centralCutoffSubgroup_mul_scalar T S Kf hg
  refine ⟨k, hk, ?_⟩
  exact (CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap_mul_of_mem_stabilizer
    W a ha k _ ⟨CliffordGeneralSpinIntrinsicPoint.scalarGroupHom W RationalAdele u,
      W.nonisotropicLastComplementGeneralSpinPoint_ofScalar a ha RationalAdele u⟩).symm

/-- The discharged central-cutoff orbit identity: for supplied subgroups `S` (real block `SO`)
and `K_f` (finite block `GSpin`) and a supplied `-1`-stable `T` of finite positive Haar mass,

`N(K • x_old) · μ_{SO_W}(e⁻¹ S) · μ_{W,f}(ι_f⁻¹ K_f) = μ_{SO_V}(S) · μ_{V,f}(K_f)`,

with `K` the central-cutoff subgroup. -/
theorem fullAdelicNonisotropicLastShellMeasure_centralCutoffSubgroup_orbit
    (W : RationalQuadraticSpaceMatrix n) [NeZero n] (a : ℚ) (ha : a ≠ 0)
    {T : Set ℝˣ} (hT : MeasurableSet T) (hneg : ∀ t : ℝˣ, -t ∈ T ↔ t ∈ T)
    (hT0 : (Measure.haar : Measure ℝˣ) T ≠ 0) (hTtop : (Measure.haar : Measure ℝˣ) T ≠ ⊤)
    (S : Subgroup ((W.nonisotropicLastExtension a ha).specialOrthogonalMatrixGroup ℝ))
    (hS : MeasurableSet (S : Set ((W.nonisotropicLastExtension a ha).specialOrthogonalMatrixGroup ℝ)))
    (hSW : MeasurableSet (W.nonisotropicLastCoordinateFiberEmbedGroup a ha ℝ ⁻¹'
      (S : Set ((W.nonisotropicLastExtension a ha).specialOrthogonalMatrixGroup ℝ))))
    (Kf : Subgroup (W.nonisotropicLastExtension a ha).FiniteAdelicCliffordGeneralSpinGroup)
    (hKf : MeasurableSet (Kf : Set (W.nonisotropicLastExtension a ha).FiniteAdelicCliffordGeneralSpinGroup))
    (hWfin : MeasurableSet
      (W.nonisotropicLastComplementGeneralSpinPoint a ha RationalFiniteAdele ⁻¹' (Kf : Set _)))
    (hOm : MeasurableSet ((CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap
      W a ha RationalAdele) ''
        ((W.nonisotropicLastExtension a ha).centralCutoffSubgroup S Kf : Set _))) :
    W.fullAdelicNonisotropicLastShellMeasure a ha
        ((CliffordGeneralSpinIntrinsicPoint.nonisotropicLastShellOrbitMap W a ha RationalAdele) ''
          ((W.nonisotropicLastExtension a ha).centralCutoffSubgroup S Kf : Set _)) *
      (W.realInvariantDifferentialGroupMeasure
          (W.nonisotropicLastCoordinateFiberEmbedGroup a ha ℝ ⁻¹'
            (S : Set ((W.nonisotropicLastExtension a ha).specialOrthogonalMatrixGroup ℝ))) *
        W.finiteAdelicCliffordGeneralSpinHorizontalGroupMeasure
          (W.nonisotropicLastComplementGeneralSpinPoint a ha RationalFiniteAdele ⁻¹' (Kf : Set _))) =
      (W.nonisotropicLastExtension a ha).realInvariantDifferentialGroupMeasure
          (S : Set ((W.nonisotropicLastExtension a ha).specialOrthogonalMatrixGroup ℝ)) *
        (W.nonisotropicLastExtension a ha).finiteAdelicCliffordGeneralSpinHorizontalGroupMeasure
          (Kf : Set _) :=
  W.fullAdelicNonisotropicLastShellMeasure_orbit_mul_centralCutoff_of_leftStable a ha _ hT hneg
    hT0 hTtop hS hSW hKf hWfin
    (fun _k hk g ↦ (W.nonisotropicLastExtension a ha).mul_mem_centralCutoffSet_iff hneg S Kf hk g)
    (fun _g hg ↦ W.nonisotropicLastShellOrbitMap_mem_image_centralCutoffSubgroup a ha T S Kf hg) hOm

end RationalQuadraticSpaceMatrix

end
