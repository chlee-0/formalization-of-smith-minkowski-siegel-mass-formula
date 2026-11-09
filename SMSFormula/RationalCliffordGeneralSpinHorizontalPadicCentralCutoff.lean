import SMSFormula.RationalCliffordGeneralSpinHorizontalIntegralCentralFactor
import SMSFormula.RationalCliffordGeneralSpinFullAdelicShellOrbitCentralCutoff

/-!
# The p-adic central cutoff at every prime, and the relative bad-place local factor

The horizontal p-adic `GSpin` Haar is glued from `Haar(ℚ_p^×) × μ_SO` through the
central fiber map `φ = (ν, toSO)` with two sheets.  For a supplied measurable subgroup
`U ≤ ℚ_p^×` and a supplied measurable `S ⊆ SO(V)(ℚ_p)` all of whose points lift to `GSpin`
points of similitude in `U`, each slice of `(U × S) ∩ range φ` is a translate of
`U ⊓ (ℚ_p^×)²`, so at every prime `p` (including `2` and the bad primes)

`μ_GSpin(φ⁻¹(U × S)) = 2 · Haar(U ⊓ (ℚ_p^×)²) · μ_SO(S)`.

The constant `2 · Haar(U ⊓ (ℚ_p^×)²)` depends only on `p` and `U`, not on the form.  The
block embedding `ι` preserves the similitude and sends `toSO` to the fixed-last-coordinate
embedding `e`, so `ι⁻¹ φ_V⁻¹(U × S) = φ_W⁻¹(U × e⁻¹S)`; lifts for `e⁻¹S` follow from lifts
for `S` by field surjectivity.  Hence the relative local factor is

`μ_{GSpin_V}(t) · μ_{SO_W}(e⁻¹S) = μ_{GSpin_W}(ι⁻¹t) · μ_{SO_V}(S)`,  `t = φ_V⁻¹(U × S)`.

`U`, `S` and the lift hypothesis are supplied; no section, sheet or square class is chosen.
-/

noncomputable section

open MeasureTheory Set PositiveDefiniteIntegralLattice
open scoped ENNReal

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

set_option synthInstance.maxHeartbeats 700000
set_option maxHeartbeats 2400000

noncomputable local instance padicCutoffUnitMeasurableSpace (p : ℕ) [Fact (Nat.Prime p)] :
    MeasurableSpace ℚ_[p]ˣ := borel _

noncomputable local instance padicCutoffUnitBorelSpace (p : ℕ) [Fact (Nat.Prime p)] :
    BorelSpace ℚ_[p]ˣ := ⟨rfl⟩

noncomputable local instance padicCutoffSOMeasurableSpace (V : RationalQuadraticSpaceMatrix n)
    (p : ℕ) [Fact (Nat.Prime p)] :
    MeasurableSpace (V.specialOrthogonalMatrixGroup ℚ_[p]) :=
  V.padicSpecialOrthogonalGroupMeasurableSpace_spinorNorm p

noncomputable local instance padicCutoffSOBorelSpace (V : RationalQuadraticSpaceMatrix n)
    (p : ℕ) [Fact (Nat.Prime p)] :
    BorelSpace (V.specialOrthogonalMatrixGroup ℚ_[p]) :=
  V.padicSpecialOrthogonalGroupBorelSpace_spinorNorm p

set_option backward.isDefEq.respectTransparency false in
/-- The p-ADIC central cutoff at every prime: for a measurable subgroup `U ≤ ℚ_p^×` and a
measurable `S ⊆ SO(V)(ℚ_p)` whose points lift with similitude in `U`,
`μ_GSpin(φ⁻¹(U × S)) = 2 · Haar(U ⊓ (ℚ_p^×)²) · μ_SO(S)`. -/
theorem padicCliffordGeneralSpinHorizontalDifferentialHaarMeasure_centralFiber
    (V : RationalQuadraticSpaceMatrix n) (p : ℕ) [Fact (Nat.Prime p)] (U : Subgroup ℚ_[p]ˣ)
    (hU : MeasurableSet (U : Set ℚ_[p]ˣ))
    (S : Set (V.specialOrthogonalMatrixGroup ℚ_[p])) (hS : MeasurableSet S)
    (hlift : ∀ g ∈ S, ∃ y : V.CliffordGeneralSpinIntrinsicPoint ℚ_[p],
      y.similitude ∈ U ∧ CliffordGeneralSpinIntrinsicPoint.toSpecialOrthogonalGroupHom V _ y = g) :
    V.padicCliffordGeneralSpinHorizontalDifferentialHaarMeasure p
        (CliffordGeneralSpinIntrinsicPoint.centralFiberGroupHom V ℚ_[p] ⁻¹' ((U : Set ℚ_[p]ˣ) ×ˢ S)) =
      2 * (Measure.haar : Measure ℚ_[p]ˣ) ((U ⊓ Subgroup.square ℚ_[p]ˣ : Subgroup ℚ_[p]ˣ) : Set ℚ_[p]ˣ) *
        V.padicInvariantDifferentialGroupMeasure p S := by
  haveI := padicCayleySpecialOrthogonalDifferentialMeasure_isHaarMeasure
    p n V.pairingMatrix V.form_symm V.form_det_ne_zero
  haveI : SigmaFinite (padicCayleySpecialOrthogonalDifferentialMeasure
      p n V.pairingMatrix V.form_det_ne_zero) :=
    padicCayleySpecialOrthogonalDifferentialMeasure_sigmaFinite
      p n V.pairingMatrix V.form_symm V.form_det_ne_zero
  have hRo := V.isOpen_padicCliffordGeneralSpinCentralFiberImage p
  rw [MonoidHom.coe_range] at hRo
  have hA : MeasurableSet (((U : Set ℚ_[p]ˣ) ×ˢ S) ∩
      Set.range (CliffordGeneralSpinIntrinsicPoint.centralFiberGroupHom V ℚ_[p])) :=
    (hU.prod hS).inter hRo.measurableSet
  set Q : Set ℚ_[p]ˣ := ((U ⊓ Subgroup.square ℚ_[p]ˣ : Subgroup ℚ_[p]ˣ) : Set ℚ_[p]ˣ) with hQ
  have hslice : ∀ g : V.specialOrthogonalMatrixGroup ℚ_[p],
      (Measure.haar : Measure ℚ_[p]ˣ) ((fun t ↦ (t, g)) ⁻¹' (((U : Set ℚ_[p]ˣ) ×ˢ S) ∩
          Set.range (CliffordGeneralSpinIntrinsicPoint.centralFiberGroupHom V ℚ_[p]))) =
        S.indicator (fun _ ↦ (Measure.haar : Measure ℚ_[p]ˣ) Q) g := by
    intro g
    by_cases hg : g ∈ S
    · rw [Set.indicator_of_mem hg]
      obtain ⟨y, hy0, hyg⟩ := hlift g hg
      have hsl : (fun t ↦ (t, g)) ⁻¹' (((U : Set ℚ_[p]ˣ) ×ˢ S) ∩
          Set.range (CliffordGeneralSpinIntrinsicPoint.centralFiberGroupHom V ℚ_[p])) =
          (fun t ↦ y.similitude⁻¹ * t) ⁻¹' Q := by
        ext t
        simp only [Set.mem_preimage, Set.mem_inter_iff, Set.mem_prod, SetLike.mem_coe, Set.mem_range,
          hQ, Subgroup.mem_inf, Subgroup.mem_square]
        constructor
        · rintro ⟨⟨ht, -⟩, x, hx⟩
          have hxν : x.similitude = t := congrArg Prod.fst hx
          have hxπ : CliffordGeneralSpinIntrinsicPoint.toSpecialOrthogonalGroupHom V _ x = g :=
            congrArg Prod.snd hx
          have hker : x * y⁻¹ ∈
              (CliffordGeneralSpinIntrinsicPoint.toSpecialOrthogonalGroupHom V _).ker := by
            rw [MonoidHom.mem_ker, map_mul, map_inv, hxπ, hyg, mul_inv_cancel]
          rw [← CliffordGeneralSpinIntrinsicPoint.range_scalarGroupHom_eq_ker_toSpecialOrthogonalGroupHom]
            at hker
          obtain ⟨a, ha⟩ := hker
          have hxa : x = CliffordGeneralSpinIntrinsicPoint.scalarGroupHom V _ a * y := by
            rw [ha, inv_mul_cancel_right]
          have htt : t = a ^ 2 * y.similitude := by
            rw [← hxν, hxa, CliffordGeneralSpinIntrinsicPoint.mul_similitude]; rfl
          refine ⟨U.mul_mem (U.inv_mem hy0) ht, a, ?_⟩
          rw [htt, pow_two, mul_comm, mul_inv_cancel_right]
        · rintro ⟨hmem, b, hb⟩
          have ht : t = y.similitude * (b * b) := by
            rw [← hb, mul_inv_cancel_left]
          refine ⟨⟨?_, hg⟩, CliffordGeneralSpinIntrinsicPoint.scalarGroupHom V _ b * y, ?_⟩
          · have := U.mul_mem hy0 hmem
            rwa [mul_inv_cancel_left] at this
          · refine Prod.ext ?_ ?_
            · change (CliffordGeneralSpinIntrinsicPoint.scalarGroupHom V _ b * y).similitude = t
              rw [CliffordGeneralSpinIntrinsicPoint.mul_similitude, ht]
              change b ^ 2 * y.similitude = _
              rw [pow_two, mul_comm]
            · change CliffordGeneralSpinIntrinsicPoint.toSpecialOrthogonalGroupHom V _
                (CliffordGeneralSpinIntrinsicPoint.scalarGroupHom V _ b * y) = g
              rw [map_mul, hyg]
              have : CliffordGeneralSpinIntrinsicPoint.scalarGroupHom V _ b ∈
                  (CliffordGeneralSpinIntrinsicPoint.toSpecialOrthogonalGroupHom V _).ker := by
                rw [← CliffordGeneralSpinIntrinsicPoint.range_scalarGroupHom_eq_ker_toSpecialOrthogonalGroupHom]
                exact ⟨b, rfl⟩
              rw [MonoidHom.mem_ker.mp this, one_mul]
      rw [hsl, measure_preimage_mul]
    · rw [Set.indicator_of_notMem hg]
      exact measure_mono_null (fun t ht ↦ (hg ht.1.2).elim) measure_empty
  rw [V.padicCliffordGeneralSpinHorizontalDifferentialHaarMeasure_preimage p (hU.prod hS),
    padicCliffordGeneralSpinHorizontalDifferentialProductMeasure, padicInvariantDifferentialGroupMeasure,
    Measure.prod_apply_symm hA]
  simp_rw [hslice]
  rw [lintegral_indicator_const hS, mul_assoc]
  rfl

/-- At an odd prime with `U = ℤ_p^×`, the central constant is the common mass `Haar(ℤ_p^×)`. -/
theorem padicCliffordGeneralSpinHorizontalDifferentialHaarMeasure_centralFiber_integralUnits
    (V : RationalQuadraticSpaceMatrix n) (p : ℕ) [Fact (Nat.Prime p)] (hp : p ≠ 2)
    (S : Set (V.specialOrthogonalMatrixGroup ℚ_[p])) (hS : MeasurableSet S)
    (hlift : ∀ g ∈ S, ∃ y : V.CliffordGeneralSpinIntrinsicPoint ℚ_[p],
      y.similitude ∈ padicIntegralUnitsSubgroup p ∧
        CliffordGeneralSpinIntrinsicPoint.toSpecialOrthogonalGroupHom V _ y = g) :
    V.padicCliffordGeneralSpinHorizontalDifferentialHaarMeasure p
        (CliffordGeneralSpinIntrinsicPoint.centralFiberGroupHom V ℚ_[p] ⁻¹'
          ((padicIntegralUnitsSubgroup p : Set ℚ_[p]ˣ) ×ˢ S)) =
      padicIntegralUnitsHaarMass p * V.padicInvariantDifferentialGroupMeasure p S := by
  rw [V.padicCliffordGeneralSpinHorizontalDifferentialHaarMeasure_centralFiber p _
      (isOpen_padicIntegralUnitsSubgroup p).measurableSet S hS hlift,
    padicIntegralUnitsHaarMass, haar_padicIntegralUnits_eq_two_mul p hp]

/-- The pullback of a block central cutoff through the block embedding, over any
coefficient ring. -/
theorem preimage_centralFiber_nonisotropicLastComplementGeneralSpinPoint_of
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (A : Type*) [Field A] [Algebra ℚ A] (T : Set Aˣ)
    (S : Set ((W.nonisotropicLastExtension a ha).specialOrthogonalMatrixGroup A)) :
    W.nonisotropicLastComplementGeneralSpinPoint a ha A ⁻¹'
        (CliffordGeneralSpinIntrinsicPoint.centralFiberGroupHom (W.nonisotropicLastExtension a ha)
          A ⁻¹' (T ×ˢ S)) =
      CliffordGeneralSpinIntrinsicPoint.centralFiberGroupHom W A ⁻¹'
        (T ×ˢ (W.nonisotropicLastCoordinateFiberEmbedGroup a ha A ⁻¹' S)) := by
  ext x
  simp only [Set.mem_preimage, Set.mem_prod, CliffordGeneralSpinIntrinsicPoint.centralFiberGroupHom_apply,
    nonisotropicLastComplementGeneralSpinPoint_similitude,
    nonisotropicLastComplementGeneralSpinPoint_matrixGroup]

/-- Lifts descend: over a field, if `e(h)` lifts to a block `GSpin` point of similitude `s`,
then `h` lifts to a lower `GSpin` point of the same similitude `s`. -/
theorem exists_lower_lift_of_block_lift
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (K : Type*) [Field K] [Algebra ℚ K] [CharZero K]
    (h : W.specialOrthogonalMatrixGroup K)
    (y : (W.nonisotropicLastExtension a ha).CliffordGeneralSpinIntrinsicPoint K)
    (hy : CliffordGeneralSpinIntrinsicPoint.toSpecialOrthogonalGroupHom _ K y =
      W.nonisotropicLastCoordinateFiberEmbedGroup a ha K h) :
    ∃ z : W.CliffordGeneralSpinIntrinsicPoint K,
      z.similitude = y.similitude ∧
        CliffordGeneralSpinIntrinsicPoint.toSpecialOrthogonalGroupHom W K z = h := by
  obtain ⟨z₀, hz₀⟩ := CliffordGeneralSpinIntrinsicPoint.toSpecialOrthogonalGroupHom_surjective W K h
  have hι : CliffordGeneralSpinIntrinsicPoint.toSpecialOrthogonalGroupHom _ K
      (W.nonisotropicLastComplementGeneralSpinPoint a ha K z₀) =
        W.nonisotropicLastCoordinateFiberEmbedGroup a ha K h := by
    change (W.nonisotropicLastComplementGeneralSpinPoint a ha K z₀).matrixGroup = _
    rw [nonisotropicLastComplementGeneralSpinPoint_matrixGroup]
    exact congrArg _ hz₀
  have hker : y * (W.nonisotropicLastComplementGeneralSpinPoint a ha K z₀)⁻¹ ∈
      (CliffordGeneralSpinIntrinsicPoint.toSpecialOrthogonalGroupHom _ K).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hy, hι, mul_inv_cancel]
  rw [← CliffordGeneralSpinIntrinsicPoint.range_scalarGroupHom_eq_ker_toSpecialOrthogonalGroupHom]
    at hker
  obtain ⟨c, hc⟩ := hker
  have hyc : y = CliffordGeneralSpinIntrinsicPoint.scalarGroupHom _ K c *
      W.nonisotropicLastComplementGeneralSpinPoint a ha K z₀ := by
    rw [hc, inv_mul_cancel_right]
  refine ⟨CliffordGeneralSpinIntrinsicPoint.scalarGroupHom W K c * z₀, ?_, ?_⟩
  · rw [hyc, CliffordGeneralSpinIntrinsicPoint.mul_similitude,
      CliffordGeneralSpinIntrinsicPoint.mul_similitude,
      nonisotropicLastComplementGeneralSpinPoint_similitude]
    rfl
  · rw [map_mul, hz₀]
    have : CliffordGeneralSpinIntrinsicPoint.scalarGroupHom W K c ∈
        (CliffordGeneralSpinIntrinsicPoint.toSpecialOrthogonalGroupHom W K).ker := by
      rw [← CliffordGeneralSpinIntrinsicPoint.range_scalarGroupHom_eq_ker_toSpecialOrthogonalGroupHom]
      exact ⟨c, rfl⟩
    rw [MonoidHom.mem_ker.mp this, one_mul]

/-- The p-adic central fiber map `(ν, toSO)` is continuous (identity chart). -/
theorem continuous_centralFiberGroupHom_padic (V : RationalQuadraticSpaceMatrix n)
    (p : ℕ) [Fact (Nat.Prime p)] :
    Continuous (CliffordGeneralSpinIntrinsicPoint.centralFiberGroupHom V ℚ_[p]) := by
  have hfe := V.padicCliffordGeneralSpinCentralFiberIdentityChart_coe p
  have hone := V.one_mem_padicCliffordGeneralSpinCentralFiberIdentityChart_source p
  refine continuous_of_continuousAt_one
    (CliffordGeneralSpinIntrinsicPoint.centralFiberGroupHom V ℚ_[p]) ?_
  have h := (V.padicCliffordGeneralSpinCentralFiberIdentityChart p).continuousAt hone
  rwa [← hfe] at h

/-- The lower side of the relative local factor: the pullback of a block central cutoff has
`GSpin_W` mass `2 · Haar(U ⊓ (ℚ_p^×)²) · μ_{SO_W}(e⁻¹S)`. -/
theorem padicCliffordGeneralSpinHorizontalDifferentialHaarMeasure_preimage_block_centralFiber
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) (p : ℕ) [Fact (Nat.Prime p)]
    (U : Subgroup ℚ_[p]ˣ) (hU : MeasurableSet (U : Set ℚ_[p]ˣ))
    (S : Set ((W.nonisotropicLastExtension a ha).specialOrthogonalMatrixGroup ℚ_[p]))
    (hSW : MeasurableSet (W.nonisotropicLastCoordinateFiberEmbedGroup a ha ℚ_[p] ⁻¹' S))
    (hlift : ∀ g ∈ S, ∃ y : (W.nonisotropicLastExtension a ha).CliffordGeneralSpinIntrinsicPoint ℚ_[p],
      y.similitude ∈ U ∧ CliffordGeneralSpinIntrinsicPoint.toSpecialOrthogonalGroupHom _ _ y = g) :
    W.padicCliffordGeneralSpinHorizontalDifferentialHaarMeasure p
        (W.nonisotropicLastComplementGeneralSpinPoint a ha ℚ_[p] ⁻¹'
          (CliffordGeneralSpinIntrinsicPoint.centralFiberGroupHom (W.nonisotropicLastExtension a ha)
            ℚ_[p] ⁻¹' ((U : Set ℚ_[p]ˣ) ×ˢ S))) =
      2 * (Measure.haar : Measure ℚ_[p]ˣ) ((U ⊓ Subgroup.square ℚ_[p]ˣ : Subgroup ℚ_[p]ˣ) : Set ℚ_[p]ˣ) *
        W.padicInvariantDifferentialGroupMeasure p
          (W.nonisotropicLastCoordinateFiberEmbedGroup a ha ℚ_[p] ⁻¹' S) := by
  have hliftW : ∀ h ∈ W.nonisotropicLastCoordinateFiberEmbedGroup a ha ℚ_[p] ⁻¹' S,
      ∃ z : W.CliffordGeneralSpinIntrinsicPoint ℚ_[p],
        z.similitude ∈ U ∧ CliffordGeneralSpinIntrinsicPoint.toSpecialOrthogonalGroupHom W _ z = h := by
    intro h hh
    obtain ⟨y, hyU, hyg⟩ := hlift _ hh
    obtain ⟨z, hz, hzh⟩ := W.exists_lower_lift_of_block_lift a ha ℚ_[p] h y hyg
    exact ⟨z, hz ▸ hyU, hzh⟩
  rw [W.preimage_centralFiber_nonisotropicLastComplementGeneralSpinPoint_of a ha ℚ_[p]]
  exact W.padicCliffordGeneralSpinHorizontalDifferentialHaarMeasure_centralFiber p U hU _ hSW hliftW

set_option backward.isDefEq.respectTransparency false in
/-- The relative p-ADIC local factor at every prime: for `t = φ_V⁻¹(U × S)` with supplied
measurable `U`, `S`, measurable `e⁻¹S`, and lifts of `S` with similitude in `U`,

`μ_{GSpin_V}(t) · μ_{SO_W}(e⁻¹S) = μ_{GSpin_W}(ι⁻¹ t) · μ_{SO_V}(S)`. -/
theorem padicCliffordGeneralSpinHorizontalDifferentialHaarMeasure_centralFiber_relative
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) (p : ℕ) [Fact (Nat.Prime p)]
    (U : Subgroup ℚ_[p]ˣ) (hU : MeasurableSet (U : Set ℚ_[p]ˣ))
    (S : Set ((W.nonisotropicLastExtension a ha).specialOrthogonalMatrixGroup ℚ_[p]))
    (hS : MeasurableSet S)
    (hSW : MeasurableSet (W.nonisotropicLastCoordinateFiberEmbedGroup a ha ℚ_[p] ⁻¹' S))
    (hlift : ∀ g ∈ S, ∃ y : (W.nonisotropicLastExtension a ha).CliffordGeneralSpinIntrinsicPoint ℚ_[p],
      y.similitude ∈ U ∧ CliffordGeneralSpinIntrinsicPoint.toSpecialOrthogonalGroupHom _ _ y = g) :
    (W.nonisotropicLastExtension a ha).padicCliffordGeneralSpinHorizontalDifferentialHaarMeasure p
        (CliffordGeneralSpinIntrinsicPoint.centralFiberGroupHom (W.nonisotropicLastExtension a ha)
          ℚ_[p] ⁻¹' ((U : Set ℚ_[p]ˣ) ×ˢ S)) *
        W.padicInvariantDifferentialGroupMeasure p
          (W.nonisotropicLastCoordinateFiberEmbedGroup a ha ℚ_[p] ⁻¹' S) =
      W.padicCliffordGeneralSpinHorizontalDifferentialHaarMeasure p
          (W.nonisotropicLastComplementGeneralSpinPoint a ha ℚ_[p] ⁻¹'
            (CliffordGeneralSpinIntrinsicPoint.centralFiberGroupHom (W.nonisotropicLastExtension a ha)
              ℚ_[p] ⁻¹' ((U : Set ℚ_[p]ˣ) ×ˢ S))) *
        (W.nonisotropicLastExtension a ha).padicInvariantDifferentialGroupMeasure p S := by
  have hliftW : ∀ h ∈ W.nonisotropicLastCoordinateFiberEmbedGroup a ha ℚ_[p] ⁻¹' S,
      ∃ z : W.CliffordGeneralSpinIntrinsicPoint ℚ_[p],
        z.similitude ∈ U ∧ CliffordGeneralSpinIntrinsicPoint.toSpecialOrthogonalGroupHom W _ z = h := by
    intro h hh
    obtain ⟨y, hyU, hyg⟩ := hlift _ hh
    obtain ⟨z, hz, hzh⟩ := W.exists_lower_lift_of_block_lift a ha ℚ_[p] h y hyg
    exact ⟨z, hz ▸ hyU, hzh⟩
  rw [W.preimage_centralFiber_nonisotropicLastComplementGeneralSpinPoint_of a ha ℚ_[p],
    (W.nonisotropicLastExtension a ha).padicCliffordGeneralSpinHorizontalDifferentialHaarMeasure_centralFiber
      p U hU S hS hlift,
    W.padicCliffordGeneralSpinHorizontalDifferentialHaarMeasure_centralFiber p U hU _ hSW hliftW]
  ring_nf <;> rfl

end RationalQuadraticSpaceMatrix
