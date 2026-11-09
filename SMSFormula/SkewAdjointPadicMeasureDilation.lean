import SMSFormula.SkewAdjointPadicMeasureTransport
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.Topology.Instances.ZMod

/-!
# One-coordinate p-adic dilation of the skew-adjoint measure

Multiplication of one transported skew-adjoint coordinate by `p^k` has
determinant norm `p⁻ᵏ`. The image of the unit coordinate lattice has volume
`p⁻ᵏ`, so the pushforward of the normalized additive Haar measure is `p^k`
times that measure, equivalently the inverse determinant norm times it.

The lattice-volume calculation is intrinsic: it comaps the coordinate measure
to `Z_p^d` and computes the kernel index of reduction to `ZMod (p^k)`. No
orthogonal-group measure or stabilizer normalization is used.
-/

noncomputable section

open MeasureTheory
open Topology
open scoped NNReal ENNReal

namespace Matrix

variable {d : ℕ}

private def padicPowerUnit (p k : ℕ) [Fact (Nat.Prime p)] : ℚ_[p]ˣ :=
  Units.mk0 ((p : ℚ_[p]) ^ k)
    (pow_ne_zero _ (by exact_mod_cast (Fact.out : Nat.Prime p).ne_zero))

def padicPowerCoordinateDilation (p k : ℕ) [Fact (Nat.Prime p)]
    (i : Fin d) : (Fin d → ℚ_[p]) ≃L[ℚ_[p]] (Fin d → ℚ_[p]) :=
  ContinuousLinearEquiv.piCongrRight fun j =>
    if j = i then
      ContinuousLinearEquiv.smulLeft
        (R₁ := ℚ_[p]) (M₁ := ℚ_[p]) (padicPowerUnit p k)
    else ContinuousLinearEquiv.refl ℚ_[p] ℚ_[p]

@[simp]
theorem padicPowerCoordinateDilation_apply (p k : ℕ)
    [Fact (Nat.Prime p)] (i : Fin d) (x : Fin d → ℚ_[p]) (j : Fin d) :
    padicPowerCoordinateDilation p k i x j =
      if j = i then (p : ℚ_[p]) ^ k * x j else x j := by
  classical
  by_cases h : j = i
  · subst j
    simp [padicPowerCoordinateDilation, padicPowerUnit,
      ContinuousLinearEquiv.smulLeft, smul_eq_mul]
  · simp [padicPowerCoordinateDilation, h]

private theorem padicPowerCoordinateDilation_det
    (p k : ℕ) [Fact (Nat.Prime p)] (i : Fin d) :
    LinearMap.det (padicPowerCoordinateDilation p k i).toLinearMap =
      (p : ℚ_[p]) ^ k := by
  classical
  have hmap :
      (padicPowerCoordinateDilation p k i).toLinearMap =
        Matrix.toLin'
          (diagonal fun j : Fin d => if j = i then (p : ℚ_[p]) ^ k else 1) := by
    apply LinearMap.ext
    intro x
    funext j
    change padicPowerCoordinateDilation p k i x j = _
    rw [padicPowerCoordinateDilation_apply]
    simp [Matrix.toLin'_apply, mulVec_diagonal]
  rw [hmap, LinearMap.det_toLin', Matrix.det_diagonal]
  simp

theorem padicPowerCoordinateDilation_det_norm
    (p k : ℕ) [Fact (Nat.Prime p)] (i : Fin d) :
    ‖LinearMap.det (padicPowerCoordinateDilation p k i).toLinearMap‖ =
      (p : ℝ) ^ (-k : ℤ) := by
  rw [padicPowerCoordinateDilation_det, Padic.norm_p_pow]

private def padicIntCoordinateCoe (p d : ℕ) [Fact (Nat.Prime p)] :
    (Fin d → ℤ_[p]) →+ (Fin d → ℚ_[p]) where
  toFun z i := z i
  map_zero' := rfl
  map_add' _ _ := by
    funext i
    exact PadicInt.coe_add _ _

private theorem padicIntCoordinateCoe_isOpenEmbedding
    (p d : ℕ) [Fact (Nat.Prime p)] :
    IsOpenEmbedding (padicIntCoordinateCoe p d) := by
  exact Topology.IsOpenEmbedding.piMap
    (fun _ : Fin d ↦ PadicInt.isOpenEmbedding_coe)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

local instance padicDilationPadicIntPiMeasurableSpace
    (p d : ℕ) [Fact (Nat.Prime p)] :
    MeasurableSpace (Fin d → ℤ_[p]) :=
  borel _

local instance padicDilationPadicIntPiBorelSpace
    (p d : ℕ) [Fact (Nat.Prime p)] :
    BorelSpace (Fin d → ℤ_[p]) :=
  ⟨rfl⟩

local instance padicDilationSkewMeasurableSpace
    (F : Matrix ι ι ℚ) (p : ℕ) [Fact (Nat.Prime p)] :
    MeasurableSpace
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  borel _

local instance padicDilationSkewBorelSpace
    (F : Matrix ι ι ℚ) (p : ℕ) [Fact (Nat.Prime p)] :
    BorelSpace
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  ⟨rfl⟩

local instance padicDilationSkewSecondCountableTopology
    (F : Matrix ι ι ℚ) (p : ℕ) [Fact (Nat.Prime p)] :
    SecondCountableTopology
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule := by
  letI : SecondCountableTopology (ι → ℚ_[p]) :=
    TopologicalSpace.instSecondCountableTopologyForallOfCountable
  letI : SecondCountableTopology (Matrix ι ι ℚ_[p]) :=
    TopologicalSpace.instSecondCountableTopologyForallOfCountable
  exact TopologicalSpace.secondCountableTopology_induced
    (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule
    (Matrix ι ι ℚ_[p])
    ((↑) : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule → Matrix ι ι ℚ_[p])

private def skewAdjointPadicIntegralCoordinateEmbedding
    (F : Matrix ι ι ℚ) (p : ℕ) [Fact (Nat.Prime p)] :
    (Fin (Module.finrank ℚ (skewAdjointMatricesLieSubalgebra F)) → ℤ_[p]) →+
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  (skewAdjointPadicCoordinateEquiv F p).symm.toLinearMap.toAddMonoidHom.comp
    (padicIntCoordinateCoe p _)

private theorem skewAdjointPadicIntegralCoordinateEmbedding_isOpenEmbedding
    (F : Matrix ι ι ℚ) (p : ℕ) [Fact (Nat.Prime p)] :
    IsOpenEmbedding (skewAdjointPadicIntegralCoordinateEmbedding F p) := by
  exact (skewAdjointPadicCoordinateEquiv F p).symm.toHomeomorph.isOpenEmbedding.comp
    (padicIntCoordinateCoe_isOpenEmbedding p _)

private theorem skewAdjointPadicIntegralCoordinateEmbedding_range
    (F : Matrix ι ι ℚ) (p : ℕ) [Fact (Nat.Prime p)] :
    Set.range (skewAdjointPadicIntegralCoordinateEmbedding F p) =
      (skewAdjointPadicCoordinateLattice F p :
        Set (skewAdjointMatricesLieSubalgebra
          (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule) := by
  apply Set.Subset.antisymm
  · rintro _ ⟨z, rfl⟩
    exact ⟨_, ⟨z, rfl⟩, rfl⟩
  · rintro _ ⟨q, ⟨z, rfl⟩, rfl⟩
    exact ⟨z, rfl⟩

private def skewAdjointPadicCoordinateLatticeMeasure
    (F : Matrix ι ι ℚ) (p : ℕ) [Fact (Nat.Prime p)] :
    Measure
      (Fin (Module.finrank ℚ (skewAdjointMatricesLieSubalgebra F)) → ℤ_[p]) :=
  Measure.comap (skewAdjointPadicIntegralCoordinateEmbedding F p)
    (skewAdjointPadicCoordinateMeasure F p)

private theorem skewAdjointPadicCoordinateLatticeMeasure_univ
    (F : Matrix ι ι ℚ) (p : ℕ) [Fact (Nat.Prime p)] :
    skewAdjointPadicCoordinateLatticeMeasure F p Set.univ = 1 := by
  rw [skewAdjointPadicCoordinateLatticeMeasure,
    (skewAdjointPadicIntegralCoordinateEmbedding_isOpenEmbedding F p).measurableEmbedding.comap_apply]
  rw [Set.image_univ, skewAdjointPadicIntegralCoordinateEmbedding_range,
    skewAdjointPadicCoordinateMeasure_lattice]

local instance skewAdjointPadicCoordinateLatticeMeasure_isAddLeftInvariant
    (F : Matrix ι ι ℚ) (p : ℕ) [Fact (Nat.Prime p)] :
    Measure.IsAddLeftInvariant
      (skewAdjointPadicCoordinateLatticeMeasure F p) := by
  letI : Measure.IsAddHaarMeasure
      (skewAdjointPadicCoordinateMeasure F p) :=
    skewAdjointPadicCoordinateMeasure_isAddHaarMeasure F p
  exact Measure.IsAddLeftInvariant.comap
    (G :=
      Fin (Module.finrank ℚ (skewAdjointMatricesLieSubalgebra F)) → ℤ_[p])
    (H := (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule)
    (skewAdjointPadicCoordinateMeasure F p)
    (skewAdjointPadicIntegralCoordinateEmbedding_isOpenEmbedding F p).measurableEmbedding

private def padicCoordinateReduction (p k : ℕ) [Fact (Nat.Prime p)] (i : Fin d) :
    (Fin d → ℤ_[p]) →+ ZMod (p ^ k) :=
  (PadicInt.toZModPow k).toAddMonoidHom.comp
    (Pi.evalAddMonoidHom (fun _ : Fin d ↦ ℤ_[p]) i)

private theorem padicCoordinateReduction_surjective
    (p k : ℕ) [Fact (Nat.Prime p)] (i : Fin d) :
    Function.Surjective (padicCoordinateReduction p k i) := by
  intro a
  obtain ⟨z, hz⟩ := ZMod.ringHom_surjective (PadicInt.toZModPow k) a
  refine ⟨Function.update 0 i z, ?_⟩
  simpa [padicCoordinateReduction] using hz

private theorem padicCoordinateReduction_range_card
    (p k : ℕ) [Fact (Nat.Prime p)] (i : Fin d) :
    Nat.card (padicCoordinateReduction p k i).range = p ^ k := by
  rw [show (padicCoordinateReduction p k i).range = ⊤ by
    exact AddMonoidHom.range_eq_top.mpr
      (padicCoordinateReduction_surjective p k i)]
  simp

private theorem isOpen_padicCoordinateReduction_ker
    (p k : ℕ) [Fact (Nat.Prime p)] (i : Fin d) :
    IsOpen ((padicCoordinateReduction p k i).ker : Set (Fin d → ℤ_[p])) := by
  change IsOpen {z : Fin d → ℤ_[p] |
    PadicInt.toZModPow k (z i) = 0}
  rw [show {z : Fin d → ℤ_[p] | PadicInt.toZModPow k (z i) = 0} =
      (fun z : Fin d → ℤ_[p] ↦ z i) ⁻¹'
        (Ideal.span {(p : ℤ_[p]) ^ k} : Set ℤ_[p]) by
    ext z
    simp [← PadicInt.ker_toZModPow k]]
  have hball :
      (Ideal.span {(p : ℤ_[p]) ^ k} : Set ℤ_[p]) =
        Metric.closedBall 0 ((p : ℝ) ^ (-k : ℤ)) := by
    ext z
    simpa [Metric.mem_closedBall, dist_zero_right] using
      (PadicInt.norm_le_pow_iff_mem_span_pow z k).symm
  rw [hball]
  exact (IsUltrametricDist.isOpen_closedBall
      (x := (0 : ℤ_[p])) (r := (p : ℝ) ^ (-k : ℤ))
      (zpow_ne_zero _ (by exact_mod_cast (Fact.out : Nat.Prime p).ne_zero))).preimage
    (continuous_apply i)

private theorem skewAdjointPadicCoordinateLatticeMeasure_reduction_ker
    (F : Matrix ι ι ℚ) (p k : ℕ) [Fact (Nat.Prime p)]
    (i : Fin (Module.finrank ℚ (skewAdjointMatricesLieSubalgebra F))) :
    skewAdjointPadicCoordinateLatticeMeasure F p
        ((padicCoordinateReduction p k i).ker : Set _) =
      (p ^ k : ℝ≥0∞)⁻¹ := by
  letI : (padicCoordinateReduction p k i).ker.FiniteIndex := inferInstance
  have hindex := AddSubgroup.index_mul_measure
    (padicCoordinateReduction p k i).ker
    (isOpen_padicCoordinateReduction_ker p k i).measurableSet
    (skewAdjointPadicCoordinateLatticeMeasure F p)
  rw [skewAdjointPadicCoordinateLatticeMeasure_univ,
    AddSubgroup.index_ker, padicCoordinateReduction_range_card] at hindex
  exact ENNReal.eq_inv_of_mul_eq_one_left (by simpa [mul_comm] using hindex)

private def padicIntPowerCoordinateDilation
    (p k : ℕ) [Fact (Nat.Prime p)] (i : Fin d) :
    (Fin d → ℤ_[p]) →+ (Fin d → ℤ_[p]) where
  toFun z j := if j = i then (p : ℤ_[p]) ^ k * z j else z j
  map_zero' := by
    funext j
    simp
  map_add' x y := by
    funext j
    by_cases h : j = i
    · simp [h, mul_add]
    · simp [h]

private theorem padicIntPowerCoordinateDilation_range_eq_reduction_ker
    (p k : ℕ) [Fact (Nat.Prime p)] (i : Fin d) :
    (padicIntPowerCoordinateDilation p k i).range =
      (padicCoordinateReduction p k i).ker := by
  ext z
  constructor
  · rintro ⟨w, rfl⟩
    have hpzero : PadicInt.toZModPow k ((p : ℤ_[p]) ^ k) = 0 := by
      rw [← RingHom.mem_ker, PadicInt.ker_toZModPow]
      exact Ideal.subset_span (Set.mem_singleton _)
    simp [padicIntPowerCoordinateDilation, padicCoordinateReduction, hpzero]
  · intro hz
    change PadicInt.toZModPow k (z i) = 0 at hz
    have hzmem :
        z i ∈ (Ideal.span {(p : ℤ_[p]) ^ k} : Ideal ℤ_[p]) := by
      rw [← PadicInt.ker_toZModPow k]
      exact hz
    rw [Ideal.mem_span_singleton] at hzmem
    obtain ⟨c, hc⟩ := hzmem
    refine ⟨fun j => if j = i then c else z j, ?_⟩
    funext j
    by_cases h : j = i
    · subst j
      simpa [padicIntPowerCoordinateDilation, mul_comm] using hc.symm
    · simp [padicIntPowerCoordinateDilation, h]

def skewAdjointPadicPowerCoordinateDilation
    (F : Matrix ι ι ℚ) (p k : ℕ) [Fact (Nat.Prime p)]
    (i : Fin (Module.finrank ℚ (skewAdjointMatricesLieSubalgebra F))) :
    (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule ≃L[ℚ_[p]]
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  ((skewAdjointPadicCoordinateEquiv F p).trans
    (padicPowerCoordinateDilation p k i)).trans
      (skewAdjointPadicCoordinateEquiv F p).symm

theorem skewAdjointPadicPowerCoordinateDilation_det_norm
    (F : Matrix ι ι ℚ) (p k : ℕ) [Fact (Nat.Prime p)]
    (i : Fin (Module.finrank ℚ (skewAdjointMatricesLieSubalgebra F))) :
    ‖LinearMap.det
      (skewAdjointPadicPowerCoordinateDilation F p k i).toLinearMap‖ =
        (p : ℝ) ^ (-k : ℤ) := by
  have hdet :
      LinearEquiv.det
          (skewAdjointPadicPowerCoordinateDilation F p k i).toLinearEquiv =
        LinearEquiv.det (padicPowerCoordinateDilation p k i).toLinearEquiv := by
    unfold skewAdjointPadicPowerCoordinateDilation
    exact LinearEquiv.det_conj _
      (skewAdjointPadicCoordinateEquiv F p).symm.toLinearEquiv
  have hval := congrArg (fun z : ℚ_[p]ˣ ↦ (z : ℚ_[p])) hdet
  have hval' :
      LinearMap.det
          (skewAdjointPadicPowerCoordinateDilation F p k i).toLinearMap =
        LinearMap.det (padicPowerCoordinateDilation p k i).toLinearMap := by
    simpa only [LinearEquiv.coe_det] using hval
  rw [hval']
  exact padicPowerCoordinateDilation_det_norm p k i

theorem skewAdjointPadicPowerCoordinateDilation_inv_nnnorm_det
    (F : Matrix ι ι ℚ) (p k : ℕ) [Fact (Nat.Prime p)]
    (i : Fin (Module.finrank ℚ (skewAdjointMatricesLieSubalgebra F))) :
    ‖LinearMap.det
      (skewAdjointPadicPowerCoordinateDilation F p k i).toLinearMap‖₊⁻¹ =
        (p ^ k : ℝ≥0) := by
  apply NNReal.eq
  rw [NNReal.coe_inv, coe_nnnorm,
    skewAdjointPadicPowerCoordinateDilation_det_norm]
  simp [zpow_neg, zpow_natCast]

private theorem skewAdjointPadicPowerCoordinateDilation_comp_integralEmbedding
    (F : Matrix ι ι ℚ) (p k : ℕ) [Fact (Nat.Prime p)]
    (i : Fin (Module.finrank ℚ (skewAdjointMatricesLieSubalgebra F)))
    (z : Fin (Module.finrank ℚ (skewAdjointMatricesLieSubalgebra F)) → ℤ_[p]) :
    skewAdjointPadicPowerCoordinateDilation F p k i
        (skewAdjointPadicIntegralCoordinateEmbedding F p z) =
      skewAdjointPadicIntegralCoordinateEmbedding F p
        (padicIntPowerCoordinateDilation p k i z) := by
  apply (skewAdjointPadicCoordinateEquiv F p).injective
  funext j
  by_cases h : j = i
  · subst j
    simp [skewAdjointPadicPowerCoordinateDilation,
      skewAdjointPadicIntegralCoordinateEmbedding,
      padicIntCoordinateCoe,
      padicPowerCoordinateDilation_apply,
      padicIntPowerCoordinateDilation]
  · simp [skewAdjointPadicPowerCoordinateDilation,
      skewAdjointPadicIntegralCoordinateEmbedding,
      padicIntCoordinateCoe,
      padicPowerCoordinateDilation_apply,
      padicIntPowerCoordinateDilation, h]

private theorem skewAdjointPadicPowerCoordinateDilation_image_lattice
    (F : Matrix ι ι ℚ) (p k : ℕ) [Fact (Nat.Prime p)]
    (i : Fin (Module.finrank ℚ (skewAdjointMatricesLieSubalgebra F))) :
    skewAdjointPadicPowerCoordinateDilation F p k i ''
        (skewAdjointPadicCoordinateLattice F p :
          Set (skewAdjointMatricesLieSubalgebra
            (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule) =
      skewAdjointPadicIntegralCoordinateEmbedding F p ''
        ((padicCoordinateReduction p k i).ker : Set _) := by
  rw [← skewAdjointPadicIntegralCoordinateEmbedding_range,
    ← padicIntPowerCoordinateDilation_range_eq_reduction_ker]
  ext x
  constructor
  · rintro ⟨_, ⟨z, rfl⟩, rfl⟩
    exact ⟨padicIntPowerCoordinateDilation p k i z,
      ⟨z, rfl⟩,
      (skewAdjointPadicPowerCoordinateDilation_comp_integralEmbedding
        F p k i z).symm⟩
  · rintro ⟨_, ⟨z, rfl⟩, rfl⟩
    exact ⟨skewAdjointPadicIntegralCoordinateEmbedding F p z,
      ⟨z, rfl⟩,
      skewAdjointPadicPowerCoordinateDilation_comp_integralEmbedding F p k i z⟩

theorem skewAdjointPadicCoordinateMeasure_powerDilation_image_lattice
    (F : Matrix ι ι ℚ) (p k : ℕ) [Fact (Nat.Prime p)]
    (i : Fin (Module.finrank ℚ (skewAdjointMatricesLieSubalgebra F))) :
    skewAdjointPadicCoordinateMeasure F p
        (skewAdjointPadicPowerCoordinateDilation F p k i ''
          (skewAdjointPadicCoordinateLattice F p :
            Set (skewAdjointMatricesLieSubalgebra
              (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule)) =
      (p ^ k : ℝ≥0∞)⁻¹ := by
  rw [skewAdjointPadicPowerCoordinateDilation_image_lattice]
  rw [← (skewAdjointPadicIntegralCoordinateEmbedding_isOpenEmbedding F p).measurableEmbedding.comap_apply]
  exact skewAdjointPadicCoordinateLatticeMeasure_reduction_ker F p k i

theorem map_skewAdjointPadicCoordinateMeasure_powerCoordinateDilation
    (F : Matrix ι ι ℚ) (p k : ℕ) [Fact (Nat.Prime p)]
    (i : Fin (Module.finrank ℚ (skewAdjointMatricesLieSubalgebra F))) :
    Measure.map (skewAdjointPadicPowerCoordinateDilation F p k i)
        (skewAdjointPadicCoordinateMeasure F p) =
      (p ^ k : ℝ≥0) • skewAdjointPadicCoordinateMeasure F p := by
  let μ := skewAdjointPadicCoordinateMeasure F p
  let C := skewAdjointPadicCoordinateLattice F p
  let e := skewAdjointPadicPowerCoordinateDilation F p k i
  let D : TopologicalSpace.PositiveCompacts
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
    C.map e e.continuous e.isOpenMap
  have hp0 : (p : ℝ≥0) ≠ 0 := by
    exact_mod_cast (Fact.out : Nat.Prime p).ne_zero
  have hpk0 : (p ^ k : ℝ≥0) ≠ 0 := pow_ne_zero k hp0
  letI : Measure.IsAddHaarMeasure μ :=
    skewAdjointPadicCoordinateMeasure_isAddHaarMeasure F p
  letI : Measure.IsAddHaarMeasure (Measure.map e μ) :=
    e.isAddHaarMeasure_map μ
  letI : Measure.IsAddHaarMeasure ((p ^ k : ℝ≥0) • μ) :=
    Measure.IsAddHaarMeasure.nnreal_smul μ hpk0
  letI : SigmaFinite μ := by
    dsimp [μ]
    unfold skewAdjointPadicCoordinateMeasure
    infer_instance
  letI : SigmaFinite (Measure.map e μ) :=
    e.toHomeomorph.toMeasurableEquiv.sigmaFinite_map
  have hmap : Measure.addHaarMeasure D = Measure.map e μ := by
    apply (Measure.addHaarMeasure_eq_iff D (Measure.map e μ)).2
    change Measure.map e μ (e '' (C : Set _)) = 1
    rw [Measure.map_apply e.continuous.measurable
      ((C.isCompact.image e.continuous).measurableSet)]
    have hpre : e ⁻¹' (e '' (C : Set _)) = (C : Set _) :=
      Set.preimage_image_eq _ e.injective
    rw [hpre]
    exact skewAdjointPadicCoordinateMeasure_lattice F p
  have hsmul :
      Measure.addHaarMeasure D = (p ^ k : ℝ≥0) • μ := by
    apply (Measure.addHaarMeasure_eq_iff D ((p ^ k : ℝ≥0) • μ)).2
    change ((p ^ k : ℝ≥0) • μ) (e '' (C : Set _)) = 1
    rw [Measure.smul_apply]
    change (p ^ k : ℝ≥0∞) *
      skewAdjointPadicCoordinateMeasure F p
        (skewAdjointPadicPowerCoordinateDilation F p k i ''
          (skewAdjointPadicCoordinateLattice F p : Set _)) = 1
    rw [skewAdjointPadicCoordinateMeasure_powerDilation_image_lattice]
    exact ENNReal.mul_inv_cancel
      (by exact_mod_cast hpk0)
      (by simp)
  exact hmap.symm.trans hsmul

theorem map_skewAdjointPadicCoordinateMeasure_powerCoordinateDilation_det
    (F : Matrix ι ι ℚ) (p k : ℕ) [Fact (Nat.Prime p)]
    (i : Fin (Module.finrank ℚ (skewAdjointMatricesLieSubalgebra F))) :
    Measure.map (skewAdjointPadicPowerCoordinateDilation F p k i)
        (skewAdjointPadicCoordinateMeasure F p) =
      ‖LinearMap.det
        (skewAdjointPadicPowerCoordinateDilation F p k i).toLinearMap‖₊⁻¹ •
        skewAdjointPadicCoordinateMeasure F p := by
  rw [skewAdjointPadicPowerCoordinateDilation_inv_nnnorm_det]
  exact map_skewAdjointPadicCoordinateMeasure_powerCoordinateDilation F p k i

theorem map_skewAdjointPadicCoordinateMeasure_powerCoordinateDilation_symm
    (F : Matrix ι ι ℚ) (p k : ℕ) [Fact (Nat.Prime p)]
    (i : Fin (Module.finrank ℚ (skewAdjointMatricesLieSubalgebra F))) :
    Measure.map
        (skewAdjointPadicPowerCoordinateDilation F p k i).symm
        (skewAdjointPadicCoordinateMeasure F p) =
      (p ^ k : ℝ≥0)⁻¹ • skewAdjointPadicCoordinateMeasure F p := by
  let e := skewAdjointPadicPowerCoordinateDilation F p k i
  let μ := skewAdjointPadicCoordinateMeasure F p
  have hp0 : (p : ℝ≥0) ≠ 0 := by
    exact_mod_cast (Fact.out : Nat.Prime p).ne_zero
  have hpk0 : (p ^ k : ℝ≥0) ≠ 0 := pow_ne_zero k hp0
  apply e.toHomeomorph.measurableEmbedding.map_injective
  change Measure.map e (Measure.map e.symm μ) =
    Measure.map e ((p ^ k : ℝ≥0)⁻¹ • μ)
  have hcancel : Measure.map e (Measure.map e.symm μ) = μ := by
    exact MeasurableEquiv.map_map_symm e.toHomeomorph.toMeasurableEquiv
  rw [hcancel, Measure.map_smul,
    map_skewAdjointPadicCoordinateMeasure_powerCoordinateDilation]
  simp [hpk0]
  rfl

private theorem skewAdjointPadicPowerCoordinateDilation_symm_det_norm
    (F : Matrix ι ι ℚ) (p k : ℕ) [Fact (Nat.Prime p)]
    (i : Fin (Module.finrank ℚ (skewAdjointMatricesLieSubalgebra F))) :
    ‖LinearMap.det
      (skewAdjointPadicPowerCoordinateDilation F p k i).symm.toLinearMap‖ =
      (p : ℝ) ^ k := by
  rw [show
      (skewAdjointPadicPowerCoordinateDilation F p k i).symm.toLinearMap =
        (skewAdjointPadicPowerCoordinateDilation F p k i).toLinearEquiv.symm.toLinearMap
    by rfl]
  rw [LinearEquiv.det_coe_symm, norm_inv,
    skewAdjointPadicPowerCoordinateDilation_det_norm]
  simp [zpow_neg, zpow_natCast]

/-- Multiplication of one transported coordinate by the signed power `p^z`. -/
def skewAdjointPadicSignedPowerCoordinateDilation
    (F : Matrix ι ι ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (i : Fin (Module.finrank ℚ (skewAdjointMatricesLieSubalgebra F))) :
    ℤ →
      (skewAdjointMatricesLieSubalgebra
          (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule ≃L[ℚ_[p]]
        (skewAdjointMatricesLieSubalgebra
          (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule
  | Int.ofNat k => skewAdjointPadicPowerCoordinateDilation F p k i
  | Int.negSucc k =>
      (skewAdjointPadicPowerCoordinateDilation F p (k + 1) i).symm

set_option maxRecDepth 2048 in
theorem skewAdjointPadicSignedPowerCoordinateDilation_coordinate_apply
    (F : Matrix ι ι ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (i j : Fin (Module.finrank ℚ (skewAdjointMatricesLieSubalgebra F)))
    (z : ℤ)
    (x : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule) :
    skewAdjointPadicCoordinateEquiv F p
        (skewAdjointPadicSignedPowerCoordinateDilation F p i z x) j =
      (if j = i then (p : ℚ_[p]) ^ z *
        skewAdjointPadicCoordinateEquiv F p x j
      else skewAdjointPadicCoordinateEquiv F p x j) := by
  cases z with
  | ofNat k =>
      simp [skewAdjointPadicSignedPowerCoordinateDilation,
        skewAdjointPadicPowerCoordinateDilation,
        padicPowerCoordinateDilation_apply]
  | negSucc k =>
      let c := skewAdjointPadicCoordinateEquiv F p
      let y := skewAdjointPadicCoordinateEquiv F p x
      let e := padicPowerCoordinateDilation p (k + 1) i
      let s := ((c.trans e).trans c.symm)
      have hcoord : c (s.symm x) = e.symm (c x) := by
        apply e.injective
        simp [s, c, e]
      change c (s.symm x) j =
        if j = i then (p : ℚ_[p]) ^ Int.negSucc k * c x j else c x j
      rw [hcoord]
      change e.symm y j =
        if j = i then (p : ℚ_[p]) ^ Int.negSucc k * y j else y j
      by_cases hji : j = i
      · subst j
        rw [if_pos rfl, zpow_negSucc]
        have hforward := congrArg (fun q => q i) (e.apply_symm_apply y)
        change padicPowerCoordinateDilation p (k + 1) i (e.symm y) i =
          y i at hforward
        rw [padicPowerCoordinateDilation_apply] at hforward
        simp only [if_pos] at hforward
        rw [eq_inv_mul_iff_mul_eq₀ (pow_ne_zero _ (by
          exact_mod_cast (Fact.out : Nat.Prime p).ne_zero))]
        exact hforward
      · rw [if_neg hji]
        have hforward := congrArg (fun q => q j) (e.apply_symm_apply y)
        change padicPowerCoordinateDilation p (k + 1) i (e.symm y) j =
          y j at hforward
        rw [padicPowerCoordinateDilation_apply, if_neg hji] at hforward
        exact hforward

theorem skewAdjointPadicSignedPowerCoordinateDilation_det_norm
    (F : Matrix ι ι ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (i : Fin (Module.finrank ℚ (skewAdjointMatricesLieSubalgebra F)))
    (z : ℤ) :
    ‖LinearMap.det
      (skewAdjointPadicSignedPowerCoordinateDilation F p i z).toLinearMap‖ =
      (p : ℝ) ^ (-z) := by
  cases z with
  | ofNat k =>
      exact skewAdjointPadicPowerCoordinateDilation_det_norm F p k i
  | negSucc k =>
      simpa [skewAdjointPadicSignedPowerCoordinateDilation] using
        skewAdjointPadicPowerCoordinateDilation_symm_det_norm F p (k + 1) i

theorem skewAdjointPadicSignedPowerCoordinateDilation_inv_nnnorm_det
    (F : Matrix ι ι ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (i : Fin (Module.finrank ℚ (skewAdjointMatricesLieSubalgebra F)))
    (z : ℤ) :
    ‖LinearMap.det
      (skewAdjointPadicSignedPowerCoordinateDilation F p i z).toLinearMap‖₊⁻¹ =
      (p : ℝ≥0) ^ z := by
  apply NNReal.eq
  rw [NNReal.coe_inv, coe_nnnorm,
    skewAdjointPadicSignedPowerCoordinateDilation_det_norm]
  simp [zpow_neg]

theorem map_skewAdjointPadicCoordinateMeasure_signedPowerCoordinateDilation
    (F : Matrix ι ι ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (i : Fin (Module.finrank ℚ (skewAdjointMatricesLieSubalgebra F)))
    (z : ℤ) :
    Measure.map (skewAdjointPadicSignedPowerCoordinateDilation F p i z)
        (skewAdjointPadicCoordinateMeasure F p) =
      (p : ℝ≥0) ^ z • skewAdjointPadicCoordinateMeasure F p := by
  cases z with
  | ofNat k =>
      exact
        map_skewAdjointPadicCoordinateMeasure_powerCoordinateDilation
          F p k i
  | negSucc k =>
      rw [show (p : ℝ≥0) ^ Int.negSucc k =
        (p ^ (k + 1) : ℝ≥0)⁻¹ by simp [zpow_negSucc]]
      exact
        map_skewAdjointPadicCoordinateMeasure_powerCoordinateDilation_symm
          F p (k + 1) i

theorem map_skewAdjointPadicCoordinateMeasure_signedPowerCoordinateDilation_det
    (F : Matrix ι ι ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (i : Fin (Module.finrank ℚ (skewAdjointMatricesLieSubalgebra F)))
    (z : ℤ) :
    Measure.map (skewAdjointPadicSignedPowerCoordinateDilation F p i z)
        (skewAdjointPadicCoordinateMeasure F p) =
      ‖LinearMap.det
        (skewAdjointPadicSignedPowerCoordinateDilation F p i z).toLinearMap‖₊⁻¹ •
        skewAdjointPadicCoordinateMeasure F p := by
  rw [skewAdjointPadicSignedPowerCoordinateDilation_inv_nnnorm_det]
  exact
    map_skewAdjointPadicCoordinateMeasure_signedPowerCoordinateDilation
      F p i z

private def skewAdjointPadicSignedDiagonalDilationList
    (F : Matrix ι ι ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (z : Fin (Module.finrank ℚ (skewAdjointMatricesLieSubalgebra F)) → ℤ) :
    List (Fin (Module.finrank ℚ (skewAdjointMatricesLieSubalgebra F))) →
      (skewAdjointMatricesLieSubalgebra
          (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule ≃L[ℚ_[p]]
        (skewAdjointMatricesLieSubalgebra
          (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule
  | [] => ContinuousLinearEquiv.refl ℚ_[p] _
  | i :: l =>
      (skewAdjointPadicSignedDiagonalDilationList F p z l).trans
        (skewAdjointPadicSignedPowerCoordinateDilation F p i (z i))

/-- The finite diagonal coordinate change with entries `p ^ z i`, conjugated
to the transported p-adic skew-adjoint model. -/
def skewAdjointPadicSignedDiagonalDilation
    (F : Matrix ι ι ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (z : Fin (Module.finrank ℚ (skewAdjointMatricesLieSubalgebra F)) → ℤ) :
    (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule ≃L[ℚ_[p]]
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  skewAdjointPadicSignedDiagonalDilationList F p z
    (List.finRange (Module.finrank ℚ (skewAdjointMatricesLieSubalgebra F)))

private theorem skewAdjointPadicSignedDiagonalDilationList_coordinate_apply
    (F : Matrix ι ι ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (z : Fin (Module.finrank ℚ (skewAdjointMatricesLieSubalgebra F)) → ℤ)
    (l : List (Fin (Module.finrank ℚ
      (skewAdjointMatricesLieSubalgebra F))))
    (x : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule)
    (j : Fin (Module.finrank ℚ (skewAdjointMatricesLieSubalgebra F))) :
    skewAdjointPadicCoordinateEquiv F p
        (skewAdjointPadicSignedDiagonalDilationList F p z l x) j =
      ((l.map fun i => if j = i then (p : ℚ_[p]) ^ z i else 1).prod) *
        skewAdjointPadicCoordinateEquiv F p x j := by
  induction l with
  | nil => simp [skewAdjointPadicSignedDiagonalDilationList]
  | cons i l ih =>
      rw [skewAdjointPadicSignedDiagonalDilationList]
      change skewAdjointPadicCoordinateEquiv F p
          (skewAdjointPadicSignedPowerCoordinateDilation F p i (z i)
            (skewAdjointPadicSignedDiagonalDilationList F p z l x)) j = _
      rw [
        skewAdjointPadicSignedPowerCoordinateDilation_coordinate_apply, ih]
      by_cases hji : j = i
      · simp only [List.map_cons, List.prod_cons, if_pos hji]
        rw [mul_assoc]
      · simp only [List.map_cons, List.prod_cons, if_neg hji, one_mul]

theorem skewAdjointPadicSignedDiagonalDilation_coordinate_apply
    (F : Matrix ι ι ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (z : Fin (Module.finrank ℚ (skewAdjointMatricesLieSubalgebra F)) → ℤ)
    (x : (skewAdjointMatricesLieSubalgebra
      (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule)
    (j : Fin (Module.finrank ℚ (skewAdjointMatricesLieSubalgebra F))) :
    skewAdjointPadicCoordinateEquiv F p
        (skewAdjointPadicSignedDiagonalDilation F p z x) j =
      (p : ℚ_[p]) ^ z j * skewAdjointPadicCoordinateEquiv F p x j := by
  rw [skewAdjointPadicSignedDiagonalDilation,
    skewAdjointPadicSignedDiagonalDilationList_coordinate_apply,
    ← Fin.prod_univ_def, Finset.prod_eq_single j]
  · simp
  · intro i _ hij
    simp [Ne.symm hij]
  · simp

private theorem map_skewAdjointPadicCoordinateMeasure_signedDiagonalDilationList
    (F : Matrix ι ι ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (z : Fin (Module.finrank ℚ (skewAdjointMatricesLieSubalgebra F)) → ℤ)
    (l : List (Fin (Module.finrank ℚ
      (skewAdjointMatricesLieSubalgebra F)))) :
    Measure.map (skewAdjointPadicSignedDiagonalDilationList F p z l)
        (skewAdjointPadicCoordinateMeasure F p) =
      (p : ℝ≥0) ^ ((l.map z).sum) •
        skewAdjointPadicCoordinateMeasure F p := by
  induction l with
  | nil => simp [skewAdjointPadicSignedDiagonalDilationList]
  | cons a l ih =>
      change Measure.map
        ((skewAdjointPadicSignedPowerCoordinateDilation F p a (z a)) ∘
          skewAdjointPadicSignedDiagonalDilationList F p z l)
          (skewAdjointPadicCoordinateMeasure F p) = _
      rw [← Measure.map_map
        (skewAdjointPadicSignedPowerCoordinateDilation F p a (z a)).continuous.measurable
        (skewAdjointPadicSignedDiagonalDilationList F p z l).continuous.measurable]
      rw [ih, Measure.map_smul,
        map_skewAdjointPadicCoordinateMeasure_signedPowerCoordinateDilation,
        smul_smul]
      have hp0 : (p : ℝ≥0) ≠ 0 := by
        exact_mod_cast (Fact.out : Nat.Prime p).ne_zero
      rw [← zpow_add₀ hp0, add_comm]
      simp

theorem map_skewAdjointPadicCoordinateMeasure_signedDiagonalDilation
    (F : Matrix ι ι ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (z : Fin (Module.finrank ℚ (skewAdjointMatricesLieSubalgebra F)) → ℤ) :
    Measure.map (skewAdjointPadicSignedDiagonalDilation F p z)
        (skewAdjointPadicCoordinateMeasure F p) =
      (p : ℝ≥0) ^ (∑ i, z i) •
        skewAdjointPadicCoordinateMeasure F p := by
  simpa [skewAdjointPadicSignedDiagonalDilation] using
    map_skewAdjointPadicCoordinateMeasure_signedDiagonalDilationList
      F p z
      (List.finRange (Module.finrank ℚ
        (skewAdjointMatricesLieSubalgebra F)))

private theorem skewAdjointPadicSignedDiagonalDilationList_det_norm
    (F : Matrix ι ι ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (z : Fin (Module.finrank ℚ (skewAdjointMatricesLieSubalgebra F)) → ℤ)
    (l : List (Fin (Module.finrank ℚ
      (skewAdjointMatricesLieSubalgebra F)))) :
    ‖LinearMap.det
      (skewAdjointPadicSignedDiagonalDilationList F p z l).toLinearMap‖ =
      (p : ℝ) ^ (-((l.map z).sum)) := by
  induction l with
  | nil =>
      rw [show
        (skewAdjointPadicSignedDiagonalDilationList F p z []).toLinearMap =
          LinearMap.id
        by rfl]
      simp
  | cons a l ih =>
      change ‖LinearMap.det
        ((skewAdjointPadicSignedPowerCoordinateDilation F p a (z a)).toLinearMap.comp
          (skewAdjointPadicSignedDiagonalDilationList F p z l).toLinearMap)‖ = _
      rw [LinearMap.det_comp, norm_mul,
        skewAdjointPadicSignedPowerCoordinateDilation_det_norm, ih]
      have hp0 : (p : ℝ) ≠ 0 := by
        exact_mod_cast (Fact.out : Nat.Prime p).ne_zero
      simp only [List.map_cons, List.sum_cons]
      rw [neg_add, zpow_add₀ hp0]

theorem skewAdjointPadicSignedDiagonalDilation_det_norm
    (F : Matrix ι ι ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (z : Fin (Module.finrank ℚ (skewAdjointMatricesLieSubalgebra F)) → ℤ) :
    ‖LinearMap.det
      (skewAdjointPadicSignedDiagonalDilation F p z).toLinearMap‖ =
      (p : ℝ) ^ (-(∑ i, z i)) := by
  simpa [skewAdjointPadicSignedDiagonalDilation] using
    skewAdjointPadicSignedDiagonalDilationList_det_norm
      F p z
      (List.finRange (Module.finrank ℚ
        (skewAdjointMatricesLieSubalgebra F)))

theorem skewAdjointPadicSignedDiagonalDilation_inv_nnnorm_det
    (F : Matrix ι ι ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (z : Fin (Module.finrank ℚ (skewAdjointMatricesLieSubalgebra F)) → ℤ) :
    ‖LinearMap.det
      (skewAdjointPadicSignedDiagonalDilation F p z).toLinearMap‖₊⁻¹ =
      (p : ℝ≥0) ^ (∑ i, z i) := by
  apply NNReal.eq
  rw [NNReal.coe_inv, coe_nnnorm,
    skewAdjointPadicSignedDiagonalDilation_det_norm]
  simp [zpow_neg]

theorem map_skewAdjointPadicCoordinateMeasure_signedDiagonalDilation_det
    (F : Matrix ι ι ℚ) (p : ℕ) [Fact (Nat.Prime p)]
    (z : Fin (Module.finrank ℚ (skewAdjointMatricesLieSubalgebra F)) → ℤ) :
    Measure.map (skewAdjointPadicSignedDiagonalDilation F p z)
        (skewAdjointPadicCoordinateMeasure F p) =
      ‖LinearMap.det
        (skewAdjointPadicSignedDiagonalDilation F p z).toLinearMap‖₊⁻¹ •
        skewAdjointPadicCoordinateMeasure F p := by
  rw [skewAdjointPadicSignedDiagonalDilation_inv_nnnorm_det]
  exact map_skewAdjointPadicCoordinateMeasure_signedDiagonalDilation F p z

end Matrix
