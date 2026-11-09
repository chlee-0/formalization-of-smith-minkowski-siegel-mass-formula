import SMSFormula.RationalCliffordSpinBlockIntrinsicStabilizer
import SMSFormula.RationalCliffordGeneralSpinPlacewiseHorizontalHaar
import SMSFormula.RationalCliffordGeneralSpinLocalCompactness
import Mathlib.Topology.Algebra.Group.OpenMapping

/-!
# Haar measure on the intrinsic GSpin complement stabilizer

The existing complement block homomorphism is continuous for the finite-coordinate
topologies on intrinsic general-Spin points.  At the real and p-adic places its
exact fixed-last-vector range is closed and locally compact, so the open-mapping
theorem upgrades the algebraic stabilizer equivalence to a homeomorphism.

The already normalized placewise horizontal differential Haar measures are then
pushed through this homeomorphism.  This is transport from lower-rank GSpin, not
restriction of higher-rank ambient Haar to a lower-dimensional subgroup.
-/

noncomputable section

open MeasureTheory Topology
open scoped ENNReal

namespace RationalQuadraticSpaceMatrix

set_option synthInstance.maxHeartbeats 300000

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

/-- The intrinsic general-Spin complement block map is continuous. -/
theorem continuous_nonisotropicLastComplementGeneralSpinPoint
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (A : Type*) [CommRing A] [Algebra ℚ A]
    [TopologicalSpace A] [IsTopologicalRing A] :
    Continuous (W.nonisotropicLastComplementGeneralSpinPoint a ha A) := by
  let E := W.nonisotropicLastExtension a ha
  apply continuous_induced_rng.mpr
  apply Continuous.prodMk
  · apply Continuous.prodMk
    · apply continuous_pi
      intro u
      rw [show (fun x : W.CliffordGeneralSpinIntrinsicPoint A =>
          (E.cliffordCoordinateBaseChangeBasis A).repr
            ((W.nonisotropicLastComplementGeneralSpinPoint a ha A x).cliffordUnit :
              E.cliffordCoordinateBaseChangeAlgebra A) u) =
          fun x => ∑ s,
            (W.cliffordCoordinateBaseChangeBasis A).repr
                (x.cliffordUnit : W.cliffordCoordinateBaseChangeAlgebra A) s *
              (E.cliffordCoordinateBaseChangeBasis A).repr
                (W.nonisotropicLastComplementCoordinateCliffordMap a ha A
                  (W.cliffordCoordinateBaseChangeBasis A s)) u by
        funext x
        change
          (E.cliffordCoordinateBaseChangeBasis A).repr
              (W.nonisotropicLastComplementCoordinateCliffordMap a ha A
                (x.cliffordUnit : W.cliffordCoordinateBaseChangeAlgebra A)) u = _
        conv_lhs =>
          rw [← (W.cliffordCoordinateBaseChangeBasis A).sum_repr
            (x.cliffordUnit : W.cliffordCoordinateBaseChangeAlgebra A)]
        simp only [map_sum, map_smul, Finsupp.coe_finset_sum,
          Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul]]
      apply continuous_finset_sum
      intro s _
      exact (W.continuous_cliffordGeneralSpinCliffordCoordinate A s).mul
        continuous_const
    · simpa using W.continuous_cliffordGeneralSpinSimilitude A
  · apply Continuous.prodMk
    · apply continuous_pi
      intro i
      apply continuous_pi
      intro j
      rw [show (fun x : W.CliffordGeneralSpinIntrinsicPoint A =>
          (W.nonisotropicLastComplementGeneralSpinPoint a ha A x).matrixPoint.1 i j) =
          fun x => (fixLastBlockMatrix x.matrixPoint.1) i j by
        funext x
        simp only [W.nonisotropicLastComplementGeneralSpinPoint_matrixPoint,
          W.nonisotropicLastComplementGeneralSpinMatrixPoint_coe]]
      cases i using Fin.lastCases with
      | last =>
          cases j using Fin.lastCases
          · simpa [fixLastBlockMatrix] using
              (continuous_const : Continuous
                (fun _ : W.CliffordGeneralSpinIntrinsicPoint A => (1 : A)))
          · simpa [fixLastBlockMatrix] using
              (continuous_const : Continuous
                (fun _ : W.CliffordGeneralSpinIntrinsicPoint A => (0 : A)))
      | cast i =>
          cases j using Fin.lastCases with
          | last =>
              simpa [fixLastBlockMatrix] using
                (continuous_const : Continuous
                  (fun _ : W.CliffordGeneralSpinIntrinsicPoint A => (0 : A)))
          | cast j =>
              simpa [fixLastBlockMatrix] using
                W.continuous_cliffordGeneralSpinMatrixCoordinate A i j
    · apply continuous_pi
      intro i
      apply continuous_pi
      intro j
      rw [show (fun x : W.CliffordGeneralSpinIntrinsicPoint A =>
          (W.nonisotropicLastComplementGeneralSpinPoint a ha A x).matrixGroup⁻¹.1.1.1 i j) =
          fun x => (fixLastBlockMatrix x.matrixGroup⁻¹.1.1.1) i j by
        funext x
        rw [W.nonisotropicLastComplementGeneralSpinPoint_matrixGroup]
        change
          ((W.nonisotropicLastCoordinateFiberEmbedHom a ha A x.matrixGroup)⁻¹).1.1.1 i j = _
        rw [← map_inv]
        change
          (W.nonisotropicLastCoordinateFiberEmbedGroup a ha A
            x.matrixGroup⁻¹).1.1.1 i j = _
        rw [W.coe_nonisotropicLastCoordinateFiberEmbedGroup]]
      cases i using Fin.lastCases with
      | last =>
          cases j using Fin.lastCases
          · simpa [fixLastBlockMatrix] using
              (continuous_const : Continuous
                (fun _ : W.CliffordGeneralSpinIntrinsicPoint A => (1 : A)))
          · simpa [fixLastBlockMatrix] using
              (continuous_const : Continuous
                (fun _ : W.CliffordGeneralSpinIntrinsicPoint A => (0 : A)))
      | cast i =>
          cases j using Fin.lastCases with
          | last =>
              simpa [fixLastBlockMatrix] using
                (continuous_const : Continuous
                  (fun _ : W.CliffordGeneralSpinIntrinsicPoint A => (0 : A)))
          | cast j =>
              simpa [fixLastBlockMatrix] using
                W.continuous_cliffordGeneralSpinInvMatrixCoordinate A i j

theorem continuous_nonisotropicLastComplementGeneralSpinStabilizerMulEquiv
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (A : Type*) [CommRing A] [Algebra ℚ A]
    [TopologicalSpace A] [IsTopologicalRing A] :
    Continuous
      (W.nonisotropicLastComplementGeneralSpinStabilizerMulEquiv a ha A) :=
  (W.continuous_nonisotropicLastComplementGeneralSpinPoint a ha A).subtype_mk _

/-- The literal fixed-last-vector intrinsic GSpin stabilizer is closed. -/
theorem isClosed_nonisotropicLastComplementGeneralSpinStabilizerSubgroup
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (A : Type*) [CommRing A] [Algebra ℚ A]
    [TopologicalSpace A] [IsTopologicalRing A] [T2Space A] :
    IsClosed
      (W.nonisotropicLastComplementGeneralSpinStabilizerSubgroup a ha A :
        Set ((W.nonisotropicLastExtension a ha).CliffordGeneralSpinIntrinsicPoint A)) := by
  rw [show
      (W.nonisotropicLastComplementGeneralSpinStabilizerSubgroup a ha A :
          Set ((W.nonisotropicLastExtension a ha).CliffordGeneralSpinIntrinsicPoint A)) =
        ⋂ j : Fin (n + 1),
          {z | z.matrixPoint.1 j (Fin.last n) =
            (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) A) j (Fin.last n)} by
    ext z
    simp only [Set.mem_iInter, Set.mem_setOf_eq]
    change z ∈ W.nonisotropicLastComplementGeneralSpinStabilizerSubgroup a ha A ↔ _
    rw [W.mem_nonisotropicLastComplementGeneralSpinStabilizerSubgroup_iff]
    unfold IsNonisotropicLastBlockGeneralSpinFixedPoint
    exact fixesLastCoordinate_iff_column z.matrixPoint.1]
  apply isClosed_iInter
  intro j
  exact isClosed_eq
    ((W.nonisotropicLastExtension a ha).continuous_cliffordGeneralSpinMatrixCoordinate
      A j (Fin.last n))
    continuous_const

/-- The inherited fixed-last-vector GSpin stabilizer topology is locally
compact whenever the ambient block GSpin topology is locally compact. -/
noncomputable instance nonisotropicLastComplementGeneralSpinStabilizerLocallyCompactSpace
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (A : Type*) [CommRing A] [Algebra ℚ A]
    [TopologicalSpace A] [IsTopologicalRing A] [T2Space A]
    [LocallyCompactSpace
      ((W.nonisotropicLastExtension a ha).CliffordGeneralSpinIntrinsicPoint A)] :
    LocallyCompactSpace
      (W.nonisotropicLastComplementGeneralSpinStabilizerSubgroup a ha A) :=
  (W.isClosed_nonisotropicLastComplementGeneralSpinStabilizerSubgroup a ha A)
    |>.isClosedEmbedding_subtypeVal.locallyCompactSpace

/-- The lower intrinsic GSpin group is continuously multiplicatively
equivalent to the inherited fixed-last-vector stabilizer. -/
noncomputable def nonisotropicLastComplementGeneralSpinStabilizerContinuousMulEquiv
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (A : Type*) [CommRing A] [Algebra ℚ A]
    [TopologicalSpace A] [IsTopologicalRing A] [T2Space A]
    [LocallyCompactSpace (W.CliffordGeneralSpinIntrinsicPoint A)]
    [LocallyCompactSpace
      ((W.nonisotropicLastExtension a ha).CliffordGeneralSpinIntrinsicPoint A)]
    [SigmaCompactSpace (W.CliffordGeneralSpinIntrinsicPoint A)] :
    W.CliffordGeneralSpinIntrinsicPoint A ≃ₜ*
      W.nonisotropicLastComplementGeneralSpinStabilizerSubgroup a ha A := by
  letI : LocallyCompactSpace
      (W.nonisotropicLastComplementGeneralSpinStabilizerSubgroup a ha A) :=
    W.nonisotropicLastComplementGeneralSpinStabilizerLocallyCompactSpace a ha A
  letI : T2Space
      (W.nonisotropicLastComplementGeneralSpinStabilizerSubgroup a ha A) :=
    (W.isClosed_nonisotropicLastComplementGeneralSpinStabilizerSubgroup a ha A)
      |>.isClosedEmbedding_subtypeVal.isEmbedding.t2Space
  letI : BaireSpace
      (W.nonisotropicLastComplementGeneralSpinStabilizerSubgroup a ha A) :=
    BaireSpace.of_t2Space_locallyCompactSpace
  let e := W.nonisotropicLastComplementGeneralSpinStabilizerMulEquiv a ha A
  have hcont : Continuous e :=
    W.continuous_nonisotropicLastComplementGeneralSpinStabilizerMulEquiv a ha A
  have hopen : IsOpenMap e :=
    e.toMonoidHom.isOpenMap_of_sigmaCompact e.surjective hcont
  exact ContinuousMulEquiv.mk'
    (e.toEquiv.toHomeomorphOfContinuousOpen hcont hopen) e.map_mul

theorem nonisotropicLastComplementGeneralSpinStabilizerContinuousMulEquiv_toMulEquiv
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (A : Type*) [CommRing A] [Algebra ℚ A]
    [TopologicalSpace A] [IsTopologicalRing A] [T2Space A]
    [LocallyCompactSpace (W.CliffordGeneralSpinIntrinsicPoint A)]
    [LocallyCompactSpace
      ((W.nonisotropicLastExtension a ha).CliffordGeneralSpinIntrinsicPoint A)]
    [SigmaCompactSpace (W.CliffordGeneralSpinIntrinsicPoint A)] :
    (W.nonisotropicLastComplementGeneralSpinStabilizerContinuousMulEquiv
      a ha A).toMulEquiv =
        W.nonisotropicLastComplementGeneralSpinStabilizerMulEquiv a ha A := by
  rfl

abbrev RealNonisotropicLastComplementGeneralSpinStabilizer
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :=
  W.nonisotropicLastComplementGeneralSpinStabilizerSubgroup a ha ℝ

abbrev PadicNonisotropicLastComplementGeneralSpinStabilizer
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (p : ℕ) [Fact (Nat.Prime p)] :=
  W.nonisotropicLastComplementGeneralSpinStabilizerSubgroup a ha ℚ_[p]

noncomputable local instance realGSpinBlockSourceLocallyCompact
    (W : RationalQuadraticSpaceMatrix n) :
    LocallyCompactSpace (W.CliffordGeneralSpinIntrinsicPoint ℝ) :=
  W.realCliffordGeneralSpinGroupLocallyCompactSpace

noncomputable local instance padicGSpinBlockSourceLocallyCompact
    (W : RationalQuadraticSpaceMatrix n) (p : ℕ) [Fact (Nat.Prime p)] :
    LocallyCompactSpace (W.CliffordGeneralSpinIntrinsicPoint ℚ_[p]) :=
  W.padicCliffordGeneralSpinGroupLocallyCompactSpace p

/-- Real specialization of the complement-stabilizer homeomorphism. -/
noncomputable def realNonisotropicLastComplementGeneralSpinStabilizerContinuousMulEquiv
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    W.CliffordGeneralSpinIntrinsicPoint ℝ ≃ₜ*
      W.RealNonisotropicLastComplementGeneralSpinStabilizer a ha :=
  W.nonisotropicLastComplementGeneralSpinStabilizerContinuousMulEquiv a ha ℝ

/-- P-adic specialization of the complement-stabilizer homeomorphism. -/
noncomputable def padicNonisotropicLastComplementGeneralSpinStabilizerContinuousMulEquiv
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (p : ℕ) [Fact (Nat.Prime p)] :
    W.CliffordGeneralSpinIntrinsicPoint ℚ_[p] ≃ₜ*
      W.PadicNonisotropicLastComplementGeneralSpinStabilizer a ha p :=
  W.nonisotropicLastComplementGeneralSpinStabilizerContinuousMulEquiv a ha ℚ_[p]

noncomputable instance realNonisotropicLastComplementGeneralSpinStabilizerMeasurableSpace
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    MeasurableSpace (W.RealNonisotropicLastComplementGeneralSpinStabilizer a ha) :=
  borel _

noncomputable instance realNonisotropicLastComplementGeneralSpinStabilizerBorelSpace
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    BorelSpace (W.RealNonisotropicLastComplementGeneralSpinStabilizer a ha) :=
  ⟨rfl⟩

noncomputable instance padicNonisotropicLastComplementGeneralSpinStabilizerMeasurableSpace
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (p : ℕ) [Fact (Nat.Prime p)] :
    MeasurableSpace (W.PadicNonisotropicLastComplementGeneralSpinStabilizer a ha p) :=
  borel _

noncomputable instance padicNonisotropicLastComplementGeneralSpinStabilizerBorelSpace
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (p : ℕ) [Fact (Nat.Prime p)] :
    BorelSpace (W.PadicNonisotropicLastComplementGeneralSpinStabilizer a ha p) :=
  ⟨rfl⟩

/-- The existing real horizontal differential Haar transported to the exact
GSpin complement stabilizer. -/
noncomputable def realNonisotropicLastComplementGeneralSpinStabilizerRawMeasure
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    Measure (W.RealNonisotropicLastComplementGeneralSpinStabilizer a ha) :=
  Measure.map
    (W.nonisotropicLastComplementGeneralSpinStabilizerMulEquiv a ha ℝ)
    W.realCliffordGeneralSpinHorizontalDifferentialHaarMeasure

/-- The existing p-adic horizontal differential Haar transported to the exact
GSpin complement stabilizer. -/
noncomputable def padicNonisotropicLastComplementGeneralSpinStabilizerRawMeasure
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (p : ℕ) [Fact (Nat.Prime p)] :
    Measure (W.PadicNonisotropicLastComplementGeneralSpinStabilizer a ha p) :=
  Measure.map
    (W.nonisotropicLastComplementGeneralSpinStabilizerMulEquiv a ha ℚ_[p])
    (W.padicCliffordGeneralSpinHorizontalDifferentialHaarMeasure p)

noncomputable instance realNonisotropicLastComplementGeneralSpinStabilizerRawMeasure_isHaarMeasure
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    Measure.IsHaarMeasure
      (W.realNonisotropicLastComplementGeneralSpinStabilizerRawMeasure a ha) := by
  letI : Measure.IsHaarMeasure
      W.realCliffordGeneralSpinHorizontalDifferentialHaarMeasure :=
    W.realCliffordGeneralSpinHorizontalDifferentialHaarMeasure_isHaarMeasure
  let e :=
    W.realNonisotropicLastComplementGeneralSpinStabilizerContinuousMulEquiv a ha
  change Measure.IsHaarMeasure
    (Measure.map e.toMulEquiv
      W.realCliffordGeneralSpinHorizontalDifferentialHaarMeasure)
  exact e.toMulEquiv.isHaarMeasure_map
    W.realCliffordGeneralSpinHorizontalDifferentialHaarMeasure
    e.continuous e.symm.continuous

noncomputable instance padicNonisotropicLastComplementGeneralSpinStabilizerRawMeasure_isHaarMeasure
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (p : ℕ) [Fact (Nat.Prime p)] :
    Measure.IsHaarMeasure
      (W.padicNonisotropicLastComplementGeneralSpinStabilizerRawMeasure a ha p) := by
  letI : Measure.IsHaarMeasure
      (W.padicCliffordGeneralSpinHorizontalDifferentialHaarMeasure p) :=
    W.padicCliffordGeneralSpinHorizontalDifferentialHaarMeasure_isHaarMeasure p
  let e :=
    W.padicNonisotropicLastComplementGeneralSpinStabilizerContinuousMulEquiv a ha p
  change Measure.IsHaarMeasure
    (Measure.map e.toMulEquiv
      (W.padicCliffordGeneralSpinHorizontalDifferentialHaarMeasure p))
  exact e.toMulEquiv.isHaarMeasure_map
    (W.padicCliffordGeneralSpinHorizontalDifferentialHaarMeasure p)
    e.continuous e.symm.continuous

noncomputable instance realNonisotropicLastComplementGeneralSpinStabilizerRawMeasure_isLocallyFinite
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0) :
    IsLocallyFiniteMeasure
      (W.realNonisotropicLastComplementGeneralSpinStabilizerRawMeasure a ha) := by
  infer_instance

noncomputable instance padicNonisotropicLastComplementGeneralSpinStabilizerRawMeasure_isLocallyFinite
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (p : ℕ) [Fact (Nat.Prime p)] :
    IsLocallyFiniteMeasure
      (W.padicNonisotropicLastComplementGeneralSpinStabilizerRawMeasure a ha p) := by
  infer_instance

/-- Integration against the real GSpin stabilizer raw measure is exactly
lower-rank horizontal differential integration through the block map. -/
theorem lintegral_realNonisotropicLastComplementGeneralSpinStabilizerRawMeasure
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (f : W.RealNonisotropicLastComplementGeneralSpinStabilizer a ha → ℝ≥0∞)
    (hf : Measurable f) :
    ∫⁻ z, f z ∂(W.realNonisotropicLastComplementGeneralSpinStabilizerRawMeasure a ha) =
      ∫⁻ x, f (W.nonisotropicLastComplementGeneralSpinStabilizerMulEquiv
        a ha ℝ x) ∂W.realCliffordGeneralSpinHorizontalDifferentialHaarMeasure := by
  have hmeas : Measurable
      (W.nonisotropicLastComplementGeneralSpinStabilizerMulEquiv a ha ℝ) :=
    W.continuous_nonisotropicLastComplementGeneralSpinStabilizerMulEquiv
      a ha ℝ |>.measurable
  rw [realNonisotropicLastComplementGeneralSpinStabilizerRawMeasure,
    lintegral_map hf hmeas]

/-- Integration against a p-adic GSpin stabilizer raw measure is exactly
lower-rank horizontal differential integration through the block map. -/
theorem lintegral_padicNonisotropicLastComplementGeneralSpinStabilizerRawMeasure
    (W : RationalQuadraticSpaceMatrix n) (a : ℚ) (ha : a ≠ 0)
    (p : ℕ) [Fact (Nat.Prime p)]
    (f : W.PadicNonisotropicLastComplementGeneralSpinStabilizer a ha p → ℝ≥0∞)
    (hf : Measurable f) :
    ∫⁻ z, f z ∂(W.padicNonisotropicLastComplementGeneralSpinStabilizerRawMeasure a ha p) =
      ∫⁻ x, f (W.nonisotropicLastComplementGeneralSpinStabilizerMulEquiv
        a ha ℚ_[p] x)
        ∂(W.padicCliffordGeneralSpinHorizontalDifferentialHaarMeasure p) := by
  have hmeas : Measurable
      (W.nonisotropicLastComplementGeneralSpinStabilizerMulEquiv a ha ℚ_[p]) :=
    W.continuous_nonisotropicLastComplementGeneralSpinStabilizerMulEquiv
      a ha ℚ_[p] |>.measurable
  rw [padicNonisotropicLastComplementGeneralSpinStabilizerRawMeasure,
    lintegral_map hf hmeas]

end RationalQuadraticSpaceMatrix
