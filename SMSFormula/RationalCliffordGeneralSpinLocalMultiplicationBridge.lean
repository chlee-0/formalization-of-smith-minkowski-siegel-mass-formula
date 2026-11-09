import SMSFormula.RationalCliffordGeneralSpinUnitSquareLocalChart
import SMSFormula.RationalCliffordSpinCandidateGeneralSpinEmbedding

/-!
# The local scalar-times-Spin multiplication bridge

The horizontal parameter charts live on
`Kˣ × Spin(K)`, whereas the common quotient measure lives on intrinsic
`GSpin(K)`.  This file connects the two carriers by the map

`(z, s) ↦ scalar(z) * ofSpin(s)`.

The combined map `(nu, pi)` transports this multiplication map to the product
chart `(z, s) ↦ (z², pi(s))`.  Consequently the multiplication map is
injective on the chosen identity product chart.  Every intrinsic point whose
combined image lies in the product-chart target belongs to one of the two
algebraic sheets obtained from that chart, with the second sheet given by
right multiplication by the nontrivial central-fiber point.

This is an algebraic and topological statement: no Haar scale or differential
normalization is assigned here.
-/

noncomputable section

open Topology

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

/-- Literal scalar-times-Spin multiplication into intrinsic `GSpin`. -/
def cliffordGeneralSpinCentralSpinMultiplication
    (K : Type*) [CommRing K] [Algebra ℚ K] :
    Kˣ × V.CliffordSpinCandidateGroup K →
      V.CliffordGeneralSpinIntrinsicPoint K :=
  fun x =>
    CliffordGeneralSpinIntrinsicPoint.scalarGroupHom V K x.1 *
      V.cliffordSpinCandidateToCliffordGeneralSpinHom K x.2

@[simp]
theorem cliffordGeneralSpinCentralSpinMultiplication_similitude
    (K : Type*) [CommRing K] [Algebra ℚ K]
    (x : Kˣ × V.CliffordSpinCandidateGroup K) :
    (V.cliffordGeneralSpinCentralSpinMultiplication K x).similitude =
      x.1 ^ 2 := by
  change CliffordGeneralSpinIntrinsicPoint.similitudeGroupHom V K
      (CliffordGeneralSpinIntrinsicPoint.scalarGroupHom V K x.1 *
        V.cliffordSpinCandidateToCliffordGeneralSpinHom K x.2) = _
  rw [map_mul,
    CliffordGeneralSpinIntrinsicPoint.similitudeGroupHom_comp_scalarGroupHom]
  change x.1 ^ 2 *
      (V.cliffordSpinCandidateToCliffordGeneralSpinHom K x.2).similitude = _
  rw [V.cliffordSpinCandidateToCliffordGeneralSpinHom_apply_similitude, mul_one]

@[simp]
theorem cliffordGeneralSpinCentralSpinMultiplication_matrixGroup
    (K : Type*) [CommRing K] [Algebra ℚ K]
    (x : Kˣ × V.CliffordSpinCandidateGroup K) :
    (V.cliffordGeneralSpinCentralSpinMultiplication K x).matrixGroup =
      V.cliffordSpinCandidateGroupToSpecialOrthogonal K x.2 := by
  change CliffordGeneralSpinIntrinsicPoint.toSpecialOrthogonalGroupHom V K
      (CliffordGeneralSpinIntrinsicPoint.scalarGroupHom V K x.1 *
        V.cliffordSpinCandidateToCliffordGeneralSpinHom K x.2) = _
  rw [map_mul]
  change (CliffordGeneralSpinIntrinsicPoint.ofScalar V K x.1).matrixGroup *
      (CliffordGeneralSpinIntrinsicPoint.ofSpin V K
        (V.cliffordSpinCandidateCoordinateAlgHomMulEquivPointData K x.2)).matrixGroup = _
  rw [CliffordGeneralSpinIntrinsicPoint.ofScalar_matrixGroup, one_mul]
  rfl

/-- The combined field map transports scalar-times-Spin multiplication to the
literal square/Spin product map. -/
@[simp]
theorem centralFiberGroupHom_cliffordGeneralSpinCentralSpinMultiplication
    (K : Type*) [Field K] [Algebra ℚ K]
    (x : Kˣ × V.CliffordSpinCandidateGroup K) :
    CliffordGeneralSpinIntrinsicPoint.centralFiberGroupHom V K
        (V.cliffordGeneralSpinCentralSpinMultiplication K x) =
      (x.1 ^ 2, V.cliffordSpinCandidateGroupToSpecialOrthogonal K x.2) := by
  apply Prod.ext
  · exact V.cliffordGeneralSpinCentralSpinMultiplication_similitude K x
  · exact V.cliffordGeneralSpinCentralSpinMultiplication_matrixGroup K x

/-- Scalar-times-Spin multiplication is continuous for the literal local
coordinate topologies. -/
theorem continuous_cliffordGeneralSpinCentralSpinMultiplication
    (K : Type*) [CommRing K] [Algebra ℚ K]
    [TopologicalSpace K] [IsTopologicalRing K] :
    Continuous (V.cliffordGeneralSpinCentralSpinMultiplication K) := by
  exact
    ((V.continuous_cliffordGeneralSpinScalarGroupHom K).comp continuous_fst).mul
      ((V.continuous_cliffordSpinCandidateToCliffordGeneralSpinHom K).comp
        continuous_snd)

/-- The combined field map is continuous. -/
theorem continuous_cliffordGeneralSpinCentralFiberGroupHom
    (K : Type*) [Field K] [Algebra ℚ K]
    [TopologicalSpace K] [IsTopologicalRing K] :
    Continuous
      (CliffordGeneralSpinIntrinsicPoint.centralFiberGroupHom V K) := by
  exact
    (V.continuous_cliffordGeneralSpinSimilitudeGroupHom K).prodMk
      (V.continuous_cliffordGeneralSpinToSpecialOrthogonalGroupHom K)

/-- The residual central-fiber element obtained by normalizing a point through
the product chart.  On the preimage of the chart target this takes only the
values `1` and the nontrivial central-fiber point. -/
def cliffordGeneralSpinCentralSpinSheetDefect
    (K : Type*) [Field K] [Algebra ℚ K] [TopologicalSpace K]
    (e : OpenPartialHomeomorph
      (Kˣ × V.CliffordSpinCandidateGroup K)
      (Kˣ × V.specialOrthogonalMatrixGroup K))
    (g : V.CliffordGeneralSpinIntrinsicPoint K) :
    V.CliffordGeneralSpinIntrinsicPoint K :=
  (V.cliffordGeneralSpinCentralSpinMultiplication K
      (e.symm (CliffordGeneralSpinIntrinsicPoint.centralFiberGroupHom V K g)))⁻¹ * g

/-- The sheet-defect map is continuous on the preimage of the product-chart
target. -/
theorem continuousOn_cliffordGeneralSpinCentralSpinSheetDefect
    (K : Type*) [Field K] [Algebra ℚ K]
    [TopologicalSpace K] [IsTopologicalRing K]
    (e : OpenPartialHomeomorph
      (Kˣ × V.CliffordSpinCandidateGroup K)
      (Kˣ × V.specialOrthogonalMatrixGroup K)) :
    ContinuousOn (V.cliffordGeneralSpinCentralSpinSheetDefect K e)
      ((CliffordGeneralSpinIntrinsicPoint.centralFiberGroupHom V K) ⁻¹'
        e.target) := by
  have hparameter : ContinuousOn
      (fun g : V.CliffordGeneralSpinIntrinsicPoint K =>
        e.symm (CliffordGeneralSpinIntrinsicPoint.centralFiberGroupHom V K g))
      ((CliffordGeneralSpinIntrinsicPoint.centralFiberGroupHom V K) ⁻¹'
        e.target) :=
    e.symm.continuousOn.comp
      (V.continuous_cliffordGeneralSpinCentralFiberGroupHom K).continuousOn
      (fun _ hg => hg)
  have hmultiplication : ContinuousOn
      (fun g : V.CliffordGeneralSpinIntrinsicPoint K =>
        V.cliffordGeneralSpinCentralSpinMultiplication K
          (e.symm (CliffordGeneralSpinIntrinsicPoint.centralFiberGroupHom V K g)))
      ((CliffordGeneralSpinIntrinsicPoint.centralFiberGroupHom V K) ⁻¹'
        e.target) :=
    (V.continuous_cliffordGeneralSpinCentralSpinMultiplication K).comp_continuousOn
      hparameter
  exact hmultiplication.inv.mul continuous_id.continuousOn

set_option synthInstance.maxHeartbeats 100000 in
/-- Over the product-chart target the sheet defect is one of the two literal
central-fiber points. -/
theorem cliffordGeneralSpinCentralSpinSheetDefect_eq_one_or_negOne
    (K : Type*) [Field K] [Algebra ℚ K] [TopologicalSpace K]
    (e : OpenPartialHomeomorph
      (Kˣ × V.CliffordSpinCandidateGroup K)
      (Kˣ × V.specialOrthogonalMatrixGroup K))
    (he : ∀ x,
      e x = CliffordGeneralSpinIntrinsicPoint.centralFiberGroupHom V K
        (V.cliffordGeneralSpinCentralSpinMultiplication K x))
    (g : V.CliffordGeneralSpinIntrinsicPoint K)
    (hg : CliffordGeneralSpinIntrinsicPoint.centralFiberGroupHom V K g ∈
      e.target) :
    V.cliffordGeneralSpinCentralSpinSheetDefect K e g = 1 ∨
      V.cliffordGeneralSpinCentralSpinSheetDefect K e g =
        CliffordGeneralSpinIntrinsicPoint.centralFiberNegOnePoint V K := by
  apply
    CliffordGeneralSpinIntrinsicPoint.eq_one_or_centralFiberNegOnePoint_of_centralFiberGroupHom_eq_one
      V K
  rw [cliffordGeneralSpinCentralSpinSheetDefect, map_mul, map_inv, ← he,
    e.right_inv hg, inv_mul_cancel]

set_option synthInstance.maxHeartbeats 100000 in
/-- The first intrinsic sheet is exactly the open target-preimage part where
the sheet defect is not the nontrivial central-fiber point. -/
theorem image_cliffordGeneralSpinCentralSpinMultiplication_source_eq
    (K : Type*) [Field K] [Algebra ℚ K] [TopologicalSpace K]
    (e : OpenPartialHomeomorph
      (Kˣ × V.CliffordSpinCandidateGroup K)
      (Kˣ × V.specialOrthogonalMatrixGroup K))
    (he : ∀ x,
      e x = CliffordGeneralSpinIntrinsicPoint.centralFiberGroupHom V K
        (V.cliffordGeneralSpinCentralSpinMultiplication K x)) :
    V.cliffordGeneralSpinCentralSpinMultiplication K '' e.source =
      ((CliffordGeneralSpinIntrinsicPoint.centralFiberGroupHom V K) ⁻¹'
          e.target) ∩
        (V.cliffordGeneralSpinCentralSpinSheetDefect K e) ⁻¹'
          ({CliffordGeneralSpinIntrinsicPoint.centralFiberNegOnePoint V K} :
            Set (V.CliffordGeneralSpinIntrinsicPoint K))ᶜ := by
  ext g
  constructor
  · rintro ⟨x, hx, rfl⟩
    constructor
    · change CliffordGeneralSpinIntrinsicPoint.centralFiberGroupHom V K
          (V.cliffordGeneralSpinCentralSpinMultiplication K x) ∈ e.target
      rw [← he x]
      exact e.map_source hx
    · have hleft : e.symm
          (CliffordGeneralSpinIntrinsicPoint.centralFiberGroupHom V K
            (V.cliffordGeneralSpinCentralSpinMultiplication K x)) = x := by
        rw [← he x]
        exact e.left_inv hx
      change V.cliffordGeneralSpinCentralSpinSheetDefect K e
          (V.cliffordGeneralSpinCentralSpinMultiplication K x) ≠
        CliffordGeneralSpinIntrinsicPoint.centralFiberNegOnePoint V K
      rw [cliffordGeneralSpinCentralSpinSheetDefect, hleft, inv_mul_cancel]
      exact
        (CliffordGeneralSpinIntrinsicPoint.centralFiberNegOnePoint_ne_one V K).symm
  · rintro ⟨hgTarget, hgNotNeg⟩
    let x := e.symm
      (CliffordGeneralSpinIntrinsicPoint.centralFiberGroupHom V K g)
    have hx : x ∈ e.source := e.map_target hgTarget
    have hdefect : V.cliffordGeneralSpinCentralSpinSheetDefect K e g = 1 := by
      rcases V.cliffordGeneralSpinCentralSpinSheetDefect_eq_one_or_negOne
          K e he g hgTarget with hone | hneg
      · exact hone
      · exact False.elim (hgNotNeg hneg)
    refine ⟨x, hx, ?_⟩
    calc
      V.cliffordGeneralSpinCentralSpinMultiplication K x =
          V.cliffordGeneralSpinCentralSpinMultiplication K x *
            V.cliffordGeneralSpinCentralSpinSheetDefect K e g := by
              rw [hdefect, mul_one]
      _ = g := by
        rw [cliffordGeneralSpinCentralSpinSheetDefect]
        change V.cliffordGeneralSpinCentralSpinMultiplication K x *
            ((V.cliffordGeneralSpinCentralSpinMultiplication K x)⁻¹ * g) = g
        group

/-- The chosen scalar-times-Spin sheet is open in intrinsic `GSpin`. -/
theorem isOpen_image_cliffordGeneralSpinCentralSpinMultiplication_source
    (K : Type*) [Field K] [Algebra ℚ K]
    [TopologicalSpace K] [IsTopologicalRing K] [T2Space K]
    (e : OpenPartialHomeomorph
      (Kˣ × V.CliffordSpinCandidateGroup K)
      (Kˣ × V.specialOrthogonalMatrixGroup K))
    (he : ∀ x,
      e x = CliffordGeneralSpinIntrinsicPoint.centralFiberGroupHom V K
        (V.cliffordGeneralSpinCentralSpinMultiplication K x)) :
    IsOpen (V.cliffordGeneralSpinCentralSpinMultiplication K '' e.source) := by
  rw [V.image_cliffordGeneralSpinCentralSpinMultiplication_source_eq K e he]
  exact
    (V.continuousOn_cliffordGeneralSpinCentralSpinSheetDefect K e).isOpen_inter_preimage
      (e.open_target.preimage
        (V.continuous_cliffordGeneralSpinCentralFiberGroupHom K))
      isOpen_compl_singleton

/-- The intrinsic scalar-times-Spin chart induced by a compatible product
chart.  Its inverse is obtained by applying the combined map and then the
product-chart inverse. -/
noncomputable def cliffordGeneralSpinCentralSpinLocalChart
    (K : Type*) [Field K] [Algebra ℚ K]
    [TopologicalSpace K] [IsTopologicalRing K] [T2Space K]
    (e : OpenPartialHomeomorph
      (Kˣ × V.CliffordSpinCandidateGroup K)
      (Kˣ × V.specialOrthogonalMatrixGroup K))
    (he : ∀ x,
      e x = CliffordGeneralSpinIntrinsicPoint.centralFiberGroupHom V K
        (V.cliffordGeneralSpinCentralSpinMultiplication K x)) :
    OpenPartialHomeomorph
      (Kˣ × V.CliffordSpinCandidateGroup K)
      (V.CliffordGeneralSpinIntrinsicPoint K) where
  toFun := V.cliffordGeneralSpinCentralSpinMultiplication K
  invFun := fun g =>
    e.symm (CliffordGeneralSpinIntrinsicPoint.centralFiberGroupHom V K g)
  source := e.source
  target := V.cliffordGeneralSpinCentralSpinMultiplication K '' e.source
  map_source' x hx := ⟨x, hx, rfl⟩
  map_target' := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← he x]
    exact e.map_target (e.map_source hx)
  left_inv' x hx := by
    rw [← he x]
    exact e.left_inv hx
  right_inv' := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← he x, e.left_inv hx]
  open_source := e.open_source
  open_target :=
    V.isOpen_image_cliffordGeneralSpinCentralSpinMultiplication_source K e he
  continuousOn_toFun :=
    (V.continuous_cliffordGeneralSpinCentralSpinMultiplication K).continuousOn
  continuousOn_invFun := by
    apply e.symm.continuousOn.comp
      (V.continuous_cliffordGeneralSpinCentralFiberGroupHom K).continuousOn
    rintro _ ⟨x, hx, rfl⟩
    change CliffordGeneralSpinIntrinsicPoint.centralFiberGroupHom V K
        (V.cliffordGeneralSpinCentralSpinMultiplication K x) ∈ e.target
    rw [← he x]
    exact e.map_source hx

@[simp]
theorem cliffordGeneralSpinCentralSpinLocalChart_apply
    (K : Type*) [Field K] [Algebra ℚ K]
    [TopologicalSpace K] [IsTopologicalRing K] [T2Space K]
    (e : OpenPartialHomeomorph
      (Kˣ × V.CliffordSpinCandidateGroup K)
      (Kˣ × V.specialOrthogonalMatrixGroup K))
    (he : ∀ x,
      e x = CliffordGeneralSpinIntrinsicPoint.centralFiberGroupHom V K
        (V.cliffordGeneralSpinCentralSpinMultiplication K x))
    (x : Kˣ × V.CliffordSpinCandidateGroup K) :
    V.cliffordGeneralSpinCentralSpinLocalChart K e he x =
      V.cliffordGeneralSpinCentralSpinMultiplication K x :=
  rfl

/-- The intrinsic real identity chart obtained from the square/Spin product
chart. -/
noncomputable def realCliffordGeneralSpinCentralSpinIdentityChart :
    OpenPartialHomeomorph
      (ℝˣ × V.RealCliffordSpinCandidateGroup)
      (V.CliffordGeneralSpinIntrinsicPoint ℝ) :=
  V.cliffordGeneralSpinCentralSpinLocalChart ℝ
    V.realCliffordGeneralSpinHorizontalProductIdentityChart (by
      intro x
      exact (V.realCliffordGeneralSpinHorizontalProductIdentityChart_apply x).trans
        (V.centralFiberGroupHom_cliffordGeneralSpinCentralSpinMultiplication ℝ x).symm)

@[simp]
theorem realCliffordGeneralSpinCentralSpinIdentityChart_apply
    (x : ℝˣ × V.RealCliffordSpinCandidateGroup) :
    V.realCliffordGeneralSpinCentralSpinIdentityChart x =
      V.cliffordGeneralSpinCentralSpinMultiplication ℝ x :=
  rfl

/-- On the intrinsic real chart, the combined map is exactly the chosen
square/Spin product chart. -/
@[simp]
theorem centralFiberGroupHom_realCliffordGeneralSpinCentralSpinIdentityChart
    (x : ℝˣ × V.RealCliffordSpinCandidateGroup) :
    CliffordGeneralSpinIntrinsicPoint.centralFiberGroupHom V ℝ
        (V.realCliffordGeneralSpinCentralSpinIdentityChart x) =
      V.realCliffordGeneralSpinHorizontalProductIdentityChart x := by
  rw [V.realCliffordGeneralSpinCentralSpinIdentityChart_apply,
    V.realCliffordGeneralSpinHorizontalProductIdentityChart_apply,
    V.centralFiberGroupHom_cliffordGeneralSpinCentralSpinMultiplication,
    realCliffordSpinCandidateToSpecialOrthogonalHom]
  rfl

/-- The intrinsic p-adic identity chart obtained from the square/Spin product
chart. -/
noncomputable def padicCliffordGeneralSpinCentralSpinIdentityChart
    (p : ℕ) [Fact (Nat.Prime p)] :
    OpenPartialHomeomorph
      (ℚ_[p]ˣ × V.PadicCliffordSpinCandidateGroup p)
      (V.CliffordGeneralSpinIntrinsicPoint ℚ_[p]) :=
  V.cliffordGeneralSpinCentralSpinLocalChart ℚ_[p]
    (V.padicCliffordGeneralSpinHorizontalProductIdentityChart p) (by
      intro x
      rw [V.padicCliffordGeneralSpinHorizontalProductIdentityChart_apply]
      exact
        (V.centralFiberGroupHom_cliffordGeneralSpinCentralSpinMultiplication
          ℚ_[p] x).symm)

@[simp]
theorem padicCliffordGeneralSpinCentralSpinIdentityChart_apply
    (p : ℕ) [Fact (Nat.Prime p)]
    (x : ℚ_[p]ˣ × V.PadicCliffordSpinCandidateGroup p) :
    V.padicCliffordGeneralSpinCentralSpinIdentityChart p x =
      V.cliffordGeneralSpinCentralSpinMultiplication ℚ_[p] x :=
  rfl

/-- On the intrinsic p-adic chart, the combined map is exactly the chosen
square/Spin product chart. -/
@[simp]
theorem centralFiberGroupHom_padicCliffordGeneralSpinCentralSpinIdentityChart
    (p : ℕ) [Fact (Nat.Prime p)]
    (x : ℚ_[p]ˣ × V.PadicCliffordSpinCandidateGroup p) :
    CliffordGeneralSpinIntrinsicPoint.centralFiberGroupHom V ℚ_[p]
        (V.padicCliffordGeneralSpinCentralSpinIdentityChart p x) =
      V.padicCliffordGeneralSpinHorizontalProductIdentityChart p x := by
  rw [V.padicCliffordGeneralSpinCentralSpinIdentityChart_apply,
    V.padicCliffordGeneralSpinHorizontalProductIdentityChart_apply,
    V.centralFiberGroupHom_cliffordGeneralSpinCentralSpinMultiplication]

/-- On the chosen real product-chart source, scalar-times-Spin multiplication
is injective. -/
theorem real_cliffordGeneralSpinCentralSpinMultiplication_injOn :
    Set.InjOn (V.cliffordGeneralSpinCentralSpinMultiplication ℝ)
      V.realCliffordGeneralSpinHorizontalProductIdentityChart.source := by
  intro x hx y hy hxy
  apply V.realCliffordGeneralSpinHorizontalProductIdentityChart.injOn hx hy
  rw [V.realCliffordGeneralSpinHorizontalProductIdentityChart_apply,
    V.realCliffordGeneralSpinHorizontalProductIdentityChart_apply]
  simpa [realCliffordSpinCandidateToSpecialOrthogonalHom] using congrArg
    (CliffordGeneralSpinIntrinsicPoint.centralFiberGroupHom V ℝ) hxy

/-- On every chosen p-adic product-chart source, scalar-times-Spin
multiplication is injective. -/
theorem padic_cliffordGeneralSpinCentralSpinMultiplication_injOn
    (p : ℕ) [Fact (Nat.Prime p)] :
    Set.InjOn (V.cliffordGeneralSpinCentralSpinMultiplication ℚ_[p])
      (V.padicCliffordGeneralSpinHorizontalProductIdentityChart p).source := by
  intro x hx y hy hxy
  apply (V.padicCliffordGeneralSpinHorizontalProductIdentityChart p).injOn hx hy
  rw [V.padicCliffordGeneralSpinHorizontalProductIdentityChart_apply,
    V.padicCliffordGeneralSpinHorizontalProductIdentityChart_apply]
  simpa using congrArg
    (CliffordGeneralSpinIntrinsicPoint.centralFiberGroupHom V ℚ_[p]) hxy

set_option synthInstance.maxHeartbeats 100000 in
/-- Algebraic two-sheet completion over an arbitrary local product chart whose
underlying map is the combined map after scalar-times-Spin multiplication. -/
theorem exists_centralSpinParameter_or_parameter_mul_negOne_of_mem_target
    (K : Type*) [Field K] [Algebra ℚ K] [TopologicalSpace K]
    (e : OpenPartialHomeomorph
      (Kˣ × V.CliffordSpinCandidateGroup K)
      (Kˣ × V.specialOrthogonalMatrixGroup K))
    (he : ∀ x,
      e x = CliffordGeneralSpinIntrinsicPoint.centralFiberGroupHom V K
        (V.cliffordGeneralSpinCentralSpinMultiplication K x))
    (g : V.CliffordGeneralSpinIntrinsicPoint K)
    (hg : CliffordGeneralSpinIntrinsicPoint.centralFiberGroupHom V K g ∈
      e.target) :
    ∃ x ∈ e.source,
      g = V.cliffordGeneralSpinCentralSpinMultiplication K x ∨
      g = V.cliffordGeneralSpinCentralSpinMultiplication K x *
        CliffordGeneralSpinIntrinsicPoint.centralFiberNegOnePoint V K := by
  let x := e.symm
    (CliffordGeneralSpinIntrinsicPoint.centralFiberGroupHom V K g)
  have hx : x ∈ e.source := e.map_target hg
  have hcombined :
      CliffordGeneralSpinIntrinsicPoint.centralFiberGroupHom V K
          (V.cliffordGeneralSpinCentralSpinMultiplication K x) =
        CliffordGeneralSpinIntrinsicPoint.centralFiberGroupHom V K g := by
    rw [← he x]
    exact e.right_inv hg
  have hkernel :
      CliffordGeneralSpinIntrinsicPoint.centralFiberGroupHom V K
          ((V.cliffordGeneralSpinCentralSpinMultiplication K x)⁻¹ * g) = 1 := by
    rw [map_mul, map_inv, hcombined, inv_mul_cancel]
  rcases
      CliffordGeneralSpinIntrinsicPoint.eq_one_or_centralFiberNegOnePoint_of_centralFiberGroupHom_eq_one
        V K _ hkernel with hone | hneg
  · refine ⟨x, hx, Or.inl ?_⟩
    calc
      g = V.cliffordGeneralSpinCentralSpinMultiplication K x *
          ((V.cliffordGeneralSpinCentralSpinMultiplication K x)⁻¹ * g) := by
            group
      _ = V.cliffordGeneralSpinCentralSpinMultiplication K x := by rw [hone, mul_one]
  · refine ⟨x, hx, Or.inr ?_⟩
    calc
      g = V.cliffordGeneralSpinCentralSpinMultiplication K x *
          ((V.cliffordGeneralSpinCentralSpinMultiplication K x)⁻¹ * g) := by
            group
      _ = V.cliffordGeneralSpinCentralSpinMultiplication K x *
          CliffordGeneralSpinIntrinsicPoint.centralFiberNegOnePoint V K := by rw [hneg]

/-- Real specialization of the exact two-sheet completion over the product
chart target. -/
theorem exists_real_centralSpinParameter_or_parameter_mul_negOne_of_mem_target
    (g : V.CliffordGeneralSpinIntrinsicPoint ℝ)
    (hg : CliffordGeneralSpinIntrinsicPoint.centralFiberGroupHom V ℝ g ∈
      V.realCliffordGeneralSpinHorizontalProductIdentityChart.target) :
    ∃ x ∈ V.realCliffordGeneralSpinHorizontalProductIdentityChart.source,
      g = V.cliffordGeneralSpinCentralSpinMultiplication ℝ x ∨
      g = V.cliffordGeneralSpinCentralSpinMultiplication ℝ x *
        CliffordGeneralSpinIntrinsicPoint.centralFiberNegOnePoint V ℝ := by
  apply V.exists_centralSpinParameter_or_parameter_mul_negOne_of_mem_target ℝ
    V.realCliffordGeneralSpinHorizontalProductIdentityChart
  · intro x
    exact (V.realCliffordGeneralSpinHorizontalProductIdentityChart_apply x).trans
      (V.centralFiberGroupHom_cliffordGeneralSpinCentralSpinMultiplication ℝ x).symm
  · exact hg

/-- P-adic specialization of the exact two-sheet completion over the product
chart target. -/
theorem exists_padic_centralSpinParameter_or_parameter_mul_negOne_of_mem_target
    (p : ℕ) [Fact (Nat.Prime p)]
    (g : V.CliffordGeneralSpinIntrinsicPoint ℚ_[p])
    (hg : CliffordGeneralSpinIntrinsicPoint.centralFiberGroupHom V ℚ_[p] g ∈
      (V.padicCliffordGeneralSpinHorizontalProductIdentityChart p).target) :
    ∃ x ∈ (V.padicCliffordGeneralSpinHorizontalProductIdentityChart p).source,
      g = V.cliffordGeneralSpinCentralSpinMultiplication ℚ_[p] x ∨
      g = V.cliffordGeneralSpinCentralSpinMultiplication ℚ_[p] x *
        CliffordGeneralSpinIntrinsicPoint.centralFiberNegOnePoint V ℚ_[p] := by
  apply V.exists_centralSpinParameter_or_parameter_mul_negOne_of_mem_target ℚ_[p]
    (V.padicCliffordGeneralSpinHorizontalProductIdentityChart p)
  · intro x
    rw [V.padicCliffordGeneralSpinHorizontalProductIdentityChart_apply]
    exact
      (V.centralFiberGroupHom_cliffordGeneralSpinCentralSpinMultiplication ℚ_[p] x).symm
  · exact hg

end RationalQuadraticSpaceMatrix
