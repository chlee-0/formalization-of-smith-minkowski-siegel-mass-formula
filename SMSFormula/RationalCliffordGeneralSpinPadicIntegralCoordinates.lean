import SMSFormula.RationalCliffordGeneralSpinLocalCompactness
import SMSFormula.RationalSpecialOrthogonalIntegralLocalFactorNormalization

/-!
# Compact-open integral coordinates in local intrinsic general Spin

At a p-adic place, require the Clifford unit, its inverse, the similitude and
its inverse, and the special-orthogonal matrix and its inverse to have
integral coordinates.  This literal locus is compact and open.  It is the
compact local reference set used by the restricted-product construction for
the crossed `GSpin` integral; no Haar normalization is chosen here.
-/

noncomputable section

open PositiveDefiniteIntegralLattice
open Set
open scoped Matrix

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

set_option synthInstance.maxHeartbeats 500000
set_option maxHeartbeats 1600000

/-! ## Integral unit and special-orthogonal factors -/

/-- P-adic units whose value and inverse value both lie in the p-adic
integer ring. -/
def padicIntegralUnitsSubgroup (p : ℕ) [Fact p.Prime] : Subgroup ℚ_[p]ˣ :=
  (PadicInt.subring p).toSubmonoid.units

@[simp]
theorem mem_padicIntegralUnitsSubgroup_iff
    (p : ℕ) [Fact p.Prime] (u : ℚ_[p]ˣ) :
    u ∈ padicIntegralUnitsSubgroup p ↔
      (u : ℚ_[p]) ∈ PadicInt.subring p ∧
        ((u⁻¹ : ℚ_[p]ˣ) : ℚ_[p]) ∈ PadicInt.subring p :=
  Iff.rfl

theorem isOpen_padicIntegralUnitsSubgroup
    (p : ℕ) [Fact p.Prime] :
    IsOpen (padicIntegralUnitsSubgroup p : Set ℚ_[p]ˣ) := by
  have hopen : IsOpen (PadicInt.subring p : Set ℚ_[p]) := by
    change IsOpen {x : ℚ_[p] | ‖x‖ ≤ 1}
    simpa [Metric.closedBall, dist_zero_right] using
      (IsUltrametricDist.isOpen_closedBall (x := (0 : ℚ_[p]))
        (r := 1) one_ne_zero)
  exact (hopen.preimage Units.continuous_val).inter
    (hopen.preimage Units.continuous_coe_inv)

theorem isCompact_padicIntegralUnitsSubgroup
    (p : ℕ) [Fact p.Prime] :
    IsCompact (padicIntegralUnitsSubgroup p : Set ℚ_[p]ˣ) := by
  have hp : IsCompact (PadicInt.subring p : Set ℚ_[p]) := by
    simpa only [isCompact_iff_compactSpace] using PadicInt.compactSpace p
  exact Submonoid.units_isCompact hp

/-- The generic p-adic special-orthogonal group mapped to the ambient general
linear group. -/
def padicSpecialOrthogonalToGL
    (p : ℕ) [Fact p.Prime] :
    V.specialOrthogonalMatrixGroup ℚ_[p] →*
      (Matrix (Fin n) (Fin n) ℚ_[p])ˣ :=
  (formPreservingMatrixSubgroup
      (V.specialOrthogonalMappedFormMatrix ℚ_[p])).subtype.comp
    (specialFormPreservingMatrixSubgroup
      (V.specialOrthogonalMappedFormMatrix ℚ_[p])).subtype

theorem continuous_padicSpecialOrthogonalToGL
    (p : ℕ) [Fact p.Prime] :
    Continuous (V.padicSpecialOrthogonalToGL p) :=
  continuous_subtype_val.comp continuous_subtype_val

/-- The integral matrix-and-inverse subgroup in the generic p-adic
special-orthogonal carrier. -/
def padicSpecialOrthogonalIntegralSubgroup
    (p : ℕ) [Fact p.Prime] :
    Subgroup (V.specialOrthogonalMatrixGroup ℚ_[p]) :=
  (localPadicIntegralMatrixUnitsSubgroup p n).comap
    (V.padicSpecialOrthogonalToGL p)

@[simp]
theorem mem_padicSpecialOrthogonalIntegralSubgroup_iff
    (p : ℕ) [Fact p.Prime]
    (g : V.specialOrthogonalMatrixGroup ℚ_[p]) :
    g ∈ V.padicSpecialOrthogonalIntegralSubgroup p ↔
      (∀ i j, g.1.1.1 i j ∈ PadicInt.subring p) ∧
        ∀ i j, (g.1.1⁻¹).1 i j ∈ PadicInt.subring p :=
  Iff.rfl

private theorem isClosed_padicFormPreservingSubgroup
    (p : ℕ) [Fact p.Prime] :
    IsClosed
      (formPreservingMatrixSubgroup
          (V.specialOrthogonalMappedFormMatrix ℚ_[p]) :
        Set (Matrix (Fin n) (Fin n) ℚ_[p])ˣ) := by
  change IsClosed
    {g : (Matrix (Fin n) (Fin n) ℚ_[p])ˣ |
      g.1ᵀ * V.specialOrthogonalMappedFormMatrix ℚ_[p] * g.1 =
        V.specialOrthogonalMappedFormMatrix ℚ_[p]}
  exact isClosed_eq (by fun_prop) continuous_const

private theorem isClosed_padicSpecialSubgroup
    (p : ℕ) [Fact p.Prime] :
    IsClosed
      (specialFormPreservingMatrixSubgroup
          (V.specialOrthogonalMappedFormMatrix ℚ_[p]) :
        Set (formPreservingMatrixSubgroup
          (V.specialOrthogonalMappedFormMatrix ℚ_[p]))) := by
  rw [show
      (specialFormPreservingMatrixSubgroup
          (V.specialOrthogonalMappedFormMatrix ℚ_[p]) :
        Set (formPreservingMatrixSubgroup
          (V.specialOrthogonalMappedFormMatrix ℚ_[p]))) =
        {g | g.1.1.det = 1} by
      ext g
      exact mem_specialFormPreservingMatrixSubgroup_iff
        (V.specialOrthogonalMappedFormMatrix ℚ_[p]) g]
  exact isClosed_eq
    ((Units.continuous_val.comp continuous_subtype_val).matrix_det)
    continuous_const

theorem isOpen_padicSpecialOrthogonalIntegralSubgroup
    (p : ℕ) [Fact p.Prime] :
    IsOpen
      (V.padicSpecialOrthogonalIntegralSubgroup p :
        Set (V.specialOrthogonalMatrixGroup ℚ_[p])) :=
  (isOpen_localPadicIntegralMatrixUnitsSubgroup p n).preimage
    (V.continuous_padicSpecialOrthogonalToGL p)

theorem isCompact_padicSpecialOrthogonalIntegralSubgroup
    (p : ℕ) [Fact p.Prime] :
    IsCompact
      (V.padicSpecialOrthogonalIntegralSubgroup p :
        Set (V.specialOrthogonalMatrixGroup ℚ_[p])) := by
  have hspecial :=
    (V.isClosed_padicSpecialSubgroup p).isClosedEmbedding_subtypeVal
  have hform :=
    (V.isClosed_padicFormPreservingSubgroup p).isClosedEmbedding_subtypeVal
  exact (hform.comp hspecial).isCompact_preimage
    (isCompact_localPadicIntegralMatrixUnitsSubgroup p n)

/-! ## The integral intrinsic general-Spin locus -/

/-- Literal p-adic integral coordinates for intrinsic `GSpin`. -/
def PadicCliffordGeneralSpinIsIntegral
    (p : ℕ) [Fact p.Prime]
    (x : V.PadicCliffordGeneralSpinGroup p) : Prop :=
  (∀ s, (V.cliffordCoordinateBaseChangeBasis ℚ_[p]).repr
      (x.cliffordUnit : V.cliffordCoordinateBaseChangeAlgebra ℚ_[p]) s ∈
        PadicInt.subring p) ∧
  (∀ s, (V.cliffordCoordinateBaseChangeBasis ℚ_[p]).repr
      ((x.cliffordUnit⁻¹ :
        (V.cliffordCoordinateBaseChangeAlgebra ℚ_[p])ˣ) :
          V.cliffordCoordinateBaseChangeAlgebra ℚ_[p]) s ∈
        PadicInt.subring p) ∧
  x.similitude ∈ padicIntegralUnitsSubgroup p ∧
  x.matrixGroup ∈ V.padicSpecialOrthogonalIntegralSubgroup p

def padicCliffordGeneralSpinIntegralCoordinateTarget
    (p : ℕ) [Fact p.Prime] :
    Set (V.CliffordGeneralSpinClosedCoordinateSpace ℚ_[p]) :=
  {z |
    (∀ s, z.1.1.1 s ∈ PadicInt.subring p) ∧
    (∀ s, z.1.1.2 s ∈ PadicInt.subring p) ∧
    z.1.2 ∈ padicIntegralUnitsSubgroup p ∧
    z.2 ∈ V.padicSpecialOrthogonalIntegralSubgroup p}

theorem padicCliffordGeneralSpinIsIntegral_iff_mem_target
    (p : ℕ) [Fact p.Prime]
    (x : V.PadicCliffordGeneralSpinGroup p) :
    V.PadicCliffordGeneralSpinIsIntegral p x ↔
      V.cliffordGeneralSpinClosedCoordinateMap ℚ_[p] x ∈
        V.padicCliffordGeneralSpinIntegralCoordinateTarget p :=
  Iff.rfl

theorem isCompact_padicCliffordGeneralSpinIntegralCoordinateTarget
    (p : ℕ) [Fact p.Prime] :
    IsCompact (V.padicCliffordGeneralSpinIntegralCoordinateTarget p) := by
  have hp : IsCompact (PadicInt.subring p : Set ℚ_[p]) := by
    simpa only [isCompact_iff_compactSpace] using PadicInt.compactSpace p
  have hc : IsCompact
      {c : Finset (Fin n) → ℚ_[p] | ∀ s, c s ∈ PadicInt.subring p} := by
    rw [show
      {c : Finset (Fin n) → ℚ_[p] | ∀ s, c s ∈ PadicInt.subring p} =
        Set.univ.pi fun _ => (PadicInt.subring p : Set ℚ_[p]) by
      ext c
      simp]
    exact isCompact_univ_pi fun _ => hp
  have htarget : V.padicCliffordGeneralSpinIntegralCoordinateTarget p =
      Set.prod
        (Set.prod
          (Set.prod
            {c : Finset (Fin n) → ℚ_[p] |
              ∀ s, c s ∈ PadicInt.subring p}
            {c : Finset (Fin n) → ℚ_[p] |
              ∀ s, c s ∈ PadicInt.subring p})
          (padicIntegralUnitsSubgroup p : Set ℚ_[p]ˣ))
        (V.padicSpecialOrthogonalIntegralSubgroup p :
          Set (V.specialOrthogonalMatrixGroup ℚ_[p])) := by
    ext z
    change (_ ∧ _ ∧ _ ∧ _) ↔ (((_ ∧ _) ∧ _) ∧ _)
    tauto
  rw [htarget]
  exact ((hc.prod hc).prod (isCompact_padicIntegralUnitsSubgroup p)).prod
    (V.isCompact_padicSpecialOrthogonalIntegralSubgroup p)

theorem isCompact_padicCliffordGeneralSpinIsIntegral
    (p : ℕ) [Fact p.Prime] :
    IsCompact
      {x : V.PadicCliffordGeneralSpinGroup p |
        V.PadicCliffordGeneralSpinIsIntegral p x} := by
  rw [show
      {x : V.PadicCliffordGeneralSpinGroup p |
        V.PadicCliffordGeneralSpinIsIntegral p x} =
      (V.cliffordGeneralSpinClosedCoordinateMap ℚ_[p]) ⁻¹'
        V.padicCliffordGeneralSpinIntegralCoordinateTarget p by
    ext x
    exact V.padicCliffordGeneralSpinIsIntegral_iff_mem_target p x]
  exact (V.cliffordGeneralSpinClosedCoordinateMap_isClosedEmbedding ℚ_[p])
    |>.isCompact_preimage
      (V.isCompact_padicCliffordGeneralSpinIntegralCoordinateTarget p)

theorem isOpen_padicCliffordGeneralSpinIsIntegral
    (p : ℕ) [Fact p.Prime] :
    IsOpen
      {x : V.PadicCliffordGeneralSpinGroup p |
        V.PadicCliffordGeneralSpinIsIntegral p x} := by
  have hopen : IsOpen (PadicInt.subring p : Set ℚ_[p]) := by
    change IsOpen {x : ℚ_[p] | ‖x‖ ≤ 1}
    simpa [Metric.closedBall, dist_zero_right] using
      (IsUltrametricDist.isOpen_closedBall (x := (0 : ℚ_[p]))
        (r := 1) one_ne_zero)
  have hc : IsOpen
      {x : V.PadicCliffordGeneralSpinGroup p |
        ∀ s, (V.cliffordCoordinateBaseChangeBasis ℚ_[p]).repr
          (x.cliffordUnit : V.cliffordCoordinateBaseChangeAlgebra ℚ_[p]) s ∈
            PadicInt.subring p} := by
    rw [show
      {x : V.PadicCliffordGeneralSpinGroup p |
        ∀ s, (V.cliffordCoordinateBaseChangeBasis ℚ_[p]).repr
          (x.cliffordUnit : V.cliffordCoordinateBaseChangeAlgebra ℚ_[p]) s ∈
            PadicInt.subring p} =
        ⋂ s, {x | (V.cliffordCoordinateBaseChangeBasis ℚ_[p]).repr
          (x.cliffordUnit : V.cliffordCoordinateBaseChangeAlgebra ℚ_[p]) s ∈
            PadicInt.subring p} by
      ext x
      simp]
    exact isOpen_iInter_of_finite fun s => hopen.preimage
      (V.continuous_cliffordGeneralSpinCliffordCoordinate ℚ_[p] s)
  have hci : IsOpen
      {x : V.PadicCliffordGeneralSpinGroup p |
        ∀ s, (V.cliffordCoordinateBaseChangeBasis ℚ_[p]).repr
          ((x.cliffordUnit⁻¹ :
            (V.cliffordCoordinateBaseChangeAlgebra ℚ_[p])ˣ) :
              V.cliffordCoordinateBaseChangeAlgebra ℚ_[p]) s ∈
            PadicInt.subring p} := by
    rw [show
      {x : V.PadicCliffordGeneralSpinGroup p |
        ∀ s, (V.cliffordCoordinateBaseChangeBasis ℚ_[p]).repr
          ((x.cliffordUnit⁻¹ :
            (V.cliffordCoordinateBaseChangeAlgebra ℚ_[p])ˣ) :
              V.cliffordCoordinateBaseChangeAlgebra ℚ_[p]) s ∈
            PadicInt.subring p} =
        ⋂ s, {x | (V.cliffordCoordinateBaseChangeBasis ℚ_[p]).repr
          ((x.cliffordUnit⁻¹ :
            (V.cliffordCoordinateBaseChangeAlgebra ℚ_[p])ˣ) :
              V.cliffordCoordinateBaseChangeAlgebra ℚ_[p]) s ∈
            PadicInt.subring p} by
      ext x
      simp]
    exact isOpen_iInter_of_finite fun s => hopen.preimage
      ((V.continuous_cliffordGeneralSpinCliffordCoordinate ℚ_[p] s).comp
        continuous_inv)
  have hnu : IsOpen
      {x : V.PadicCliffordGeneralSpinGroup p |
        x.similitude ∈ padicIntegralUnitsSubgroup p} := by
    change IsOpen ((fun x : V.PadicCliffordGeneralSpinGroup p => x.similitude) ⁻¹'
      (padicIntegralUnitsSubgroup p : Set ℚ_[p]ˣ))
    exact (isOpen_padicIntegralUnitsSubgroup p).preimage
      (V.continuous_cliffordGeneralSpinSimilitude ℚ_[p])
  have hso : IsOpen
      {x : V.PadicCliffordGeneralSpinGroup p |
        x.matrixGroup ∈ V.padicSpecialOrthogonalIntegralSubgroup p} := by
    change IsOpen
      ((CliffordGeneralSpinIntrinsicPoint.toSpecialOrthogonalGroupHom V ℚ_[p]) ⁻¹'
        (V.padicSpecialOrthogonalIntegralSubgroup p :
          Set (V.specialOrthogonalMatrixGroup ℚ_[p])))
    exact (V.isOpen_padicSpecialOrthogonalIntegralSubgroup p).preimage
      (V.continuous_cliffordGeneralSpinToSpecialOrthogonalGroupHom ℚ_[p])
  exact hc.inter (hci.inter (hnu.inter hso))

end RationalQuadraticSpaceMatrix
