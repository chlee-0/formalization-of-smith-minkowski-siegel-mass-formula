import SMSFormula.AdelicFinitePresentation
import SMSFormula.QuadraticReflection
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.Topology.Instances.ZMod

/-!
# Concrete local p-adic orthogonal Haar measure

This file isolates the one-prime topological group needed by the local
gauge-measure comparison.  It constructs the orthogonal subgroup over
`ℚ_[p]`, its compact-open integral lattice stabilizer, and Haar measure
normalized to give that stabilizer volume one.

The differential-form identification with Schulze--Pillot's gauge measure is
deliberately not asserted here.  Mathlib's abstract Haar measure determines a
measure only up to scale; the gauge-form disintegration is the remaining
source input that must identify that scale.
-/

noncomputable section

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

open MeasureTheory
open Matrix
open TopologicalSpace
open scoped ENNReal Matrix

/-! ## Local orthogonal group and integral stabilizer -/

/-- The form matrix of `L` over the p-adic field. -/
def localPadicFormMatrix (L : PositiveDefiniteIntegralLattice n) (p : ℕ)
    [Fact (Nat.Prime p)] : Matrix (Fin n) (Fin n) ℚ_[p] :=
  L.pairingMatrix_padicField p

/-- The concrete p-adic orthogonal matrix group attached to `L`. -/
def localPadicOrthogonalMatrixSubgroup (L : PositiveDefiniteIntegralLattice n) (p : ℕ)
    [Fact (Nat.Prime p)] : Subgroup (Matrix (Fin n) (Fin n) ℚ_[p])ˣ :=
  formPreservingMatrixSubgroup (L.localPadicFormMatrix p)

/-- The carrier of the concrete p-adic orthogonal group. -/
abbrev ConcreteLocalPadicOrthogonalGroup (L : PositiveDefiniteIntegralLattice n) (p : ℕ)
    [Fact (Nat.Prime p)] :=
  L.localPadicOrthogonalMatrixSubgroup p

@[simp]
theorem mem_localPadicOrthogonalMatrixSubgroup_iff
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)]
    (g : (Matrix (Fin n) (Fin n) ℚ_[p])ˣ) :
    g ∈ L.localPadicOrthogonalMatrixSubgroup p ↔
      g.1ᵀ * L.localPadicFormMatrix p * g.1 = L.localPadicFormMatrix p :=
  Iff.rfl

/-- The p-adic orthogonal group is closed in the ambient general linear
group. -/
theorem isClosed_localPadicOrthogonalMatrixSubgroup
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    IsClosed (L.localPadicOrthogonalMatrixSubgroup p :
      Set (Matrix (Fin n) (Fin n) ℚ_[p])ˣ) := by
  change IsClosed
    {g : (Matrix (Fin n) (Fin n) ℚ_[p])ˣ |
      g.1ᵀ * L.localPadicFormMatrix p * g.1 = L.localPadicFormMatrix p}
  have hcontinuous : Continuous
      (fun g : (Matrix (Fin n) (Fin n) ℚ_[p])ˣ ↦
        g.1ᵀ * L.localPadicFormMatrix p * g.1) := by
    fun_prop
  change IsClosed ((fun g : (Matrix (Fin n) (Fin n) ℚ_[p])ˣ ↦
    g.1ᵀ * L.localPadicFormMatrix p * g.1) ⁻¹'
      {L.localPadicFormMatrix p})
  exact isClosed_singleton.preimage hcontinuous

/-- Integral p-adic matrix units: both a matrix and its inverse have entries
in `ℤ_[p]`. -/
def localPadicIntegralMatrixUnitsSubgroup (p n : ℕ)
    [Fact (Nat.Prime p)] : Subgroup (Matrix (Fin n) (Fin n) ℚ_[p])ˣ :=
  matrixUnitsOverSubring (PadicInt.subring p)

@[simp]
theorem mem_localPadicIntegralMatrixUnitsSubgroup_iff
    (p n : ℕ) [Fact (Nat.Prime p)]
    (g : (Matrix (Fin n) (Fin n) ℚ_[p])ˣ) :
    g ∈ localPadicIntegralMatrixUnitsSubgroup p n ↔
      (∀ i j, g.1 i j ∈ PadicInt.subring p) ∧
        (∀ i j, (g⁻¹).1 i j ∈ PadicInt.subring p) :=
  Iff.rfl

/-- Integral p-adic matrix units form an open subgroup. -/
theorem isOpen_localPadicIntegralMatrixUnitsSubgroup
    (p n : ℕ) [Fact (Nat.Prime p)] :
    IsOpen (localPadicIntegralMatrixUnitsSubgroup p n :
      Set (Matrix (Fin n) (Fin n) ℚ_[p])ˣ) := by
  apply isOpen_matrixUnitsOverSubring (PadicInt.subring p)
  change IsOpen {x : ℚ_[p] | ‖x‖ ≤ 1}
  simpa [Metric.closedBall, dist_zero_right] using
    (IsUltrametricDist.isOpen_closedBall (x := (0 : ℚ_[p]))
      (r := 1) one_ne_zero)

/-- Integral p-adic matrix units form a compact subgroup. -/
theorem isCompact_localPadicIntegralMatrixUnitsSubgroup
    (p n : ℕ) [Fact (Nat.Prime p)] :
    IsCompact (localPadicIntegralMatrixUnitsSubgroup p n :
      Set (Matrix (Fin n) (Fin n) ℚ_[p])ˣ) := by
  letI : T1Space (Matrix (Fin n) (Fin n) ℚ_[p]) :=
    inferInstanceAs (T1Space (Fin n → Fin n → ℚ_[p]))
  have hp : IsCompact (PadicInt.subring p : Set ℚ_[p]) := by
    simpa only [isCompact_iff_compactSpace] using PadicInt.compactSpace p
  have hsubmonoid : IsCompact
      ((Subring.matrix (n := Fin n) (PadicInt.subring p)).toSubmonoid :
        Set (Matrix (Fin n) (Fin n) ℚ_[p])) :=
    IsCompact.matrix (m := Fin n) (n := Fin n) hp
  exact Submonoid.units_isCompact hsubmonoid

/-- The integral lattice stabilizer inside the concrete p-adic orthogonal
group. -/
def localPadicLatticeStabilizerSubgroup
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    Subgroup (L.ConcreteLocalPadicOrthogonalGroup p) :=
  (localPadicIntegralMatrixUnitsSubgroup p n).comap
    (L.localPadicOrthogonalMatrixSubgroup p).subtype

@[simp]
theorem mem_localPadicLatticeStabilizerSubgroup_iff
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)]
    (g : L.ConcreteLocalPadicOrthogonalGroup p) :
    g ∈ L.localPadicLatticeStabilizerSubgroup p ↔
      (∀ i j, g.1.1 i j ∈ PadicInt.subring p) ∧
        (∀ i j, (g.1⁻¹).1 i j ∈ PadicInt.subring p) :=
  Iff.rfl

theorem isOpen_localPadicLatticeStabilizerSubgroup
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    IsOpen (L.localPadicLatticeStabilizerSubgroup p :
      Set (L.ConcreteLocalPadicOrthogonalGroup p)) := by
  exact (isOpen_localPadicIntegralMatrixUnitsSubgroup p n).preimage
    continuous_subtype_val

theorem isCompact_localPadicLatticeStabilizerSubgroup
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    IsCompact (L.localPadicLatticeStabilizerSubgroup p :
      Set (L.ConcreteLocalPadicOrthogonalGroup p)) := by
  have hembedding :=
    (L.isClosed_localPadicOrthogonalMatrixSubgroup p).isClosedEmbedding_subtypeVal
  exact hembedding.isCompact_preimage
    (isCompact_localPadicIntegralMatrixUnitsSubgroup p n)

/-! ## Haar normalization -/

noncomputable instance concreteLocalPadicOrthogonalGroupSecondCountableTopology
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    SecondCountableTopology (L.ConcreteLocalPadicOrthogonalGroup p) := by
  letI : SecondCountableTopology (Fin n → ℚ_[p]) :=
    TopologicalSpace.instSecondCountableTopologyForallOfCountable
  letI : SecondCountableTopology (Matrix (Fin n) (Fin n) ℚ_[p]) :=
    TopologicalSpace.instSecondCountableTopologyForallOfCountable
  letI : SecondCountableTopology
      (Matrix (Fin n) (Fin n) ℚ_[p])ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  letI : SecondCountableTopology
      (Matrix (Fin n) (Fin n) ℚ_[p] ×
        (Matrix (Fin n) (Fin n) ℚ_[p])ᵐᵒᵖ) :=
    inferInstance
  letI : SecondCountableTopology
      (Matrix (Fin n) (Fin n) ℚ_[p])ˣ :=
    Units.isEmbedding_embedProduct.secondCountableTopology
  exact TopologicalSpace.secondCountableTopology_induced
    (L.ConcreteLocalPadicOrthogonalGroup p)
    ((Matrix (Fin n) (Fin n) ℚ_[p])ˣ)
    ((↑) : L.ConcreteLocalPadicOrthogonalGroup p →
      (Matrix (Fin n) (Fin n) ℚ_[p])ˣ)

instance concreteLocalPadicOrthogonalGroupMeasurableSpace
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    MeasurableSpace (L.ConcreteLocalPadicOrthogonalGroup p) :=
  borel (L.ConcreteLocalPadicOrthogonalGroup p)

instance concreteLocalPadicOrthogonalGroupBorelSpace
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    BorelSpace (L.ConcreteLocalPadicOrthogonalGroup p) :=
  ⟨rfl⟩

/-- The compact-open local stabilizer as a Haar normalization set. -/
def localPadicLatticeStabilizerPositiveCompacts
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    PositiveCompacts (L.ConcreteLocalPadicOrthogonalGroup p) where
  carrier := L.localPadicLatticeStabilizerSubgroup p
  isCompact' := L.isCompact_localPadicLatticeStabilizerSubgroup p
  interior_nonempty' := by
    rw [L.isOpen_localPadicLatticeStabilizerSubgroup p |>.interior_eq]
    exact ⟨1, Subgroup.one_mem _⟩

instance concreteLocalPadicOrthogonalGroupLocallyCompactSpace
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    LocallyCompactSpace (L.ConcreteLocalPadicOrthogonalGroup p) :=
  (L.localPadicLatticeStabilizerPositiveCompacts p).locallyCompactSpace_of_group

/-- Haar measure normalized so that the integral local stabilizer has volume
one. -/
noncomputable def localPadicOrthogonalHaarMeasure
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    Measure (L.ConcreteLocalPadicOrthogonalGroup p) :=
  Measure.haarMeasure (L.localPadicLatticeStabilizerPositiveCompacts p)

instance localPadicOrthogonalHaarMeasure_isMulLeftInvariant
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    Measure.IsMulLeftInvariant (L.localPadicOrthogonalHaarMeasure p) := by
  unfold localPadicOrthogonalHaarMeasure
  infer_instance

@[simp]
theorem localPadicOrthogonalHaarMeasure_stabilizer
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    L.localPadicOrthogonalHaarMeasure p
        (L.localPadicLatticeStabilizerSubgroup p :
          Set (L.ConcreteLocalPadicOrthogonalGroup p)) = 1 :=
  Measure.haarMeasure_self

/-- Haar measure on the compact-open integral stabilizer, obtained by
comapping the ambient stabilizer-normalized Haar measure. -/
noncomputable def localPadicLatticeStabilizerHaarMeasure
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    Measure (L.localPadicLatticeStabilizerSubgroup p) :=
  Measure.comap
    (fun h : L.localPadicLatticeStabilizerSubgroup p =>
      (h : L.ConcreteLocalPadicOrthogonalGroup p))
    (L.localPadicOrthogonalHaarMeasure p)

/-- The integral stabilizer uses the inherited subtype measurable space. -/
theorem localPadicLatticeStabilizerMeasurableSpace_eq
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    (inferInstance :
      MeasurableSpace (L.localPadicLatticeStabilizerSubgroup p)) =
      (@Subtype.instMeasurableSpace
        (L.ConcreteLocalPadicOrthogonalGroup p)
        (fun x => x ∈ L.localPadicLatticeStabilizerSubgroup p)
        (inferInstance :
          MeasurableSpace (L.ConcreteLocalPadicOrthogonalGroup p))) :=
  rfl

/-- The normalized Haar measure on the integral stabilizer has total mass
one. -/
@[simp]
theorem localPadicLatticeStabilizerHaarMeasure_univ
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    L.localPadicLatticeStabilizerHaarMeasure p Set.univ = 1 := by
  change (Measure.comap
    (fun h : L.localPadicLatticeStabilizerSubgroup p =>
      (h : L.ConcreteLocalPadicOrthogonalGroup p))
    (L.localPadicOrthogonalHaarMeasure p)) Set.univ = 1
  rw [subgroup_comap_measure_univ_eq_of_subtype_mspace
    (L.localPadicLatticeStabilizerSubgroup p)
    (L.localPadicLatticeStabilizerMeasurableSpace_eq p)
    (L.isOpen_localPadicLatticeStabilizerSubgroup p).measurableSet]
  exact L.localPadicOrthogonalHaarMeasure_stabilizer p

instance localPadicLatticeStabilizerHaarMeasure_isMulLeftInvariant
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    Measure.IsMulLeftInvariant
      (L.localPadicLatticeStabilizerHaarMeasure p) := by
  exact subgroup_comap_measure_isMulLeftInvariant_of_subtype_mspace
    (L.localPadicLatticeStabilizerSubgroup p)
    (L.localPadicLatticeStabilizerMeasurableSpace_eq p)
    (L.isOpen_localPadicLatticeStabilizerSubgroup p).measurableSet

/-- A measurable finite-reduction kernel inside the integral stabilizer has
volume equal to the reciprocal cardinality of the reduction image.  This is
the finite-index part of a principal-congruence volume calculation; it does
not identify the differential-form scale. -/
theorem localPadicLatticeStabilizerHaarMeasure_ker_eq_inv_natCard_range
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)]
    {Q : Type*} [Group Q] [Finite Q]
    (f : L.localPadicLatticeStabilizerSubgroup p →* Q)
    (hker : MeasurableSet (f.ker :
      Set (L.localPadicLatticeStabilizerSubgroup p))) :
    L.localPadicLatticeStabilizerHaarMeasure p
        (f.ker : Set (L.localPadicLatticeStabilizerSubgroup p)) =
      (Nat.card f.range : ℝ≥0∞)⁻¹ := by
  letI : f.ker.FiniteIndex := inferInstance
  have hindex := Subgroup.index_mul_measure f.ker hker
    (L.localPadicLatticeStabilizerHaarMeasure p)
  rw [L.localPadicLatticeStabilizerHaarMeasure_univ p,
    Subgroup.index_ker] at hindex
  apply ENNReal.eq_inv_of_mul_eq_one_left
  calc
    L.localPadicLatticeStabilizerHaarMeasure p
          (f.ker : Set (L.localPadicLatticeStabilizerSubgroup p)) *
        (Nat.card f.range : ℝ≥0∞) =
      (Nat.card f.range : ℝ≥0∞) *
        L.localPadicLatticeStabilizerHaarMeasure p
          (f.ker : Set (L.localPadicLatticeStabilizerSubgroup p)) :=
      mul_comm _ _
    _ = 1 := hindex

/-! ## Finite congruence reduction -/

theorem isOpen_ker_padicInt_toZModPow
    (p k : ℕ) [Fact (Nat.Prime p)] :
    IsOpen (RingHom.ker
      (PadicInt.toZModPow k : ℤ_[p] →+* ZMod (p ^ k)) : Set ℤ_[p]) := by
  rw [PadicInt.ker_toZModPow]
  have hr : (p : ℝ) ^ (-k : ℤ) ≠ 0 := by
    apply zpow_ne_zero
    exact_mod_cast (Fact.out : Nat.Prime p).ne_zero
  simpa only [Metric.closedBall, dist_zero_right,
    PadicInt.norm_le_pow_iff_mem_span_pow] using
      (IsUltrametricDist.isOpen_closedBall (x := (0 : ℤ_[p]))
        (r := (p : ℝ) ^ (-k : ℤ)) hr)

theorem continuous_padicInt_toZModPow
    (p k : ℕ) [Fact (Nat.Prime p)] :
    Continuous (PadicInt.toZModPow k : ℤ_[p] → ZMod (p ^ k)) := by
  letI : UniformSpace (ZMod (p ^ k)) := ⊥
  have hkernel : IsOpen
      (((PadicInt.toZModPow k : ℤ_[p] →+* ZMod (p ^ k)).toAddMonoidHom).ker :
        Set ℤ_[p]) :=
    isOpen_ker_padicInt_toZModPow p k
  have hu : UniformContinuous
      ((PadicInt.toZModPow k :
        ℤ_[p] →+* ZMod (p ^ k)).toAddMonoidHom) :=
    (IsUniformAddGroup.uniformContinuous_iff_isOpen_ker
      (f := (PadicInt.toZModPow k :
        ℤ_[p] →+* ZMod (p ^ k)).toAddMonoidHom)).2 hkernel
  exact hu.continuous

private theorem coe_padicInt_matrix_mul_apply
    (p : ℕ) [Fact (Nat.Prime p)]
    (A B : Matrix (Fin n) (Fin n) ℤ_[p]) (i j : Fin n) :
    (((A * B) i j : ℤ_[p]) : ℚ_[p]) =
      ∑ k, (A i k : ℚ_[p]) * (B k j : ℚ_[p]) := by
  change PadicInt.Coe.ringHom (∑ k, A i k * B k j) = _
  rw [map_sum]
  rfl

/-- An integral p-adic stabilizer element, represented over `ℤ_[p]`. -/
def localPadicLatticeStabilizerIntegralGL
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)]
    (g : L.localPadicLatticeStabilizerSubgroup p) :
    GL (Fin n) ℤ_[p] where
  val i j := ⟨g.1.1.1 i j, g.2.1 i j⟩
  inv i j := ⟨(g.1.1⁻¹).1 i j, g.2.2 i j⟩
  val_inv := by
    apply Matrix.ext
    intro i j
    apply PadicInt.ext
    rw [coe_padicInt_matrix_mul_apply]
    calc
      _ = (g.1.1.1 * (g.1.1⁻¹).1) i j := rfl
      _ = (1 : Matrix (Fin n) (Fin n) ℚ_[p]) i j :=
        congr_fun (congr_fun g.1.1.val_inv i) j
      _ = ((1 : Matrix (Fin n) (Fin n) ℤ_[p]) i j : ℚ_[p]) := by
        by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  inv_val := by
    apply Matrix.ext
    intro i j
    apply PadicInt.ext
    rw [coe_padicInt_matrix_mul_apply]
    calc
      _ = ((g.1.1⁻¹).1 * g.1.1.1) i j := rfl
      _ = (1 : Matrix (Fin n) (Fin n) ℚ_[p]) i j :=
        congr_fun (congr_fun g.1.1.inv_val i) j
      _ = ((1 : Matrix (Fin n) (Fin n) ℤ_[p]) i j : ℚ_[p]) := by
        by_cases hij : i = j <;> simp [Matrix.one_apply, hij]

@[simp]
theorem localPadicLatticeStabilizerIntegralGL_apply
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)]
    (g : L.localPadicLatticeStabilizerSubgroup p) (i j : Fin n) :
    ((L.localPadicLatticeStabilizerIntegralGL p g i j : ℤ_[p]) : ℚ_[p]) =
      g.1.1.1 i j :=
  rfl

theorem continuous_localPadicLatticeStabilizerIntegralGL_apply
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)]
    (i j : Fin n) :
    Continuous (fun g : L.localPadicLatticeStabilizerSubgroup p =>
      L.localPadicLatticeStabilizerIntegralGL p g i j) := by
  have hcoe : Continuous
      (fun g : L.localPadicLatticeStabilizerSubgroup p =>
        g.1.1.1 i j) := by
    have hsubgroup : Continuous
        (fun g : L.localPadicLatticeStabilizerSubgroup p => g.1) :=
      continuous_subtype_val
    have horthogonal : Continuous
        (fun g : L.localPadicLatticeStabilizerSubgroup p => g.1.1) :=
      continuous_subtype_val.comp hsubgroup
    have hmatrix : Continuous
        (fun g : L.localPadicLatticeStabilizerSubgroup p => g.1.1.1) :=
      Units.continuous_val.comp horthogonal
    exact (continuous_apply j).comp ((continuous_apply i).comp hmatrix)
  simpa [localPadicLatticeStabilizerIntegralGL] using
    (show Continuous
      (fun g : L.localPadicLatticeStabilizerSubgroup p =>
        (⟨g.1.1.1 i j, g.2.1 i j⟩ : ℤ_[p])) by
      exact hcoe.subtype_mk _)

/-- The integral-matrix realization of the local stabilizer is multiplicative. -/
def localPadicLatticeStabilizerIntegralGLHom
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    L.localPadicLatticeStabilizerSubgroup p →* GL (Fin n) ℤ_[p] where
  toFun := L.localPadicLatticeStabilizerIntegralGL p
  map_one' := by
    apply Units.ext
    apply Matrix.ext
    intro i j
    apply PadicInt.ext
    simp [localPadicLatticeStabilizerIntegralGL]
    by_cases hij : i = j
    · subst j
      simp
    · simp [hij]
  map_mul' g h := by
    apply Units.ext
    apply Matrix.ext
    intro i j
    apply PadicInt.ext
    change (g.1.1.1 * h.1.1.1) i j =
      (((L.localPadicLatticeStabilizerIntegralGL p g).1 *
        (L.localPadicLatticeStabilizerIntegralGL p h).1) i j : ℤ_[p])
    rw [coe_padicInt_matrix_mul_apply]
    rfl

/-- Entrywise reduction modulo `p^k` of the integral local stabilizer. -/
def localPadicLatticeStabilizerReduction
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)] :
    L.localPadicLatticeStabilizerSubgroup p →*
      GL (Fin n) (ZMod (p ^ k)) :=
  (GeneralLinearGroup.map (PadicInt.toZModPow k)).comp
    (L.localPadicLatticeStabilizerIntegralGLHom p)

@[simp]
theorem localPadicLatticeStabilizerReduction_apply
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (g : L.localPadicLatticeStabilizerSubgroup p) (i j : Fin n) :
    L.localPadicLatticeStabilizerReduction p k g i j =
      PadicInt.toZModPow k
        (L.localPadicLatticeStabilizerIntegralGL p g i j) :=
  rfl

theorem localPadicLatticeStabilizerIntegralGL_preserves_form
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)]
    (g : L.localPadicLatticeStabilizerSubgroup p) :
    (L.localPadicLatticeStabilizerIntegralGL p g).1ᵀ *
        L.pairingMatrix_padic p *
        (L.localPadicLatticeStabilizerIntegralGL p g).1 =
      L.pairingMatrix_padic p := by
  apply Matrix.ext
  intro i j
  apply PadicInt.ext
  have hmap :
      (((L.localPadicLatticeStabilizerIntegralGL p g).1ᵀ *
          L.pairingMatrix_padic p *
          (L.localPadicLatticeStabilizerIntegralGL p g).1).map
        PadicInt.Coe.ringHom) =
        (L.pairingMatrix_padic p).map PadicInt.Coe.ringHom := by
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map]
    change g.1.1.1ᵀ * L.pairingMatrix_padicField p * g.1.1.1 =
      L.pairingMatrix_padicField p
    exact g.1.2
  exact congr_fun (congr_fun hmap i) j

theorem localPadicLatticeStabilizerReduction_preserves_form
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (g : L.localPadicLatticeStabilizerSubgroup p) :
    (L.localPadicLatticeStabilizerReduction p k g).1ᵀ *
        L.pairingMatrix.map (Int.castRingHom (ZMod (p ^ k))) *
        (L.localPadicLatticeStabilizerReduction p k g).1 =
      L.pairingMatrix.map (Int.castRingHom (ZMod (p ^ k))) := by
  have hmap := congrArg
    (RingHom.mapMatrix (PadicInt.toZModPow k))
    (L.localPadicLatticeStabilizerIntegralGL_preserves_form p g)
  have hcast :
      (L.pairingMatrix_padic p).map (PadicInt.toZModPow k) =
        L.pairingMatrix.map (Int.castRingHom (ZMod (p ^ k))) := by
    ext i j
    simp [pairingMatrix_padic]
  change
    (((L.localPadicLatticeStabilizerIntegralGL p g).1ᵀ *
        L.pairingMatrix_padic p *
        (L.localPadicLatticeStabilizerIntegralGL p g).1).map
      (PadicInt.toZModPow k)) =
      (L.pairingMatrix_padic p).map (PadicInt.toZModPow k) at hmap
  rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map] at hmap
  rw [hcast] at hmap
  simpa [localPadicLatticeStabilizerReduction,
    localPadicLatticeStabilizerIntegralGLHom] using hmap

/-! ## Determinant-one local stabilizers -/

/-- The determinant character of the integral local stabilizer, valued in
p-adic integer units. -/
def localPadicLatticeStabilizerDeterminant
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    L.localPadicLatticeStabilizerSubgroup p →* ℤ_[p]ˣ :=
  (Matrix.GeneralLinearGroup.det (n := Fin n)).comp
    (L.localPadicLatticeStabilizerIntegralGLHom p)

/-- The determinant-one subgroup of the integral local stabilizer. -/
def localPadicSpecialOrthogonalLatticeStabilizerSubgroup
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    Subgroup (L.localPadicLatticeStabilizerSubgroup p) :=
  (L.localPadicLatticeStabilizerDeterminant p).ker

private theorem localPadicLatticeStabilizer_matrix_det_sq
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)]
    (g : L.localPadicLatticeStabilizerSubgroup p) :
    g.1.1.1.det ^ 2 = 1 := by
  have hF : (L.pairingMatrix_padicField p).det ≠ 0 := by
    rw [L.pairingMatrix_padicField_det p]
    exact_mod_cast (ne_of_gt L.pairingDeterminant_pos)
  have hdet := congrArg Matrix.det g.1.2
  simp only [Matrix.det_mul, Matrix.det_transpose] at hdet
  apply mul_right_cancel₀ hF
  calc
    g.1.1.1.det ^ 2 * (L.pairingMatrix_padicField p).det =
        g.1.1.1.det * (L.pairingMatrix_padicField p).det * g.1.1.1.det := by
      ring
    _ = (L.pairingMatrix_padicField p).det := hdet
    _ = 1 * (L.pairingMatrix_padicField p).det := (one_mul _).symm

private theorem localPadicLatticeStabilizerIntegralGL_det_sq
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)]
    (g : L.localPadicLatticeStabilizerSubgroup p) :
    (L.localPadicLatticeStabilizerIntegralGL p g).1.det ^ 2 = 1 := by
  apply PadicInt.ext
  change
    PadicInt.Coe.ringHom
        ((L.localPadicLatticeStabilizerIntegralGL p g).1.det ^ 2) =
      PadicInt.Coe.ringHom 1
  rw [map_pow, map_one,
    PadicInt.Coe.ringHom.map_det
      (L.localPadicLatticeStabilizerIntegralGL p g).1]
  change g.1.1.1.det ^ 2 = 1
  exact L.localPadicLatticeStabilizer_matrix_det_sq p g

private theorem coe_localPadicLatticeStabilizerIntegralGL_det
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)]
    (g : L.localPadicLatticeStabilizerSubgroup p) :
    ((L.localPadicLatticeStabilizerIntegralGL p g).1.det : ℚ_[p]) =
      g.1.1.1.det := by
  calc
    ((L.localPadicLatticeStabilizerIntegralGL p g).1.det : ℚ_[p]) =
        ((L.localPadicLatticeStabilizerIntegralGL p g).1.map
          PadicInt.Coe.ringHom).det :=
      PadicInt.Coe.ringHom.map_det
        (L.localPadicLatticeStabilizerIntegralGL p g).1
    _ = g.1.1.1.det := by
      congr 1

/-- The integral determinant-one kernel is exactly the intersection with the
ambient p-adic special orthogonal group. -/
@[simp]
theorem mem_localPadicSpecialOrthogonalLatticeStabilizerSubgroup_iff
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)]
    (g : L.localPadicLatticeStabilizerSubgroup p) :
    g ∈ L.localPadicSpecialOrthogonalLatticeStabilizerSubgroup p ↔
      g.1.1.1.det = 1 := by
  change
    Matrix.GeneralLinearGroup.det
        (L.localPadicLatticeStabilizerIntegralGL p g) = 1 ↔
      g.1.1.1.det = 1
  constructor
  · intro h
    have hdet := congrArg Units.val h
    change (L.localPadicLatticeStabilizerIntegralGL p g).1.det = 1 at hdet
    rw [← L.coe_localPadicLatticeStabilizerIntegralGL_det p g]
    rw [hdet]
    rfl
  · intro h
    apply Units.ext
    change (L.localPadicLatticeStabilizerIntegralGL p g).1.det = 1
    apply PadicInt.ext
    rw [L.coe_localPadicLatticeStabilizerIntegralGL_det p g, h]
    rfl

/-- Every value of the integral determinant character has square one. -/
theorem localPadicLatticeStabilizerDeterminant_sq
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)]
    (g : L.localPadicLatticeStabilizerSubgroup p) :
    L.localPadicLatticeStabilizerDeterminant p g ^ 2 = 1 := by
  apply Units.ext
  exact L.localPadicLatticeStabilizerIntegralGL_det_sq p g

/-- The determinant character on the concrete finite reduction image. -/
def localPadicLatticeStabilizerReductionRangeDeterminant
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)] :
    (L.localPadicLatticeStabilizerReduction p k).range →*
      (ZMod (p ^ k))ˣ :=
  (Matrix.GeneralLinearGroup.det (n := Fin n)).comp
    (L.localPadicLatticeStabilizerReduction p k).range.subtype

/-- The determinant-one subgroup of the concrete finite reduction image. -/
def localPadicSpecialOrthogonalLatticeStabilizerReductionRangeSubgroup
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)] :
    Subgroup (L.localPadicLatticeStabilizerReduction p k).range :=
  (L.localPadicLatticeStabilizerReductionRangeDeterminant p k).ker

/-- Membership in the finite determinant-one kernel is the expected matrix
determinant equation. -/
@[simp]
theorem mem_localPadicSpecialOrthogonalLatticeStabilizerReductionRangeSubgroup_iff
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (u : (L.localPadicLatticeStabilizerReduction p k).range) :
    u ∈ L.localPadicSpecialOrthogonalLatticeStabilizerReductionRangeSubgroup p k ↔
      u.1.1.det = 1 := by
  change Matrix.GeneralLinearGroup.det u.1 = 1 ↔ u.1.1.det = 1
  constructor
  · intro h
    exact congrArg Units.val h
  · intro h
    exact Units.ext h

/-- Finite reduction carries the integral determinant character to the
residue-ring determinant character. -/
theorem localPadicLatticeStabilizerReductionRangeDeterminant_apply
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (g : L.localPadicLatticeStabilizerSubgroup p) :
    L.localPadicLatticeStabilizerReductionRangeDeterminant p k
        ⟨L.localPadicLatticeStabilizerReduction p k g, ⟨g, rfl⟩⟩ =
      Units.map (PadicInt.toZModPow k).toMonoidHom
        (L.localPadicLatticeStabilizerDeterminant p g) := by
  exact Matrix.GeneralLinearGroup.map_det
    (f := PadicInt.toZModPow k)
    (L.localPadicLatticeStabilizerIntegralGL p g)

private theorem localPadicLatticeStabilizerReduction_det_sq
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (g : L.localPadicLatticeStabilizerSubgroup p) :
    (L.localPadicLatticeStabilizerReduction p k g).1.det ^ 2 = 1 := by
  have h := congrArg Units.val
    (congrArg (Units.map (PadicInt.toZModPow k).toMonoidHom)
      (L.localPadicLatticeStabilizerDeterminant_sq p g))
  have hmapdet := congrArg Units.val
    (L.localPadicLatticeStabilizerReductionRangeDeterminant_apply p k g)
  change
    (L.localPadicLatticeStabilizerReduction p k g).1.det =
      (PadicInt.toZModPow k)
        (L.localPadicLatticeStabilizerIntegralGL p g).1.det at hmapdet
  rw [hmapdet]
  simpa using h

/-- Every determinant in the concrete finite reduction image has square one. -/
theorem localPadicLatticeStabilizerReductionRangeDeterminant_sq
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (u : (L.localPadicLatticeStabilizerReduction p k).range) :
    L.localPadicLatticeStabilizerReductionRangeDeterminant p k u ^ 2 = 1 := by
  rcases u.2 with ⟨g, hg⟩
  apply Units.ext
  change u.1.1.det ^ 2 = 1
  rw [← hg]
  exact L.localPadicLatticeStabilizerReduction_det_sq p k g

/-- Reduction maps the integral special-orthogonal stabilizer into the
determinant-one part of the finite reduction image. No converse or index-two
statement is asserted. -/
def localPadicSpecialOrthogonalLatticeStabilizerReduction
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)] :
    L.localPadicSpecialOrthogonalLatticeStabilizerSubgroup p →*
      L.localPadicSpecialOrthogonalLatticeStabilizerReductionRangeSubgroup p k where
  toFun g :=
    ⟨⟨L.localPadicLatticeStabilizerReduction p k g.1, ⟨g.1, rfl⟩⟩, by
      change
        L.localPadicLatticeStabilizerReductionRangeDeterminant p k
          ⟨L.localPadicLatticeStabilizerReduction p k g.1, ⟨g.1, rfl⟩⟩ = 1
      rw [L.localPadicLatticeStabilizerReductionRangeDeterminant_apply p k g.1,
        show L.localPadicLatticeStabilizerDeterminant p g.1 = 1 from g.2]
      simp⟩
  map_one' := by
    apply Subtype.ext
    apply Subtype.ext
    exact (L.localPadicLatticeStabilizerReduction p k).map_one
  map_mul' g h := by
    apply Subtype.ext
    apply Subtype.ext
    exact (L.localPadicLatticeStabilizerReduction p k).map_mul g.1 h.1

/-! ## Conditional integral reflections -/

private theorem exists_dvd_all_of_finite
    {α R : Type*} [CommMonoid R] [PreValuationRing R]
    [Fintype α] [Nonempty α] (f : α → R) :
    ∃ a, ∀ b, f a ∣ f b := by
  classical
  let s : Finset α := Finset.univ
  have hs : s.Nonempty := Finset.univ_nonempty
  have h :
      ∀ t : Finset α, t.Nonempty →
        ∃ a ∈ t, ∀ b ∈ t, f a ∣ f b := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
        simp
    | @insert a t ha ih =>
        intro _ht
        by_cases ht : t.Nonempty
        · obtain ⟨b, hb, hball⟩ := ih ht
          rcases ValuationRing.dvd_total (f a) (f b) with hab | hba
          · exact ⟨a, Finset.mem_insert_self a t, by
              intro c hc
              rcases Finset.mem_insert.mp hc with rfl | hct
              · exact dvd_refl _
              · exact dvd_trans hab (hball c hct)⟩
          · exact ⟨b, Finset.mem_insert_of_mem hb, by
              intro c hc
              rcases Finset.mem_insert.mp hc with rfl | hct
              · exact hba
              · exact hball c hct⟩
        · have hempty : t = ∅ := Finset.not_nonempty_iff_eq_empty.mp ht
          subst t
          exact ⟨a, Finset.mem_singleton_self a, by simp⟩
  obtain ⟨a, _ha, hall⟩ := h s hs
  exact ⟨a, fun b => hall b (Finset.mem_univ b)⟩

private noncomputable def localPadicReflectionNormCandidate
    (p : ℕ) [Fact (Nat.Prime p)]
    (c : Fin n ⊕ (Fin n × Fin n)) :
    Fin n → ℤ_[p] :=
  match c with
  | Sum.inl i => Pi.single i 1
  | Sum.inr ij => Pi.single ij.1 1 + Pi.single ij.2 1

private lemma localPadicReflectionNormCandidate_norm_inl
    (p : ℕ) [Fact (Nat.Prime p)]
    (F : Matrix (Fin n) (Fin n) ℤ_[p]) (i : Fin n) :
    localPadicReflectionNormCandidate p (Sum.inl i) ⬝ᵥ
        Matrix.mulVec F (localPadicReflectionNormCandidate p (Sum.inl i)) =
      F i i := by
  simp [localPadicReflectionNormCandidate, dotProduct, Matrix.mulVec,
    Pi.single_apply]

private lemma localPadic_single_dot_mulVec_single
    (p : ℕ) [Fact (Nat.Prime p)]
    (F : Matrix (Fin n) (Fin n) ℤ_[p]) (i j : Fin n) :
    Pi.single i 1 ⬝ᵥ Matrix.mulVec F (Pi.single j 1) = F i j := by
  simp [dotProduct, Matrix.mulVec, Pi.single_apply]

private lemma localPadicReflectionNormCandidate_norm_inr
    (p : ℕ) [Fact (Nat.Prime p)]
    (F : Matrix (Fin n) (Fin n) ℤ_[p]) (hF : F.IsSymm)
    (i j : Fin n) :
    localPadicReflectionNormCandidate p (Sum.inr (i, j)) ⬝ᵥ
        Matrix.mulVec F (localPadicReflectionNormCandidate p (Sum.inr (i, j))) =
      F i i + F j j + 2 * F i j := by
  have hji : F j i = F i j := congrFun (congrFun hF i) j
  change
    (Pi.single i 1 + Pi.single j 1) ⬝ᵥ
        Matrix.mulVec F (Pi.single i 1 + Pi.single j 1) =
      F i i + F j j + 2 * F i j
  rw [Matrix.mulVec_add, dotProduct_add, add_dotProduct]
  simp only [localPadic_single_dot_mulVec_single, hji]
  rw [add_dotProduct]
  simp only [localPadic_single_dot_mulVec_single]
  ring

/-- Integral data for a p-adic reflection. The vector has nonzero norm over
the p-adic field, and the resulting reflection matrix has integral entries.
Existence of such data is deliberately not asserted here. -/
structure LocalPadicIntegralReflectionData
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] where
  vector : Fin n → ℤ_[p]
  norm_ne_zero :
    gramQuadraticValue (L.pairingMatrix_padicField p)
        (fun i => (vector i : ℚ_[p])) ≠ 0
  reflection_integral :
    ∀ i j,
      gramReflectionMatrix (L.pairingMatrix_padicField p)
          (fun a => (vector a : ℚ_[p])) i j ∈ PadicInt.subring p

/-- A divisibility certificate sufficient for an integral p-adic reflection.
The norm divides every rank-one correction entry before division in `Q_p`. -/
structure LocalPadicIntegralReflectionNormGeneratorData
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] where
  vector : Fin n → ℤ_[p]
  norm_ne_zero :
    vector ⬝ᵥ Matrix.mulVec (L.pairingMatrix_padic p) vector ≠ 0
  norm_dvd_correction :
    ∀ i j,
      vector ⬝ᵥ Matrix.mulVec (L.pairingMatrix_padic p) vector ∣
        2 * vector i * Matrix.mulVec (L.pairingMatrix_padic p) vector j

/-- If a nonzero represented norm divides every form-matrix entry, then it
supplies the required reflection-correction divisibility. -/
noncomputable def
    LocalPadicIntegralReflectionNormGeneratorData.ofNormDvdFormMatrix
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)]
    (w : Fin n → ℤ_[p])
    (hq : w ⬝ᵥ Matrix.mulVec (L.pairingMatrix_padic p) w ≠ 0)
    (hdiv : ∀ i j,
      w ⬝ᵥ Matrix.mulVec (L.pairingMatrix_padic p) w ∣
        L.pairingMatrix_padic p i j) :
    LocalPadicIntegralReflectionNormGeneratorData L p := by
  refine ⟨w, hq, ?_⟩
  intro i j
  have hmulvec :
      w ⬝ᵥ Matrix.mulVec (L.pairingMatrix_padic p) w ∣
        Matrix.mulVec (L.pairingMatrix_padic p) w j := by
    change
      w ⬝ᵥ Matrix.mulVec (L.pairingMatrix_padic p) w ∣
        ∑ a, L.pairingMatrix_padic p j a * w a
    apply Finset.dvd_sum
    intro a _ha
    exact dvd_mul_of_dvd_left (hdiv j a) (w a)
  exact dvd_mul_of_dvd_right hmulvec (2 * w i)

/-- A norm-generator divisibility certificate gives integral reflection data. -/
noncomputable def
    LocalPadicIntegralReflectionNormGeneratorData.reflectionData
    {L : PositiveDefiniteIntegralLattice n} {p : ℕ} [Fact (Nat.Prime p)]
    (d : LocalPadicIntegralReflectionNormGeneratorData L p) :
    LocalPadicIntegralReflectionData L p := by
  let qZ : ℤ_[p] :=
    d.vector ⬝ᵥ Matrix.mulVec (L.pairingMatrix_padic p) d.vector
  let wQ : Fin n → ℚ_[p] := fun i => (d.vector i : ℚ_[p])
  have hq :
      gramQuadraticValue (L.pairingMatrix_padicField p) wQ = (qZ : ℚ_[p]) := by
    simp [gramQuadraticValue, pairingMatrix_padicField, wQ, qZ,
      Matrix.mulVec, dotProduct]
  have hq_ne : (qZ : ℚ_[p]) ≠ 0 :=
    PadicInt.coe_ne_zero.mpr d.norm_ne_zero
  refine {
    vector := d.vector
    norm_ne_zero := hq ▸ hq_ne
    reflection_integral := ?_
  }
  intro i j
  obtain ⟨c, hc⟩ := d.norm_dvd_correction i j
  have hmul :
      Matrix.mulVec (L.pairingMatrix_padicField p) wQ j =
        ((Matrix.mulVec (L.pairingMatrix_padic p) d.vector j : ℤ_[p]) : ℚ_[p]) := by
    change
      (∑ a, (L.pairingMatrix_padic p j a : ℚ_[p]) *
          (d.vector a : ℚ_[p])) =
        PadicInt.Coe.ringHom
          (∑ a, L.pairingMatrix_padic p j a * d.vector a)
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro a _ha
    rw [map_mul]
    rfl
  have hcQ :
      (2 : ℚ_[p]) * (d.vector i : ℚ_[p]) *
          Matrix.mulVec (L.pairingMatrix_padicField p) wQ j =
        (qZ : ℚ_[p]) * (c : ℚ_[p]) := by
    rw [hmul]
    have hc' := congrArg PadicInt.Coe.ringHom hc
    change
      (2 : ℚ_[p]) * (d.vector i : ℚ_[p]) *
          ((Matrix.mulVec (L.pairingMatrix_padic p) d.vector j : ℤ_[p]) : ℚ_[p]) =
        (qZ : ℚ_[p]) * (c : ℚ_[p])
    simpa [qZ] using hc'
  have hcoef :
      (2 / (qZ : ℚ_[p])) *
          ((d.vector i : ℚ_[p]) *
            Matrix.mulVec (L.pairingMatrix_padicField p) wQ j) =
        (c : ℚ_[p]) := by
    field_simp [hq_ne]
    simpa [mul_assoc] using hcQ
  rw [gramReflectionMatrix, hq]
  change
    (1 : Matrix (Fin n) (Fin n) ℚ_[p]) i j -
        (2 / (qZ : ℚ_[p])) *
          ((d.vector i : ℚ_[p]) *
            Matrix.mulVec (L.pairingMatrix_padicField p) wQ j) ∈
      PadicInt.subring p
  rw [hcoef]
  exact (PadicInt.subring p).sub_mem
    (by
      by_cases hij : i = j
      · subst j
        simp
      · simp [hij])
    c.property

/-- A vector of unit integral norm gives an integral reflection certificate.
The unit inverse supplies the coefficient `2 / Q(w)` inside `ℤ_[p]`. -/
noncomputable def LocalPadicIntegralReflectionData.ofNormIsUnit
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)]
    (w : Fin n → ℤ_[p])
    (hw : IsUnit (w ⬝ᵥ Matrix.mulVec (L.pairingMatrix_padic p) w)) :
    LocalPadicIntegralReflectionData L p := by
  let qZ : ℤ_[p] := w ⬝ᵥ Matrix.mulVec (L.pairingMatrix_padic p) w
  let u : ℤ_[p]ˣ := hw.unit
  let cZ : ℤ_[p] := 2 * (u⁻¹ : ℤ_[p]ˣ)
  let wQ : Fin n → ℚ_[p] := fun i => (w i : ℚ_[p])
  have hu : (u : ℤ_[p]) = qZ := IsUnit.unit_spec _
  have hq :
      gramQuadraticValue (L.pairingMatrix_padicField p) wQ = (qZ : ℚ_[p]) := by
    simp [gramQuadraticValue, pairingMatrix_padicField, wQ, qZ,
      Matrix.mulVec, dotProduct]
  have hq_ne : gramQuadraticValue (L.pairingMatrix_padicField p) wQ ≠ 0 := by
    rw [hq]
    intro h
    apply hw.ne_zero
    change qZ = 0
    apply PadicInt.ext
    exact h
  have hc :
      (cZ : ℚ_[p]) =
        2 / gramQuadraticValue (L.pairingMatrix_padicField p) wQ := by
    rw [hq]
    calc
      (cZ : ℚ_[p]) =
          (2 : ℚ_[p]) * (((↑(u⁻¹) : ℤ_[p]) : ℚ_[p])) := by
            change PadicInt.Coe.ringHom
              ((2 : ℤ_[p]) * ((u⁻¹ : ℤ_[p]ˣ) : ℤ_[p])) = _
            rw [map_mul]
            rfl
      _ = (2 : ℚ_[p]) * (((u : ℤ_[p]) : ℚ_[p]))⁻¹ := by
            congr 1
            change
              ((Units.map PadicInt.Coe.ringHom.toMonoidHom
                  (u⁻¹) : ℚ_[p]ˣ) : ℚ_[p]) =
                ((Units.map PadicInt.Coe.ringHom.toMonoidHom
                  u : ℚ_[p]ˣ) : ℚ_[p])⁻¹
            simp
      _ = (2 : ℚ_[p]) * (qZ : ℚ_[p])⁻¹ := by rw [hu]
      _ = 2 / (qZ : ℚ_[p]) := by rw [div_eq_mul_inv]
  refine {
    vector := w
    norm_ne_zero := hq_ne
    reflection_integral := ?_
  }
  intro i j
  rw [gramReflectionMatrix]
  rw [← hc]
  change
    (1 : Matrix (Fin n) (Fin n) ℚ_[p]) i j -
        (cZ : ℚ_[p]) *
          ((w i : ℚ_[p]) *
            Matrix.mulVec (L.pairingMatrix_padicField p) wQ j) ∈
      PadicInt.subring p
  have hmul :
      Matrix.mulVec (L.pairingMatrix_padicField p) wQ j =
        ((Matrix.mulVec (L.pairingMatrix_padic p) w j : ℤ_[p]) : ℚ_[p]) := by
    change
      (∑ a, (L.pairingMatrix_padic p j a : ℚ_[p]) * (w a : ℚ_[p])) =
        PadicInt.Coe.ringHom
          (∑ a, L.pairingMatrix_padic p j a * w a)
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro a _ha
    rw [map_mul]
    rfl
  rw [hmul]
  exact (PadicInt.subring p).sub_mem
    (by
      by_cases hij : i = j
      · subst j
        simp
      · simp [hij])
    ((PadicInt.subring p).mul_mem cZ.property
      ((PadicInt.subring p).mul_mem (w i).property
        (Matrix.mulVec (L.pairingMatrix_padic p) w j).property))

/-- At an odd prime, every positive-dimensional unimodular local form has an
integral reflection certificate. A nonzero represented residue value lifts
to a unit integral norm, so no Hensel argument is needed. -/
theorem
    localPadicIntegralReflectionData_nonempty_of_ne_two_of_pairingMatrix_det_isUnit
    (L : PositiveDefiniteIntegralLattice n) [NeZero n]
    (p : ℕ) [Fact (Nat.Prime p)] (hp_two : p ≠ 2)
    (hF : IsUnit (L.pairingMatrix_padic p).det) :
    Nonempty (LocalPadicIntegralReflectionData L p) := by
  let A : Matrix (Fin n) (Fin n) (ZMod p) :=
    (L.pairingMatrix_padic p).map PadicInt.toZMod
  have hA_symm : A.IsSymm := by
    simpa [A, pairingMatrix_padic] using
      ((L.form_symm.map (Int.castRingHom ℤ_[p])).map PadicInt.toZMod)
  have hA_det : A.det ≠ 0 := by
    have hunit : IsUnit (PadicInt.toZMod (L.pairingMatrix_padic p).det) :=
      hF.map PadicInt.toZMod
    have hdet :
        A.det = PadicInt.toZMod (L.pairingMatrix_padic p).det := by
      simpa [A] using
        (RingHom.map_det PadicInt.toZMod (L.pairingMatrix_padic p)).symm
    rw [hdet]
    exact hunit.ne_zero
  obtain ⟨c, hc, r, hr⟩ :=
    exists_gramQuadraticValue_eq_ne_zero A hA_symm hA_det (by
      simpa [ZMod.ringChar_zmod_n] using hp_two)
  let w : Fin n → ℤ_[p] := fun i => (r i).val
  have hw_res (i : Fin n) : PadicInt.toZMod (w i) = r i := by
    apply ZMod.val_injective
    simp [w]
  let qZ : ℤ_[p] := w ⬝ᵥ Matrix.mulVec (L.pairingMatrix_padic p) w
  have hq_res : PadicInt.toZMod qZ = c := by
    calc
      PadicInt.toZMod qZ = gramQuadraticValue A r := by
        simp only [qZ, gramQuadraticValue, dotProduct, Matrix.mulVec, A,
          Matrix.map_apply]
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro i _hi
        rw [map_mul, hw_res]
        congr 1
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro j _hj
        rw [map_mul, hw_res]
      _ = c := hr
  have hq_unit : IsUnit qZ := by
    by_contra hnot
    have hmem :
        qZ ∈ RingHom.ker (PadicInt.toZMod : ℤ_[p] →+* ZMod p) := by
      rw [PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal]
      exact hnot
    exact hc (hq_res ▸ hmem)
  exact ⟨LocalPadicIntegralReflectionData.ofNormIsUnit L p w hq_unit⟩

/-- Every positive-dimensional integral local lattice has a norm-generator
reflection certificate. Among the finitely many standard basis and pair-sum
norms, valuation-ring divisibility selects one that divides all the others.
Their polarization identities give exactly the integral reflection
corrections, including at the dyadic prime. -/
theorem localPadicIntegralReflectionNormGeneratorData_nonempty
    (L : PositiveDefiniteIntegralLattice n) [NeZero n]
    (p : ℕ) [Fact (Nat.Prime p)] :
    Nonempty (LocalPadicIntegralReflectionNormGeneratorData L p) := by
  classical
  let i0 : Fin n := ⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩
  letI : Nonempty (Fin n) := ⟨i0⟩
  let C := Fin n ⊕ (Fin n × Fin n)
  let q : C → ℤ_[p] := fun c =>
    localPadicReflectionNormCandidate p c ⬝ᵥ
      Matrix.mulVec (L.pairingMatrix_padic p)
        (localPadicReflectionNormCandidate p c)
  obtain ⟨c, hc⟩ := exists_dvd_all_of_finite q
  let w := localPadicReflectionNormCandidate p c
  have hdiag (i : Fin n) :
      q c ∣ L.pairingMatrix_padic p i i := by
    simpa [q, localPadicReflectionNormCandidate_norm_inl] using
      hc (Sum.inl i)
  have htwice_entry (i j : Fin n) :
      q c ∣ 2 * L.pairingMatrix_padic p i j := by
    have hpair := hc (Sum.inr (i, j))
    rw [show q (Sum.inr (i, j)) =
        L.pairingMatrix_padic p i i + L.pairingMatrix_padic p j j +
          2 * L.pairingMatrix_padic p i j by
      exact localPadicReflectionNormCandidate_norm_inr p
        (L.pairingMatrix_padic p)
        (by simpa [pairingMatrix_padic] using
          L.form_symm.map (Int.castRingHom ℤ_[p])) i j] at hpair
    have hsub := dvd_sub hpair (dvd_add (hdiag i) (hdiag j))
    simpa only [add_sub_cancel_left] using hsub
  have htwice_mulVec (j : Fin n) :
      q c ∣ 2 * Matrix.mulVec (L.pairingMatrix_padic p) w j := by
    rcases c with i | ij
    · simpa [w, localPadicReflectionNormCandidate, Matrix.mulVec,
        Pi.single_apply] using htwice_entry j i
    · have hadd := dvd_add (htwice_entry j ij.1) (htwice_entry j ij.2)
      simpa [w, localPadicReflectionNormCandidate, Matrix.mulVec,
        Pi.single_apply, mul_add] using hadd
  have hcorrection (i j : Fin n) :
      q c ∣ 2 * w i * Matrix.mulVec (L.pairingMatrix_padic p) w j := by
    have hmul := dvd_mul_of_dvd_left (htwice_mulVec j) (w i)
    simpa [mul_assoc, mul_left_comm, mul_comm] using hmul
  have hq_ne : q c ≠ 0 := by
    intro hq
    have hzero : L.pairingMatrix_padic p = 0 := by
      ext i j
      have hij := htwice_entry i j
      rw [hq, zero_dvd_iff] at hij
      exact (mul_eq_zero.mp hij).resolve_left (by norm_num)
    have hdet : (L.pairingMatrix_padicField p).det ≠ 0 := by
      rw [L.pairingMatrix_padicField_det p]
      exact_mod_cast (ne_of_gt L.pairingDeterminant_pos)
    apply hdet
    rw [pairingMatrix_padicField, hzero]
    exact Matrix.det_zero (R := ℚ_[p]) (n := Fin n) inferInstance
  exact ⟨{
    vector := w
    norm_ne_zero := by simpa [w, q] using hq_ne
    norm_dvd_correction := by
      intro i j
      simpa [q] using hcorrection i j
  }⟩

/-- Odd-prime compatibility specialization of the general norm-generator
existence theorem. -/
theorem localPadicIntegralReflectionNormGeneratorData_nonempty_of_ne_two
    (L : PositiveDefiniteIntegralLattice n) [NeZero n]
    (p : ℕ) [Fact (Nat.Prime p)] (_hp_two : p ≠ 2) :
    Nonempty (LocalPadicIntegralReflectionNormGeneratorData L p) :=
  localPadicIntegralReflectionNormGeneratorData_nonempty L p

/-- Every positive-dimensional integral local lattice has integral reflection
data, including at the dyadic prime. -/
theorem localPadicIntegralReflectionData_nonempty
    (L : PositiveDefiniteIntegralLattice n) [NeZero n]
    (p : ℕ) [Fact (Nat.Prime p)] :
    Nonempty (LocalPadicIntegralReflectionData L p) := by
  obtain ⟨d⟩ :=
    localPadicIntegralReflectionNormGeneratorData_nonempty L p
  exact ⟨d.reflectionData⟩

/-- Odd-prime compatibility specialization of integral reflection existence. -/
theorem localPadicIntegralReflectionData_nonempty_of_ne_two
    (L : PositiveDefiniteIntegralLattice n) [NeZero n]
    (p : ℕ) [Fact (Nat.Prime p)] (_hp_two : p ≠ 2) :
    Nonempty (LocalPadicIntegralReflectionData L p) :=
  localPadicIntegralReflectionData_nonempty L p

/-- The integral reflection matrix associated to a conditional certificate. -/
def LocalPadicIntegralReflectionData.matrix
    {L : PositiveDefiniteIntegralLattice n} {p : ℕ} [Fact (Nat.Prime p)]
    (d : LocalPadicIntegralReflectionData L p) :
    Matrix (Fin n) (Fin n) ℤ_[p] :=
  fun i j =>
    ⟨gramReflectionMatrix (L.pairingMatrix_padicField p)
        (fun a => (d.vector a : ℚ_[p])) i j,
      d.reflection_integral i j⟩

/-- Casting an integral reflection certificate to the p-adic field recovers
the standard Gram reflection. -/
lemma LocalPadicIntegralReflectionData.coe_matrix_eq_gramReflectionMatrix
    {L : PositiveDefiniteIntegralLattice n} {p : ℕ} [Fact (Nat.Prime p)]
    (d : LocalPadicIntegralReflectionData L p) :
    d.matrix.map PadicInt.Coe.ringHom =
      gramReflectionMatrix (L.pairingMatrix_padicField p)
        (fun i => (d.vector i : ℚ_[p])) := by
  ext i j
  rfl

/-- The integral reflection matrix has determinant `-1`. -/
lemma LocalPadicIntegralReflectionData.matrix_det
    {L : PositiveDefiniteIntegralLattice n} {p : ℕ} [Fact (Nat.Prime p)]
    (d : LocalPadicIntegralReflectionData L p) :
    d.matrix.det = -1 := by
  apply PadicInt.ext
  rw [show ((d.matrix.det : ℤ_[p]) : ℚ_[p]) =
      (d.matrix.map PadicInt.Coe.ringHom).det by
        exact PadicInt.Coe.ringHom.map_det d.matrix]
  rw [d.coe_matrix_eq_gramReflectionMatrix,
    gramReflectionMatrix_det _ _ d.norm_ne_zero]
  rfl

/-- The integral reflection matrix preserves the integral form matrix. -/
lemma LocalPadicIntegralReflectionData.matrix_preserves_form
    {L : PositiveDefiniteIntegralLattice n} {p : ℕ} [Fact (Nat.Prime p)]
    (d : LocalPadicIntegralReflectionData L p) :
    d.matrixᵀ * L.pairingMatrix_padic p * d.matrix =
      L.pairingMatrix_padic p := by
  apply Matrix.ext
  intro i j
  apply PadicInt.ext
  have hmap :
      ((d.matrixᵀ * L.pairingMatrix_padic p * d.matrix).map
          PadicInt.Coe.ringHom) =
        (L.pairingMatrix_padic p).map PadicInt.Coe.ringHom := by
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map,
      d.coe_matrix_eq_gramReflectionMatrix]
    have hsymm : (L.pairingMatrix_padicField p).IsSymm := by
      simpa [pairingMatrix_padicField, pairingMatrix_padic] using
        ((L.form_symm.map (Int.castRingHom ℤ_[p])).map
          PadicInt.Coe.ringHom)
    exact gramReflectionMatrix_preserves (L.pairingMatrix_padicField p)
      hsymm _ d.norm_ne_zero
  exact congrFun (congrFun hmap i) j

/-- The integral reflection matrix as a general-linear element. -/
lemma LocalPadicIntegralReflectionData.matrix_isUnit
    {L : PositiveDefiniteIntegralLattice n} {p : ℕ} [Fact (Nat.Prime p)]
    (d : LocalPadicIntegralReflectionData L p) :
    IsUnit d.matrix := by
  rw [Matrix.isUnit_iff_isUnit_det, d.matrix_det]
  exact isUnit_one.neg

noncomputable def LocalPadicIntegralReflectionData.integralGL
    {L : PositiveDefiniteIntegralLattice n} {p : ℕ} [Fact (Nat.Prime p)]
    (d : LocalPadicIntegralReflectionData L p) :
    GL (Fin n) ℤ_[p] :=
  d.matrix_isUnit.unit

@[simp]
lemma LocalPadicIntegralReflectionData.integralGL_val
    {L : PositiveDefiniteIntegralLattice n} {p : ℕ} [Fact (Nat.Prime p)]
    (d : LocalPadicIntegralReflectionData L p) :
    d.integralGL.1 = d.matrix :=
  IsUnit.unit_spec _

/-- A conditional integral reflection certificate gives an element of the
compact-open integral p-adic stabilizer. -/
noncomputable def LocalPadicIntegralReflectionData.stabilizer
    {L : PositiveDefiniteIntegralLattice n} {p : ℕ} [Fact (Nat.Prime p)]
    (d : LocalPadicIntegralReflectionData L p) :
    L.localPadicLatticeStabilizerSubgroup p := by
  let U := d.integralGL
  let Up : GL (Fin n) ℚ_[p] :=
    GeneralLinearGroup.map PadicInt.Coe.ringHom U
  have hformQ :
      Up.1ᵀ * L.localPadicFormMatrix p * Up.1 =
        L.localPadicFormMatrix p := by
    have hmap := congrArg
      (RingHom.mapMatrix PadicInt.Coe.ringHom) d.matrix_preserves_form
    change
      (((U.1ᵀ * L.pairingMatrix_padic p * U.1).map
        PadicInt.Coe.ringHom)) =
        (L.pairingMatrix_padic p).map PadicInt.Coe.ringHom at hmap
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map] at hmap
    simpa [Up, localPadicFormMatrix, pairingMatrix_padicField] using hmap
  let g : L.ConcreteLocalPadicOrthogonalGroup p := ⟨Up, hformQ⟩
  refine ⟨g, ?_⟩
  rw [L.mem_localPadicLatticeStabilizerSubgroup_iff p]
  constructor
  · intro i j
    change Up.1 i j ∈ PadicInt.subring p
    rw [GeneralLinearGroup.map_apply]
    exact (U.1 i j).property
  · intro i j
    change (Up⁻¹).1 i j ∈ PadicInt.subring p
    rw [show Up⁻¹ =
        GeneralLinearGroup.map PadicInt.Coe.ringHom (U⁻¹) by
      simp [Up]]
    rw [GeneralLinearGroup.map_apply]
    exact ((U⁻¹).1 i j).property

/-- The conditional reflection has ambient p-adic determinant `-1`. -/
theorem LocalPadicIntegralReflectionData.stabilizer_matrix_det
    {L : PositiveDefiniteIntegralLattice n} {p : ℕ} [Fact (Nat.Prime p)]
    (d : LocalPadicIntegralReflectionData L p) :
    d.stabilizer.1.1.1.det = -1 := by
  change (d.integralGL.1.map PadicInt.Coe.ringHom).det = -1
  calc
    (d.integralGL.1.map PadicInt.Coe.ringHom).det =
        PadicInt.Coe.ringHom d.integralGL.1.det :=
      (PadicInt.Coe.ringHom.map_det d.integralGL.1).symm
    _ = PadicInt.Coe.ringHom d.matrix.det := by rw [d.integralGL_val]
    _ = PadicInt.Coe.ringHom (-1) := by rw [d.matrix_det]
    _ = -1 := by simp

/-- The determinant character takes the conditional reflection to `-1`. -/
theorem LocalPadicIntegralReflectionData.stabilizer_determinant
    {L : PositiveDefiniteIntegralLattice n} {p : ℕ} [Fact (Nat.Prime p)]
    (d : LocalPadicIntegralReflectionData L p) :
    L.localPadicLatticeStabilizerDeterminant p d.stabilizer = -1 := by
  apply Units.ext
  change
    (L.localPadicLatticeStabilizerIntegralGL p d.stabilizer).1.det = -1
  apply PadicInt.ext
  calc
    (((L.localPadicLatticeStabilizerIntegralGL p d.stabilizer).1.det :
        ℤ_[p]) : ℚ_[p]) =
        ((L.localPadicLatticeStabilizerIntegralGL p d.stabilizer).1.map
          PadicInt.Coe.ringHom).det :=
      PadicInt.Coe.ringHom.map_det
        (L.localPadicLatticeStabilizerIntegralGL p d.stabilizer).1
    _ = d.stabilizer.1.1.1.det := by
      apply congrArg Matrix.det
      ext i j
      exact L.localPadicLatticeStabilizerIntegralGL_apply p d.stabilizer i j
    _ = -1 := d.stabilizer_matrix_det
    _ = ((-1 : ℤ_[p]) : ℚ_[p]) := rfl

/-- The local orientation source is internal for positive-dimensional
integral lattices: the norm-generator reflection is an integral orthogonal
matrix of determinant `-1`, including at the dyadic prime. -/
theorem exists_padicIntegralOrthogonal_det_neg_one
    (L : PositiveDefiniteIntegralLattice n) [NeZero n]
    (p : ℕ) [Fact (Nat.Prime p)] :
    ∃ R : GL (Fin n) ℤ_[p],
      R.1ᵀ * L.pairingMatrix_padic p * R.1 = L.pairingMatrix_padic p ∧
        R.1.det = -1 := by
  obtain ⟨d⟩ := localPadicIntegralReflectionData_nonempty L p
  refine ⟨d.integralGL, ?_, ?_⟩
  · rw [d.integralGL_val]
    exact d.matrix_preserves_form
  · rw [d.integralGL_val]
    exact d.matrix_det

/-- Odd-prime compatibility specialization of integral orientation. -/
theorem exists_padicIntegralOrthogonal_det_neg_one_of_ne_two
    (L : PositiveDefiniteIntegralLattice n) [NeZero n]
    (p : ℕ) [Fact (Nat.Prime p)] (_hp_two : p ≠ 2) :
    ∃ R : GL (Fin n) ℤ_[p],
      R.1ᵀ * L.pairingMatrix_padic p * R.1 = L.pairingMatrix_padic p ∧
        R.1.det = -1 :=
  exists_padicIntegralOrthogonal_det_neg_one L p

/-- The exact p-adic source-tower limit as an integral general-linear
element. -/
noncomputable def
    associatedBilinearDualQuotientSolutionFamilyTowerPadicLimitIntegralGL
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (hk : L.IsAssociatedBilinearHenselQuadraticDepth p k)
    (Y : associatedBilinearDualQuotientSolutionFamily L p k) :
    GL (Fin n) ℤ_[p] :=
  (associatedBilinearDualQuotientSolutionFamilyTowerPadicLimit_isUnit
    L p k hk Y).unit

@[simp] theorem
    associatedBilinearDualQuotientSolutionFamilyTowerPadicLimitIntegralGL_val
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (hk : L.IsAssociatedBilinearHenselQuadraticDepth p k)
    (Y : associatedBilinearDualQuotientSolutionFamily L p k) :
    (associatedBilinearDualQuotientSolutionFamilyTowerPadicLimitIntegralGL
      L p k hk Y).1 =
      associatedBilinearDualQuotientSolutionFamilyTowerPadicLimit
        L p k hk Y := by
  exact IsUnit.unit_spec _

/-- A source-normalized finite solution and a compatible tower of Hensel
lifts determine an element of the integral local lattice stabilizer. -/
noncomputable def
    associatedBilinearDualQuotientSolutionFamilyTowerPadicStabilizer
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (hk : L.IsAssociatedBilinearHenselQuadraticDepth p k)
    (Y : associatedBilinearDualQuotientSolutionFamily L p k) :
    L.localPadicLatticeStabilizerSubgroup p := by
  let U : GL (Fin n) ℤ_[p] :=
    associatedBilinearDualQuotientSolutionFamilyTowerPadicLimitIntegralGL
      L p k hk Y
  let Up : GL (Fin n) ℚ_[p] :=
    GeneralLinearGroup.map PadicInt.Coe.ringHom U
  have hformZ :
      U.1ᵀ * L.pairingMatrix_padic p * U.1 = L.pairingMatrix_padic p := by
    simpa [U] using
      associatedBilinearDualQuotientSolutionFamilyTowerPadicLimit_preserves_form
        L p k hk Y
  have hformQ :
      Up.1ᵀ * L.localPadicFormMatrix p * Up.1 =
        L.localPadicFormMatrix p := by
    have hmap := congrArg
      (RingHom.mapMatrix PadicInt.Coe.ringHom) hformZ
    change
      (((U.1ᵀ * L.pairingMatrix_padic p * U.1).map
        PadicInt.Coe.ringHom)) =
        (L.pairingMatrix_padic p).map PadicInt.Coe.ringHom at hmap
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map] at hmap
    simpa [Up, localPadicFormMatrix, pairingMatrix_padicField] using hmap
  let g : L.ConcreteLocalPadicOrthogonalGroup p := ⟨Up, hformQ⟩
  refine ⟨g, ?_⟩
  rw [L.mem_localPadicLatticeStabilizerSubgroup_iff p]
  constructor
  · intro i j
    change Up.1 i j ∈ PadicInt.subring p
    rw [GeneralLinearGroup.map_apply]
    exact (U.1 i j).property
  · intro i j
    change (Up⁻¹).1 i j ∈ PadicInt.subring p
    rw [show Up⁻¹ =
        GeneralLinearGroup.map PadicInt.Coe.ringHom (U⁻¹) by
      simp [Up]]
    rw [GeneralLinearGroup.map_apply]
    exact ((U⁻¹).1 i j).property

@[simp] theorem
    localPadicLatticeStabilizerIntegralGL_towerPadicStabilizer_val
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (hk : L.IsAssociatedBilinearHenselQuadraticDepth p k)
    (Y : associatedBilinearDualQuotientSolutionFamily L p k) :
    (L.localPadicLatticeStabilizerIntegralGL p
      (associatedBilinearDualQuotientSolutionFamilyTowerPadicStabilizer
        L p k hk Y)).1 =
      associatedBilinearDualQuotientSolutionFamilyTowerPadicLimit
        L p k hk Y := by
  ext i j
  apply PadicInt.ext
  change
    ((GeneralLinearGroup.map PadicInt.Coe.ringHom
      (associatedBilinearDualQuotientSolutionFamilyTowerPadicLimitIntegralGL
        L p k hk Y)).1 i j) =
      ((associatedBilinearDualQuotientSolutionFamilyTowerPadicLimit
        L p k hk Y i j : ℤ_[p]) : ℚ_[p])
  rw [GeneralLinearGroup.map_apply]
  congr 1

/-- The concrete stabilizer reduction recovers the selected source-tower
representative at every finite residue depth. -/
theorem
    localPadicLatticeStabilizerReduction_towerPadicStabilizer_val
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (hk : L.IsAssociatedBilinearHenselQuadraticDepth p k)
    (Y : associatedBilinearDualQuotientSolutionFamily L p k)
    (r : ℕ) :
    (L.localPadicLatticeStabilizerReduction p r
      (associatedBilinearDualQuotientSolutionFamilyTowerPadicStabilizer
        L p k hk Y)).1 =
      (associatedBilinearDualQuotientSolutionFamilyRepresentativeMatrix
        L p (k + r)
        (associatedBilinearDualQuotientSolutionFamilyTowerValue
          L p k hk Y r)).map Int.cast := by
  change
    (L.localPadicLatticeStabilizerIntegralGL p
      (associatedBilinearDualQuotientSolutionFamilyTowerPadicStabilizer
        L p k hk Y)).1.map (PadicInt.toZModPow r) = _
  rw [localPadicLatticeStabilizerIntegralGL_towerPadicStabilizer_val]
  exact
    associatedBilinearDualQuotientSolutionFamilyTowerPadicLimit_map_toZModPow
      L p k hk Y r

/-- The compatible p-adic lift sends each source quotient solution into the
concrete finite reduction image. -/
noncomputable def
    associatedBilinearDualQuotientSolutionFamilyToLocalPadicLatticeStabilizerReductionRange
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (hk : L.IsAssociatedBilinearHenselQuadraticDepth p k) :
    associatedBilinearDualQuotientSolutionFamily L p k →
      (L.localPadicLatticeStabilizerReduction p k).range :=
  fun Y =>
    ⟨L.localPadicLatticeStabilizerReduction p k
        (associatedBilinearDualQuotientSolutionFamilyTowerPadicStabilizer
          L p k hk Y),
      ⟨associatedBilinearDualQuotientSolutionFamilyTowerPadicStabilizer
          L p k hk Y, rfl⟩⟩

/-- Reduction at the initial depth distinguishes source quotient solutions.
The proof compares depth-`k+k` representatives and then reduces their tower
differences back to the initial source denominator. -/
theorem
    associatedBilinearDualQuotientSolutionFamilyToLocalPadicLatticeStabilizerReductionRange_injective
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (hk : L.IsAssociatedBilinearHenselQuadraticDepth p k) :
    Function.Injective
      (L.associatedBilinearDualQuotientSolutionFamilyToLocalPadicLatticeStabilizerReductionRange
        p k hk) := by
  intro Y Z hYZ
  apply Subtype.ext
  funext j
  rw [← Submodule.Quotient.mk_out (Y.1 j),
    ← Submodule.Quotient.mk_out (Z.1 j)]
  rw [Submodule.Quotient.eq]
  change
    (fun i =>
      associatedBilinearDualQuotientSolutionFamilyRepresentativeMatrix
          L p k Y i j -
        associatedBilinearDualQuotientSolutionFamilyRepresentativeMatrix
          L p k Z i j) ∈
      associatedBilinearDualPadicDenominatorIntegralPreimage L p k
  let RY :=
    associatedBilinearDualQuotientSolutionFamilyRepresentativeMatrix
      L p (k + k)
        (associatedBilinearDualQuotientSolutionFamilyTowerValue
          L p k hk Y k)
  let RZ :=
    associatedBilinearDualQuotientSolutionFamilyRepresentativeMatrix
      L p (k + k)
        (associatedBilinearDualQuotientSolutionFamilyTowerValue
          L p k hk Z k)
  have hmatrix :
      RY.map (Int.castRingHom (ZMod (p ^ k))) =
        RZ.map (Int.castRingHom (ZMod (p ^ k))) := by
    have hval := congrArg (fun u :
        (L.localPadicLatticeStabilizerReduction p k).range => u.1.1) hYZ
    simpa [
      associatedBilinearDualQuotientSolutionFamilyToLocalPadicLatticeStabilizerReductionRange,
      RY, RZ,
      L.localPadicLatticeStabilizerReduction_towerPadicStabilizer_val
        p k hk] using hval
  have hdeepPrime :
      (fun i => RY i j - RZ i j) ∈
        primePowCoordinateSubmodule (n := n) p k := by
    rw [mem_primePowCoordinateSubmodule_iff_coordinate_zmod_eq_zero]
    intro i
    have hij := congrArg (fun M => M i j) hmatrix
    simpa [RY, RZ] using sub_eq_zero.mpr hij
  have hdeep :
      (fun i => RY i j - RZ i j) ∈
        associatedBilinearDualPadicDenominatorIntegralPreimage L p k :=
    L.primePowCoordinateSubmodule_le_associatedBilinearDualPadicDenominatorIntegralPreimage
      p k hdeepPrime
  have hY :=
    L.associatedBilinearDualQuotientSolutionFamilyTowerValue_representative_sub_initial_mem
      p k hk Y k j
  have hZ :=
    L.associatedBilinearDualQuotientSolutionFamilyTowerValue_representative_sub_initial_mem
      p k hk Z k j
  have hsum :=
    (associatedBilinearDualPadicDenominatorIntegralPreimage L p k).add_mem
      ((associatedBilinearDualPadicDenominatorIntegralPreimage L p k).neg_mem hY)
      ((associatedBilinearDualPadicDenominatorIntegralPreimage L p k).add_mem
        hdeep hZ)
  convert hsum using 1
  ext i
  simp only [Pi.add_apply, Pi.neg_apply]
  dsimp [RY, RZ]
  ring

/-- At admissible depth, the source quotient-solution count is bounded by the
actual finite reduction image of the integral local stabilizer. -/
theorem
    associatedBilinearDualQuotientCount_le_natCard_localPadicLatticeStabilizerReduction_range
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (hk : L.IsAssociatedBilinearHenselQuadraticDepth p k) :
    associatedBilinearDualQuotientCount L p k ≤
      Nat.card (L.localPadicLatticeStabilizerReduction p k).range := by
  rw [associatedBilinearDualQuotientCount_eq_natCard_solutionFamily]
  exact Nat.card_le_card_of_injective
    (L.associatedBilinearDualQuotientSolutionFamilyToLocalPadicLatticeStabilizerReductionRange
      p k hk)
    (L.associatedBilinearDualQuotientSolutionFamilyToLocalPadicLatticeStabilizerReductionRange_injective
      p k hk)

/-- Coarsen the columns of a concrete stabilizer reduction modulo `p^k` to
classes modulo the associated-bilinear source denominator. Form preservation
shows that the resulting family is a source quotient solution at every
prime, including `2`. -/
noncomputable def
    localPadicLatticeStabilizerReductionRangeToAssociatedBilinearDualQuotientSolutionFamily
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (hk : L.IsAssociatedBilinearHenselQuadraticDepth p k) :
    (L.localPadicLatticeStabilizerReduction p k).range →
      associatedBilinearDualQuotientSolutionFamily L p k := by
  intro u
  let hPE :=
    L.primePowCoordinateSubmodule_le_associatedBilinearDualPadicDenominatorIntegralPreimage
      p k
  refine ⟨localDualQuotientFamilyOfLE (n := n) hPE
      (localDualQuotientLiftFamily (n := n) p k u.1.1), ?_⟩
  apply localDualQuotientFamilyOfLE_mem_localDualQuotientSolutionFamilies
    (hE :=
      L.associatedBilinearDualPadicDenominatorIntegralPreimage_admissible
        p k hk)
    hPE
  apply
    localDualQuotientLiftFamily_mem_localDualQuotientSolutionFamilies_of_pairingMatrix
  rcases u.2 with ⟨g, hg⟩
  have hform := L.localPadicLatticeStabilizerReduction_preserves_form p k g
  rw [hg] at hform
  simpa [matrixMod, primePowModulus] using hform

private lemma
    localPadicAssociatedBilinearFamilyOfLE_liftFamily_intCast_eq_mkQ
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (M : Matrix (Fin n) (Fin n) ℤ) :
    localDualQuotientFamilyOfLE (n := n)
        (L.primePowCoordinateSubmodule_le_associatedBilinearDualPadicDenominatorIntegralPreimage
          p k)
        (localDualQuotientLiftFamily (n := n) p k
          (M.map (Int.castRingHom (ZMod (p ^ k))))) =
      fun j =>
        (associatedBilinearDualPadicDenominatorIntegralPreimage L p k).mkQ
          (fun i => M i j) := by
  funext j
  change
    (associatedBilinearDualPadicDenominatorIntegralPreimage L p k).mkQ
        (fun i => (((M i j : ZMod (p ^ k))).val : ℤ)) =
      (associatedBilinearDualPadicDenominatorIntegralPreimage L p k).mkQ
        (fun i => M i j)
  change
    (Submodule.Quotient.mk
        (fun i => (((M i j : ZMod (p ^ k))).val : ℤ)) :
      (Fin n → ℤ) ⧸
        associatedBilinearDualPadicDenominatorIntegralPreimage L p k) =
      Submodule.Quotient.mk (fun i => M i j)
  rw [Submodule.Quotient.eq]
  apply
    L.primePowCoordinateSubmodule_le_associatedBilinearDualPadicDenominatorIntegralPreimage
      p k
  rw [mem_primePowCoordinateSubmodule_iff_coordinate_zmod_eq_zero]
  intro i
  change (((((M i j : ZMod (p ^ k))).val : ℤ) - M i j : ℤ) :
    ZMod (p ^ k)) = 0
  simp

/-- Coarsening the concrete reduction of the chosen p-adic source lift
recovers the original source quotient solution. Thus the canonical
reduction-to-source map is a retraction, but not generally an injection. -/
theorem
    localPadicLatticeStabilizerReductionRangeToAssociatedBilinearDualQuotientSolutionFamily_apply_sourceLift
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (hk : L.IsAssociatedBilinearHenselQuadraticDepth p k)
    (Y : associatedBilinearDualQuotientSolutionFamily L p k) :
    L.localPadicLatticeStabilizerReductionRangeToAssociatedBilinearDualQuotientSolutionFamily
        p k hk
        (L.associatedBilinearDualQuotientSolutionFamilyToLocalPadicLatticeStabilizerReductionRange
          p k hk Y) = Y := by
  apply Subtype.ext
  rw [show
    (L.localPadicLatticeStabilizerReductionRangeToAssociatedBilinearDualQuotientSolutionFamily
      p k hk
      (L.associatedBilinearDualQuotientSolutionFamilyToLocalPadicLatticeStabilizerReductionRange
        p k hk Y)).1 =
      localDualQuotientFamilyOfLE (n := n)
        (L.primePowCoordinateSubmodule_le_associatedBilinearDualPadicDenominatorIntegralPreimage
          p k)
        (localDualQuotientLiftFamily (n := n) p k
          ((L.localPadicLatticeStabilizerReduction p k
            (associatedBilinearDualQuotientSolutionFamilyTowerPadicStabilizer
              L p k hk Y)).1)) by rfl]
  rw [L.localPadicLatticeStabilizerReduction_towerPadicStabilizer_val
    p k hk Y k]
  let M :=
    associatedBilinearDualQuotientSolutionFamilyRepresentativeMatrix
      L p (k + k)
        (associatedBilinearDualQuotientSolutionFamilyTowerValue
          L p k hk Y k)
  calc
    localDualQuotientFamilyOfLE (n := n)
        (L.primePowCoordinateSubmodule_le_associatedBilinearDualPadicDenominatorIntegralPreimage
          p k)
        (localDualQuotientLiftFamily (n := n) p k (M.map Int.cast)) =
        fun j =>
          (associatedBilinearDualPadicDenominatorIntegralPreimage L p k).mkQ
            (fun i => M i j) := by
      simpa [M] using
        localPadicAssociatedBilinearFamilyOfLE_liftFamily_intCast_eq_mkQ
          L p k M
    _ = Y.1 := by
      funext j
      rw [← Submodule.Quotient.mk_out (Y.1 j)]
      change
        (Submodule.Quotient.mk (fun i => M i j) :
          (Fin n → ℤ) ⧸
            associatedBilinearDualPadicDenominatorIntegralPreimage L p k) =
          Submodule.Quotient.mk (Quotient.out (Y.1 j))
      rw [Submodule.Quotient.eq]
      exact
        L.associatedBilinearDualQuotientSolutionFamilyTowerValue_representative_sub_initial_mem
          p k hk Y k j

/-- A fiber of the reduction-to-source map injects into the `n`-fold
denominator-enlargement fiber. Its cardinality is therefore bounded by the
`n`th power of the one-column Gram-kernel cardinality. -/
theorem
    natCard_localPadicLatticeStabilizerReductionRangeToAssociatedBilinearDualQuotientSolutionFamily_fiber_le
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (hk : L.IsAssociatedBilinearHenselQuadraticDepth p k)
    (hdisc : padicValInt p L.polarDeterminant ≤ k)
    (Y : associatedBilinearDualQuotientSolutionFamily L p k) :
    Nat.card
        {u : (L.localPadicLatticeStabilizerReduction p k).range //
          L.localPadicLatticeStabilizerReductionRangeToAssociatedBilinearDualQuotientSolutionFamily
            p k hk u = Y} ≤
      p ^ (n * padicValInt p L.polarDeterminant) := by
  let P := primePowCoordinateSubmodule (n := n) p k
  let E := associatedBilinearDualPadicDenominatorIntegralPreimage L p k
  let hPE : P ≤ E :=
    L.primePowCoordinateSubmodule_le_associatedBilinearDualPadicDenominatorIntegralPreimage
      p k
  let F := {X : Fin n → localDualQuotientTarget P //
    localDualQuotientFamilyOfLE (n := n) hPE X = Y.1}
  let f :
      {u : (L.localPadicLatticeStabilizerReduction p k).range //
        L.localPadicLatticeStabilizerReductionRangeToAssociatedBilinearDualQuotientSolutionFamily
          p k hk u = Y} → F :=
    fun u => ⟨localDualQuotientLiftFamily (n := n) p k u.1.1.1, by
      exact congrArg Subtype.val u.2⟩
  have hf : Function.Injective f := by
    intro u v huv
    apply Subtype.ext
    apply Subtype.ext
    apply Units.ext
    have hfamily := congrArg Subtype.val huv
    exact
      (localDualQuotientFamilyMatrix_liftFamily (n := n) p k u.1.1.1).symm.trans
        ((congrArg (localDualQuotientFamilyMatrix (n := n) p k) hfamily).trans
          (localDualQuotientFamilyMatrix_liftFamily (n := n) p k v.1.1.1))
  have hone : ∀ q : localDualQuotientTarget E,
      Nat.card
          {x : localDualQuotientTarget P //
            localDualQuotientMapOfLE (n := n) hPE x = q} =
        p ^ padicValInt p L.polarDeterminant := by
    intro q
    rw [localDualQuotientMapOfLE_fiber_card_eq_ker (n := n) hPE q,
      localDualQuotientMapOfLE_ker_card_eq_subquotient (n := n) hPE]
    calc
      Nat.card (E ⧸ P.comap E.subtype) =
          Nat.card
            (LinearMap.ker
              (associatedBilinearGramModQuotientLinearMap L p k)) :=
        Nat.card_congr
          (associatedBilinearDualPadicDenominatorFiberEquivGramModQuotientLinearMapKer
            L p k).toEquiv
      _ = p ^ padicValInt p L.polarDeterminant :=
        L.associatedBilinearGramModQuotientLinearMap_ker_natCard_eq_prime_pow_polarDeterminant_val_of_le
          p k hdisc
  have hF :
      Nat.card F = (p ^ padicValInt p L.polarDeterminant) ^ n := by
    exact localDualQuotientFamilyOfLE_fiber_card_eq_pow
      (n := n)
      (primePowCoordinateSubmodule_rank (n := n) p k)
      (L.associatedBilinearDualPadicDenominatorIntegralPreimage_rank p k)
      hPE Y.1 (p ^ padicValInt p L.polarDeterminant) hone
  have hP_rank :
      Module.finrank ℤ P = Module.finrank ℤ (Fin n → ℤ) := by
    simpa [P, Module.finrank_fintype_fun_eq_card, Fintype.card_fin] using
      (primePowCoordinateSubmodule_rank (n := n) p k)
  letI : Finite (localDualQuotientTarget P) :=
    Submodule.finiteQuotientOfFreeOfRankEq (M := Fin n → ℤ) P hP_rank
  calc
    Nat.card
        {u : (L.localPadicLatticeStabilizerReduction p k).range //
          L.localPadicLatticeStabilizerReductionRangeToAssociatedBilinearDualQuotientSolutionFamily
            p k hk u = Y} ≤ Nat.card F :=
      Nat.card_le_card_of_injective f hf
    _ = (p ^ padicValInt p L.polarDeterminant) ^ n := hF
    _ = p ^ (n * padicValInt p L.polarDeterminant) := by
      rw [← Nat.pow_mul]
      rw [Nat.mul_comm]

private lemma nat_card_le_mul_of_fiber_card_le
    {α β : Type*} [Fintype α] [Fintype β] (f : α → β) (c : ℕ)
    (hfiber : ∀ b : β, Nat.card {a : α // f a = b} ≤ c) :
    Nat.card α ≤ Nat.card β * c := by
  classical
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  have hcard :
      Fintype.card α =
        ∑ b : β, ((Finset.univ : Finset α).filter fun a => f a = b).card := by
    simpa only [Finset.card_univ, Finset.mem_univ, true_implies] using
      (Finset.card_eq_sum_card_fiberwise
        (s := (Finset.univ : Finset α)) (t := (Finset.univ : Finset β))
        (f := f) (by intro a _ha; simp))
  calc
    Fintype.card α =
        ∑ b : β, ((Finset.univ : Finset α).filter fun a => f a = b).card := hcard
    _ ≤ ∑ _b : β, c := by
      apply Finset.sum_le_sum
      intro b _hb
      simpa [Fintype.card_subtype] using hfiber b
    _ = Fintype.card β * c := by simp

/-- At a depth beyond the discriminant valuation, the concrete stabilizer
reduction-image cardinality lies between the source quotient count and that
count times the full `n`-column denominator-fiber bound. -/
theorem localPadicLatticeStabilizerReduction_range_natCard_sandwich_of_polarDeterminant_val_le
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (hk : L.IsAssociatedBilinearHenselQuadraticDepth p k)
    (hdisc : padicValInt p L.polarDeterminant ≤ k) :
    associatedBilinearDualQuotientCount L p k ≤
        Nat.card (L.localPadicLatticeStabilizerReduction p k).range ∧
      Nat.card (L.localPadicLatticeStabilizerReduction p k).range ≤
        associatedBilinearDualQuotientCount L p k *
          p ^ (n * padicValInt p L.polarDeterminant) := by
  classical
  constructor
  · exact
      L.associatedBilinearDualQuotientCount_le_natCard_localPadicLatticeStabilizerReduction_range
        p k hk
  · rw [associatedBilinearDualQuotientCount_eq_natCard_solutionFamily]
    let f :=
      L.localPadicLatticeStabilizerReductionRangeToAssociatedBilinearDualQuotientSolutionFamily
        p k hk
    let c := p ^ (n * padicValInt p L.polarDeterminant)
    letI : Fintype (L.localPadicLatticeStabilizerReduction p k).range :=
      Fintype.ofFinite _
    letI :
        Fintype (associatedBilinearDualQuotientSolutionFamily L p k) :=
      Fintype.ofFinite _
    exact nat_card_le_mul_of_fiber_card_le f c fun Y =>
      L.natCard_localPadicLatticeStabilizerReductionRangeToAssociatedBilinearDualQuotientSolutionFamily_fiber_le
        p k hk hdisc Y

/-- The reduction-to-source map becomes injective under the reverse
denominator inclusion. -/
theorem
    localPadicLatticeStabilizerReductionRangeToAssociatedBilinearDualQuotientSolutionFamily_injective_of_denominator_le_primePow
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (hk : L.IsAssociatedBilinearHenselQuadraticDepth p k)
    (hDP :
      associatedBilinearDualPadicDenominatorIntegralPreimage L p k ≤
        primePowCoordinateSubmodule (n := n) p k) :
    Function.Injective
      (L.localPadicLatticeStabilizerReductionRangeToAssociatedBilinearDualQuotientSolutionFamily
        p k hk) := by
  intro u v huv
  apply Subtype.ext
  apply Units.ext
  apply Matrix.ext
  intro i j
  have hfamily := congrArg Subtype.val huv
  have hj := congrFun hfamily j
  change
    (associatedBilinearDualPadicDenominatorIntegralPreimage L p k).mkQ
        (fun a => ((u.1.1 a j).val : ℤ)) =
      (associatedBilinearDualPadicDenominatorIntegralPreimage L p k).mkQ
        (fun a => ((v.1.1 a j).val : ℤ)) at hj
  change
    (Submodule.Quotient.mk (fun a => ((u.1.1 a j).val : ℤ)) :
      (Fin n → ℤ) ⧸
        associatedBilinearDualPadicDenominatorIntegralPreimage L p k) =
      Submodule.Quotient.mk (fun a => ((v.1.1 a j).val : ℤ)) at hj
  rw [Submodule.Quotient.eq] at hj
  have hpMem := hDP hj
  have hi :=
    (mem_primePowCoordinateSubmodule_iff_coordinate_zmod_eq_zero
      (n := n) p k _).mp hpMem i
  have hu := ZMod.natCast_zmod_val (u.1.1 i j)
  have hv := ZMod.natCast_zmod_val (v.1.1 i j)
  have hu' : ((u.1.1 i j).val : ℤ) = u.1.1 i j := by
    exact_mod_cast hu
  have hv' : ((v.1.1 i j).val : ℤ) = v.1.1 i j := by
    exact_mod_cast hv
  rw [Pi.sub_apply, Int.cast_sub] at hi
  exact hu'.symm.trans ((sub_eq_zero.mp hi).trans hv')

/-- If the source denominator has no extra classes beyond `p^k ℤ^n`, then
the source quotient count is exactly the concrete stabilizer reduction-image
cardinality. At bad primes the missing reverse inclusion leaves a finite
denominator fiber that must be controlled rather than discarded. -/
theorem
    associatedBilinearDualQuotientCount_eq_natCard_localPadicLatticeStabilizerReduction_range_of_denominator_le_primePow
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (hk : L.IsAssociatedBilinearHenselQuadraticDepth p k)
    (hDP :
      associatedBilinearDualPadicDenominatorIntegralPreimage L p k ≤
        primePowCoordinateSubmodule (n := n) p k) :
    associatedBilinearDualQuotientCount L p k =
      Nat.card (L.localPadicLatticeStabilizerReduction p k).range := by
  apply Nat.le_antisymm
  · exact
      L.associatedBilinearDualQuotientCount_le_natCard_localPadicLatticeStabilizerReduction_range
        p k hk
  · rw [associatedBilinearDualQuotientCount_eq_natCard_solutionFamily]
    exact Nat.card_le_card_of_injective
      (L.localPadicLatticeStabilizerReductionRangeToAssociatedBilinearDualQuotientSolutionFamily
        p k hk)
      (L.localPadicLatticeStabilizerReductionRangeToAssociatedBilinearDualQuotientSolutionFamily_injective_of_denominator_le_primePow
        p k hk hDP)

/-- At a Gram-unit depth, the source quotient count is exactly the cardinality
of the concrete integral-stabilizer reduction image. -/
theorem
    associatedBilinearDualQuotientCount_eq_natCard_localPadicLatticeStabilizerReduction_range_of_polarGramMatrix_zmod_isUnit
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (hk : L.IsAssociatedBilinearHenselQuadraticDepth p k)
    (hG : IsUnit (matrixMod L.polarGramMatrix (primePowModulus p k))) :
    associatedBilinearDualQuotientCount L p k =
      Nat.card (L.localPadicLatticeStabilizerReduction p k).range :=
  L.associatedBilinearDualQuotientCount_eq_natCard_localPadicLatticeStabilizerReduction_range_of_denominator_le_primePow
    p k hk
    (L.associatedBilinearDualPadicDenominatorIntegralPreimage_le_primePowCoordinateSubmodule_of_polarGramMatrix_zmod_isUnit
      p k hG)

/-- A raw Gram-congruence solution is invertible once the modulus is deeper
than the p-adic valuation of the discriminant. -/
theorem gramCongruenceSolutionMatrix_isUnit_of_polarDeterminant_val_lt
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (hdisc : padicValInt p L.polarDeterminant < k)
    (X : Matrix (Fin n) (Fin n) (ZMod (p ^ k)))
    (hX : X ∈ gramCongruenceSolutionMatrices L p k) :
    IsUnit X := by
  rw [Matrix.isUnit_iff_isUnit_det]
  have hk : 0 < k := lt_of_le_of_lt (Nat.zero_le _) hdisc
  have hmatrix := mem_gramCongruenceSolutionMatrices_iff.mp hX
  change
    Xᵀ * L.polarGramMatrix.map (Int.castRingHom (ZMod (p ^ k))) * X =
      L.polarGramMatrix.map (Int.castRingHom (ZMod (p ^ k))) at hmatrix
  have hdet := congrArg Matrix.det hmatrix
  simp only [Matrix.det_mul, Matrix.det_transpose] at hdet
  have hgram :
      (L.polarGramMatrix.map (Int.castRingHom (ZMod (p ^ k)))).det =
        (L.polarDeterminant : ZMod (p ^ k)) := by
    calc
      _ = Int.castRingHom (ZMod (p ^ k)) L.polarGramMatrix.det :=
        (RingHom.map_det (Int.castRingHom (ZMod (p ^ k))) L.polarGramMatrix).symm
      _ = _ := rfl
  have hdet' :
      X.det * (L.polarDeterminant : ZMod (p ^ k)) * X.det =
        (L.polarDeterminant : ZMod (p ^ k)) := by
    simpa only [hgram] using hdet
  by_contra hunit
  have hpPow : p ∣ p ^ k := dvd_pow (dvd_refl p) hk.ne'
  have hdet_dvd : p ∣ X.det.val := by
    by_contra hnot
    apply hunit
    simpa only [ZMod.natCast_zmod_val] using
      (ZMod.isUnit_iff_coprime X.det.val (p ^ k)).2
        ((Fact.out : Nat.Prime p).coprime_pow_of_not_dvd hnot)
  have hone_not_dvd : ¬p ∣ (1 - X.det * X.det).val := by
    intro hone_dvd
    have hdet_cast : (ZMod.cast X.det : ZMod p) = 0 := by
      rw [← ZMod.natCast_zmod_val X.det, ZMod.cast_natCast hpPow]
      exact (ZMod.natCast_eq_zero_iff X.det.val p).2 hdet_dvd
    have hone_cast : (ZMod.cast (1 - X.det * X.det) : ZMod p) = 1 := by
      simp [hpPow, hdet_cast]
    have hone_zero :
        (ZMod.cast (1 - X.det * X.det) : ZMod p) = 0 := by
      rw [← ZMod.natCast_zmod_val (1 - X.det * X.det),
        ZMod.cast_natCast hpPow]
      exact (ZMod.natCast_eq_zero_iff
        (1 - X.det * X.det).val p).2 hone_dvd
    exact zero_ne_one (hone_zero.symm.trans hone_cast)
  have hone : IsUnit (1 - X.det * X.det) := by
    simpa only [ZMod.natCast_zmod_val] using
      (ZMod.isUnit_iff_coprime (1 - X.det * X.det).val (p ^ k)).2
        ((Fact.out : Nat.Prime p).coprime_pow_of_not_dvd hone_not_dvd)
  have hzero : (1 - X.det * X.det) * (L.polarDeterminant : ZMod (p ^ k)) = 0 := by
    calc
      (1 - X.det * X.det) * (L.polarDeterminant : ZMod (p ^ k)) =
          (L.polarDeterminant : ZMod (p ^ k)) -
            X.det * (L.polarDeterminant : ZMod (p ^ k)) * X.det := by ring
      _ = 0 := sub_eq_zero.mpr hdet'.symm
  have hdisc_zero : (L.polarDeterminant : ZMod (p ^ k)) = 0 :=
    (IsUnit.mul_right_eq_zero hone).mp hzero
  have hdiv : (p ^ k : ℤ) ∣ L.polarDeterminant :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd L.polarDeterminant (p ^ k)).mp hdisc_zero
  have hk_le : k ≤ padicValInt p L.polarDeterminant := by
    rcases (padicValInt_dvd_iff (p := p) k L.polarDeterminant).mp hdiv with hz | hle
    · exact (ne_of_gt L.polarDeterminant_pos hz).elim
    · exact hle
  omega

theorem localPadicLatticeStabilizerReduction_mem_gramCongruenceSolutionMatrices
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (g : L.localPadicLatticeStabilizerSubgroup p) :
    (L.localPadicLatticeStabilizerReduction p k g).1 ∈
      gramCongruenceSolutionMatrices L p k := by
  apply (mem_gramCongruenceSolutionMatrices_iff (L := L) (p := p) (k := k)).2
  change (L.localPadicLatticeStabilizerReduction p k g).1ᵀ *
        L.polarGramMatrix.map (Int.castRingHom (ZMod (p ^ k))) *
        (L.localPadicLatticeStabilizerReduction p k g).1 =
      L.polarGramMatrix.map (Int.castRingHom (ZMod (p ^ k)))
  have hgram :
      L.polarGramMatrix.map (Int.castRingHom (ZMod (p ^ k))) =
        (2 : ZMod (p ^ k)) •
          L.pairingMatrix.map (Int.castRingHom (ZMod (p ^ k))) := by
    simpa [matrixMod, primePowModulus] using
      matrixMod_polarGramMatrix_eq_two_smul_pairingMatrix L
        (primePowModulus p k)
  rw [hgram]
  calc
    (L.localPadicLatticeStabilizerReduction p k g).1ᵀ *
          ((2 : ZMod (p ^ k)) •
            L.pairingMatrix.map (Int.castRingHom (ZMod (p ^ k)))) *
          (L.localPadicLatticeStabilizerReduction p k g).1 =
        (2 : ZMod (p ^ k)) •
          ((L.localPadicLatticeStabilizerReduction p k g).1ᵀ *
            L.pairingMatrix.map (Int.castRingHom (ZMod (p ^ k))) *
            (L.localPadicLatticeStabilizerReduction p k g).1) :=
      matrix_conj_smul _ _ _
    _ = (2 : ZMod (p ^ k)) •
        L.pairingMatrix.map (Int.castRingHom (ZMod (p ^ k))) := by
      rw [L.localPadicLatticeStabilizerReduction_preserves_form p k g]

/-- Forgetting invertibility embeds the reduction image into the raw Gram
congruence solution set. -/
def localPadicLatticeStabilizerReductionRangeToGramCongruenceSolutions
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)] :
    (L.localPadicLatticeStabilizerReduction p k).range →
      {X // X ∈ gramCongruenceSolutionMatrices L p k} :=
  fun u => ⟨u.1.1, by
    rcases u.2 with ⟨g, hg⟩
    rw [← hg]
    exact L.localPadicLatticeStabilizerReduction_mem_gramCongruenceSolutionMatrices
      p k g⟩

theorem localPadicLatticeStabilizerReductionRangeToGramCongruenceSolutions_injective
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)] :
    Function.Injective
      (L.localPadicLatticeStabilizerReductionRangeToGramCongruenceSolutions
        p k) := by
  intro u v huv
  apply Subtype.ext
  apply Units.ext
  exact congrArg Subtype.val huv

/-- The reduction image is no larger than the raw finite Gram congruence
solution set. Equality requires a separate lifting theorem. -/
theorem natCard_localPadicLatticeStabilizerReduction_range_le
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)] :
    Nat.card (L.localPadicLatticeStabilizerReduction p k).range ≤
      gramCongruenceSolutionCount L p k := by
  calc
    Nat.card (L.localPadicLatticeStabilizerReduction p k).range ≤
        Nat.card {X // X ∈ gramCongruenceSolutionMatrices L p k} :=
      Nat.card_le_card_of_injective
        (L.localPadicLatticeStabilizerReductionRangeToGramCongruenceSolutions
          p k)
        (L.localPadicLatticeStabilizerReductionRangeToGramCongruenceSolutions_injective
          p k)
    _ = gramCongruenceSolutionCount L p k := by
      simp [gramCongruenceSolutionCount, Nat.card_eq_fintype_card]

theorem continuous_localPadicLatticeStabilizerReduction
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)] :
    Continuous (L.localPadicLatticeStabilizerReduction p k) := by
  apply Units.continuous_iff.mpr
  have hval : Continuous (fun g :
      L.localPadicLatticeStabilizerSubgroup p =>
      (L.localPadicLatticeStabilizerReduction p k g).1) := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    exact (continuous_padicInt_toZModPow p k).comp
      (L.continuous_localPadicLatticeStabilizerIntegralGL_apply p i j)
  refine ⟨hval, ?_⟩
  simpa only [map_inv] using hval.comp continuous_inv

theorem isOpen_localPadicLatticeStabilizerReduction_ker
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)] :
    IsOpen ((L.localPadicLatticeStabilizerReduction p k).ker :
      Set (L.localPadicLatticeStabilizerSubgroup p)) := by
  change IsOpen
    ((L.localPadicLatticeStabilizerReduction p k) ⁻¹' ({1} : Set
      (GL (Fin n) (ZMod (p ^ k)))))
  exact (isOpen_discrete ({1} : Set (GL (Fin n) (ZMod (p ^ k))))).preimage
    (L.continuous_localPadicLatticeStabilizerReduction p k)

/-- The depth-`k` principal congruence subgroup of the integral local
stabilizer. -/
def localPadicPrincipalCongruenceSubgroup
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)] :
    Subgroup (L.localPadicLatticeStabilizerSubgroup p) :=
  (L.localPadicLatticeStabilizerReduction p k).ker

@[simp]
theorem mem_localPadicPrincipalCongruenceSubgroup_iff
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)]
    (g : L.localPadicLatticeStabilizerSubgroup p) :
    g ∈ L.localPadicPrincipalCongruenceSubgroup p k ↔
      ∀ i j, PadicInt.toZModPow k
        (L.localPadicLatticeStabilizerIntegralGL p g i j) =
          (1 : Matrix (Fin n) (Fin n) (ZMod (p ^ k))) i j := by
  change L.localPadicLatticeStabilizerReduction p k g = 1 ↔ _
  constructor
  · intro hg i j
    exact congrArg (fun u : GL (Fin n) (ZMod (p ^ k)) => u.1 i j) hg
  · intro hg
    apply Units.ext
    apply Matrix.ext
    intro i j
    exact hg i j

theorem isOpen_localPadicPrincipalCongruenceSubgroup
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)] :
    IsOpen (L.localPadicPrincipalCongruenceSubgroup p k :
      Set (L.localPadicLatticeStabilizerSubgroup p)) :=
  L.isOpen_localPadicLatticeStabilizerReduction_ker p k

/-- Principal congruence volume for the stabilizer-normalized reference Haar
measure. This does not determine the differential-form gauge scale. -/
theorem localPadicLatticeStabilizerHaarMeasure_principalCongruenceSubgroup
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)] :
    L.localPadicLatticeStabilizerHaarMeasure p
        (L.localPadicPrincipalCongruenceSubgroup p k :
          Set (L.localPadicLatticeStabilizerSubgroup p)) =
      (Nat.card ((L.localPadicLatticeStabilizerReduction p k).range) :
        ℝ≥0∞)⁻¹ := by
  exact L.localPadicLatticeStabilizerHaarMeasure_ker_eq_inv_natCard_range p
    (L.localPadicLatticeStabilizerReduction p k)
    (L.isOpen_localPadicPrincipalCongruenceSubgroup p k).measurableSet

/-- Every sigma-finite left-invariant measure on the concrete local group is
its stabilizer volume times the stabilizer-normalized Haar measure.  Thus a
source gauge calculation only has to compute one compact-open volume. -/
theorem localPadicHaarMeasure_eq_stabilizer_smul
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)]
    (μ : Measure (L.ConcreteLocalPadicOrthogonalGroup p))
    [SigmaFinite μ] [Measure.IsMulLeftInvariant μ] :
    μ = μ (L.localPadicLatticeStabilizerSubgroup p :
        Set (L.ConcreteLocalPadicOrthogonalGroup p)) •
      L.localPadicOrthogonalHaarMeasure p := by
  simpa [localPadicOrthogonalHaarMeasure] using
    (Measure.haarMeasure_unique μ
      (L.localPadicLatticeStabilizerPositiveCompacts p))

/-- The explicit Haar normalization whose integral stabilizer has volume
`2 * normalizedLocalDensity L p`.  The source gauge theorem must identify the
determinant-renormalized differential-form measure with this measure. -/
noncomputable def normalizedLocalDensityNormalizedLocalHaarMeasure
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    Measure (L.ConcreteLocalPadicOrthogonalGroup p) :=
  ENNReal.ofReal (2 * normalizedLocalDensity L p) •
    L.localPadicOrthogonalHaarMeasure p

instance normalizedLocalDensityNormalizedLocalHaarMeasure_isMulLeftInvariant
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    Measure.IsMulLeftInvariant
      (L.normalizedLocalDensityNormalizedLocalHaarMeasure p) := by
  unfold normalizedLocalDensityNormalizedLocalHaarMeasure
  infer_instance

theorem normalizedLocalDensityNormalizedLocalHaarMeasure_isHaarMeasure
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    Measure.IsHaarMeasure
      (L.normalizedLocalDensityNormalizedLocalHaarMeasure p) := by
  letI : Measure.IsHaarMeasure (L.localPadicOrthogonalHaarMeasure p) := by
    unfold localPadicOrthogonalHaarMeasure
    infer_instance
  unfold normalizedLocalDensityNormalizedLocalHaarMeasure
  apply Measure.IsHaarMeasure.smul
  · exact ENNReal.ofReal_ne_zero_iff.mpr
      (mul_pos (by norm_num) (normalizedLocalDensity_pos L p))
  · exact ENNReal.ofReal_ne_top

theorem normalizedLocalDensityNormalizedLocalHaarMeasure_stabilizer
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    L.normalizedLocalDensityNormalizedLocalHaarMeasure p
        (L.localPadicLatticeStabilizerSubgroup p :
          Set (L.ConcreteLocalPadicOrthogonalGroup p)) =
      ENNReal.ofReal (2 * normalizedLocalDensity L p) := by
  rw [normalizedLocalDensityNormalizedLocalHaarMeasure, Measure.smul_apply,
    L.localPadicOrthogonalHaarMeasure_stabilizer p, smul_eq_mul, mul_one]

/-- A sigma-finite invariant measure is the alpha-normalized local Haar
measure as soon as the source gauge calculation gives the required
compact-open stabilizer volume. -/
theorem localHaarMeasure_eq_normalizedLocalDensityNormalized_of_stabilizer_volume
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)]
    (μ : Measure (L.ConcreteLocalPadicOrthogonalGroup p))
    [SigmaFinite μ] [Measure.IsMulLeftInvariant μ]
    (hμ : μ (L.localPadicLatticeStabilizerSubgroup p :
        Set (L.ConcreteLocalPadicOrthogonalGroup p)) =
      ENNReal.ofReal (2 * normalizedLocalDensity L p)) :
    μ = L.normalizedLocalDensityNormalizedLocalHaarMeasure p := by
  rw [L.localPadicHaarMeasure_eq_stabilizer_smul p μ, hμ]
  rfl

end PositiveDefiniteIntegralLattice
