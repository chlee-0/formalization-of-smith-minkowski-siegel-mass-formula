import SMSFormula.PadicSpecialOrthogonalDifferentialStabilizer

/-!
# Principal congruence subgroups for corrected p-adic differential Haar

The corrected integral special-orthogonal stabilizer and the original
determinant-one kernel in the ordinary integral stabilizer contain exactly the
same matrices.  This file upgrades that identification to a continuous
multiplicative equivalence and transports the existing finite congruence
reduction through it.

The resulting principal-congruence kernel has corrected differential mass
equal to the full stabilizer volume divided by the cardinality of the actual
finite reduction image.  No lifting theorem for the determinant-one finite
container, coordinate-volume calculation, or comparison with normalized
reference Haar is used.
-/

noncomputable section

open MeasureTheory
open Matrix
open TopologicalSpace
open scoped ENNReal Matrix

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

local instance
    localPadicSpecialOrthogonalDifferentialCongruenceMeasurableSpace
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    MeasurableSpace
      (specialFormPreservingMatrixSubgroup
        (L.rationalFormMatrix.map (algebraMap ℚ ℚ_[p]))) :=
  borel _

local instance
    localPadicSpecialOrthogonalDifferentialCongruenceBorelSpace
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    BorelSpace
      (specialFormPreservingMatrixSubgroup
        (L.rationalFormMatrix.map (algebraMap ℚ ℚ_[p]))) :=
  ⟨rfl⟩

/-- The original determinant-one integral stabilizer element having the
same underlying matrix as an element of the corrected direct stabilizer. -/
def localPadicSpecialOrthogonalDifferentialStabilizerToHistorical
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)]
    (g : L.localPadicSpecialOrthogonalDifferentialStabilizerSubgroup p) :
    L.localPadicSpecialOrthogonalLatticeStabilizerSubgroup p := by
  let go : L.ConcreteLocalPadicOrthogonalGroup p := ⟨g.1.1, by
    have hpres := g.1.1.2
    change
      g.1.1.1.1ᵀ * L.pairingMatrix_padicField p * g.1.1.1.1 =
        L.pairingMatrix_padicField p
    let hmatrix :=
      L.rationalFormMatrix_map_padic_eq_pairingMatrix_padicField p
    calc
      g.1.1.1.1ᵀ * L.pairingMatrix_padicField p * g.1.1.1.1 =
          g.1.1.1.1ᵀ *
              L.rationalFormMatrix.map (algebraMap ℚ ℚ_[p]) *
              g.1.1.1.1 :=
        congrArg (fun F ↦ g.1.1.1.1ᵀ * F * g.1.1.1.1) hmatrix.symm
      _ = L.rationalFormMatrix.map (algebraMap ℚ ℚ_[p]) := hpres
      _ = L.pairingMatrix_padicField p := hmatrix⟩
  let gi : L.localPadicLatticeStabilizerSubgroup p := ⟨go, g.2⟩
  exact
    ⟨gi,
      (L.mem_localPadicSpecialOrthogonalLatticeStabilizerSubgroup_iff
        p gi).mpr <|
        (mem_specialFormPreservingMatrixSubgroup_iff
          (L.rationalFormMatrix.map (algebraMap ℚ ℚ_[p])) g.1).mp g.1.2⟩

@[simp]
theorem
    localPadicSpecialOrthogonalDifferentialStabilizerToHistorical_units
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)]
    (g : L.localPadicSpecialOrthogonalDifferentialStabilizerSubgroup p) :
    (L.localPadicSpecialOrthogonalDifferentialStabilizerToHistorical p g).1.1.1 =
      g.1.1 :=
  rfl

/-- Regard an original determinant-one integral stabilizer element as an
element of the corrected direct stabilizer, without changing its underlying
matrix. -/
def localPadicSpecialOrthogonalDifferentialStabilizerFromHistorical
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)]
    (h : L.localPadicSpecialOrthogonalLatticeStabilizerSubgroup p) :
    L.localPadicSpecialOrthogonalDifferentialStabilizerSubgroup p := by
  let gform :
      formPreservingMatrixSubgroup
        (L.rationalFormMatrix.map (algebraMap ℚ ℚ_[p])) :=
    ⟨h.1.1.1, by
      have hpres := h.1.1.2
      change
        h.1.1.1.1ᵀ *
            L.rationalFormMatrix.map (algebraMap ℚ ℚ_[p]) *
            h.1.1.1.1 =
          L.rationalFormMatrix.map (algebraMap ℚ ℚ_[p])
      let hmatrix :=
        L.rationalFormMatrix_map_padic_eq_pairingMatrix_padicField p
      calc
        h.1.1.1.1ᵀ *
              L.rationalFormMatrix.map (algebraMap ℚ ℚ_[p]) *
              h.1.1.1.1 =
            h.1.1.1.1ᵀ * L.pairingMatrix_padicField p * h.1.1.1.1 :=
          congrArg (fun F ↦ h.1.1.1.1ᵀ * F * h.1.1.1.1) hmatrix
        _ = L.pairingMatrix_padicField p := hpres
        _ = L.rationalFormMatrix.map (algebraMap ℚ ℚ_[p]) := hmatrix.symm⟩
  let gspecial :
      specialFormPreservingMatrixSubgroup
        (L.rationalFormMatrix.map (algebraMap ℚ ℚ_[p])) :=
    ⟨gform, by
      rw [mem_specialFormPreservingMatrixSubgroup_iff]
      exact
        (L.mem_localPadicSpecialOrthogonalLatticeStabilizerSubgroup_iff
          p h.1).mp h.2⟩
  exact
    ⟨gspecial,
      (L.mem_localPadicSpecialOrthogonalDifferentialStabilizerSubgroup_iff_exists_historical
        p gspecial).mpr ⟨h, rfl⟩⟩

@[simp]
theorem
    localPadicSpecialOrthogonalDifferentialStabilizerFromHistorical_units
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)]
    (h : L.localPadicSpecialOrthogonalLatticeStabilizerSubgroup p) :
    (L.localPadicSpecialOrthogonalDifferentialStabilizerFromHistorical p h).1.1.1 =
      h.1.1.1 :=
  rfl

/-- The direct corrected stabilizer and the original determinant-one
stabilizer are multiplicatively equivalent by their common underlying
matrices. -/
def localPadicSpecialOrthogonalDifferentialStabilizerMulEquiv
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    L.localPadicSpecialOrthogonalDifferentialStabilizerSubgroup p ≃*
      L.localPadicSpecialOrthogonalLatticeStabilizerSubgroup p where
  toFun :=
    L.localPadicSpecialOrthogonalDifferentialStabilizerToHistorical p
  invFun :=
    L.localPadicSpecialOrthogonalDifferentialStabilizerFromHistorical p
  left_inv g := by
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    exact
      L.localPadicSpecialOrthogonalDifferentialStabilizerToHistorical_units
        p g
  right_inv h := by
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    exact
      L.localPadicSpecialOrthogonalDifferentialStabilizerToHistorical_units
        p
        (L.localPadicSpecialOrthogonalDifferentialStabilizerFromHistorical
          p h)
  map_mul' g h := by
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    calc
      (L.localPadicSpecialOrthogonalDifferentialStabilizerToHistorical
            p (g * h)).1.1.1 =
          (g * h).1.1 :=
        L.localPadicSpecialOrthogonalDifferentialStabilizerToHistorical_units
          p (g * h)
      _ =
          (g.1.1 : (Matrix (Fin n) (Fin n) ℚ_[p])ˣ) *
            (h.1.1 : (Matrix (Fin n) (Fin n) ℚ_[p])ˣ) := rfl
      _ =
          (L.localPadicSpecialOrthogonalDifferentialStabilizerToHistorical
              p g).1.1.1 *
            (L.localPadicSpecialOrthogonalDifferentialStabilizerToHistorical
              p h).1.1.1 :=
        congrArg₂ (· * ·)
          (L.localPadicSpecialOrthogonalDifferentialStabilizerToHistorical_units
            p g).symm
          (L.localPadicSpecialOrthogonalDifferentialStabilizerToHistorical_units
            p h).symm
      _ =
          (L.localPadicSpecialOrthogonalDifferentialStabilizerToHistorical
              p g *
            L.localPadicSpecialOrthogonalDifferentialStabilizerToHistorical
              p h).1.1.1 := rfl

/-- The common-underlying-matrix equivalence is a homeomorphism. -/
def localPadicSpecialOrthogonalDifferentialStabilizerHomeomorph
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    L.localPadicSpecialOrthogonalDifferentialStabilizerSubgroup p ≃ₜ
      L.localPadicSpecialOrthogonalLatticeStabilizerSubgroup p where
  toEquiv :=
    (L.localPadicSpecialOrthogonalDifferentialStabilizerMulEquiv p).toEquiv
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    change Continuous
      (fun g :
          L.localPadicSpecialOrthogonalDifferentialStabilizerSubgroup p ↦
        (g.1.1 : (Matrix (Fin n) (Fin n) ℚ_[p])ˣ))
    fun_prop
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    fun_prop

/-- The direct corrected stabilizer and the original determinant-one
stabilizer are continuously multiplicatively equivalent. -/
def localPadicSpecialOrthogonalDifferentialStabilizerContinuousMulEquiv
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    L.localPadicSpecialOrthogonalDifferentialStabilizerSubgroup p ≃ₜ*
      L.localPadicSpecialOrthogonalLatticeStabilizerSubgroup p :=
  ContinuousMulEquiv.mk'
    (L.localPadicSpecialOrthogonalDifferentialStabilizerHomeomorph p)
    (L.localPadicSpecialOrthogonalDifferentialStabilizerMulEquiv p).map_mul

/-! ## Transported finite congruence reduction -/

/-- Finite reduction on the direct corrected stabilizer, transported through
the continuous common-matrix equivalence. -/
def localPadicSpecialOrthogonalDifferentialStabilizerReduction
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)] :
    L.localPadicSpecialOrthogonalDifferentialStabilizerSubgroup p →*
      L.localPadicSpecialOrthogonalLatticeStabilizerReductionRangeSubgroup
        p k :=
  (L.localPadicSpecialOrthogonalLatticeStabilizerReduction p k).comp
    (L.localPadicSpecialOrthogonalDifferentialStabilizerContinuousMulEquiv
      p).toMonoidHom

/-- The original determinant-one finite reduction is continuous. -/
theorem continuous_localPadicSpecialOrthogonalLatticeStabilizerReduction
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)] :
    Continuous
      (L.localPadicSpecialOrthogonalLatticeStabilizerReduction p k) := by
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  exact
    (L.continuous_localPadicLatticeStabilizerReduction p k).comp
      continuous_subtype_val

/-- The transported finite reduction on the direct corrected stabilizer is
continuous. -/
theorem
    continuous_localPadicSpecialOrthogonalDifferentialStabilizerReduction
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)] :
    Continuous
      (L.localPadicSpecialOrthogonalDifferentialStabilizerReduction p k) :=
  (L.continuous_localPadicSpecialOrthogonalLatticeStabilizerReduction p k).comp
    (L.localPadicSpecialOrthogonalDifferentialStabilizerContinuousMulEquiv
      p).continuous

/-- The depth-`k` principal congruence subgroup of the direct corrected
integral special-orthogonal stabilizer. -/
def localPadicSpecialOrthogonalDifferentialPrincipalCongruenceSubgroup
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)] :
    Subgroup
      (L.localPadicSpecialOrthogonalDifferentialStabilizerSubgroup p) :=
  (L.localPadicSpecialOrthogonalDifferentialStabilizerReduction p k).ker

/-- Each transported principal congruence subgroup is open. -/
theorem
    isOpen_localPadicSpecialOrthogonalDifferentialPrincipalCongruenceSubgroup
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)] :
    IsOpen
      (L.localPadicSpecialOrthogonalDifferentialPrincipalCongruenceSubgroup
          p k :
        Set
          (L.localPadicSpecialOrthogonalDifferentialStabilizerSubgroup p)) := by
  change IsOpen
    ((L.localPadicSpecialOrthogonalDifferentialStabilizerReduction p k) ⁻¹'
      ({1} : Set
        (L.localPadicSpecialOrthogonalLatticeStabilizerReductionRangeSubgroup
          p k)))
  exact
    (isOpen_discrete
      ({1} : Set
        (L.localPadicSpecialOrthogonalLatticeStabilizerReductionRangeSubgroup
          p k))).preimage
      (L.continuous_localPadicSpecialOrthogonalDifferentialStabilizerReduction
        p k)

/-- Each transported principal congruence subgroup is measurable. -/
theorem
    measurableSet_localPadicSpecialOrthogonalDifferentialPrincipalCongruenceSubgroup
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)] :
    MeasurableSet
      (L.localPadicSpecialOrthogonalDifferentialPrincipalCongruenceSubgroup
          p k :
        Set
          (L.localPadicSpecialOrthogonalDifferentialStabilizerSubgroup p)) :=
  (L.isOpen_localPadicSpecialOrthogonalDifferentialPrincipalCongruenceSubgroup
    p k).measurableSet

/-! ## Corrected differential mass on the direct stabilizer -/

/-- The corrected differential Haar measure restricted to the direct integral
special-orthogonal stabilizer. -/
def localPadicSpecialOrthogonalDifferentialStabilizerMeasure
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    Measure
      (L.localPadicSpecialOrthogonalDifferentialStabilizerSubgroup p) :=
  Measure.comap
    (fun g :
        L.localPadicSpecialOrthogonalDifferentialStabilizerSubgroup p ↦
      (g :
        specialFormPreservingMatrixSubgroup
          (L.rationalFormMatrix.map (algebraMap ℚ ℚ_[p]))))
    (padicCayleySpecialOrthogonalDifferentialMeasure
      p n L.rationalFormMatrix L.rationalFormMatrix_det_ne_zero)

/-- The direct corrected stabilizer has the inherited subtype measurable
space. -/
theorem
    localPadicSpecialOrthogonalDifferentialStabilizerMeasurableSpace_eq
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    (inferInstance :
      MeasurableSpace
        (L.localPadicSpecialOrthogonalDifferentialStabilizerSubgroup p)) =
      (@Subtype.instMeasurableSpace
        (specialFormPreservingMatrixSubgroup
          (L.rationalFormMatrix.map (algebraMap ℚ ℚ_[p])))
        (fun g ↦
          g ∈
            L.localPadicSpecialOrthogonalDifferentialStabilizerSubgroup p)
        (inferInstance :
          MeasurableSpace
            (specialFormPreservingMatrixSubgroup
              (L.rationalFormMatrix.map (algebraMap ℚ ℚ_[p]))))) :=
  rfl

/-- The total corrected differential mass on the direct stabilizer is its
literal ambient stabilizer volume. -/
@[simp]
theorem localPadicSpecialOrthogonalDifferentialStabilizerMeasure_univ
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    L.localPadicSpecialOrthogonalDifferentialStabilizerMeasure p Set.univ =
      L.localPadicSpecialOrthogonalDifferentialStabilizerVolume p := by
  change
    (Measure.comap
      (fun g :
          L.localPadicSpecialOrthogonalDifferentialStabilizerSubgroup p ↦
        (g :
          specialFormPreservingMatrixSubgroup
            (L.rationalFormMatrix.map (algebraMap ℚ ℚ_[p]))))
      (padicCayleySpecialOrthogonalDifferentialMeasure
        p n L.rationalFormMatrix L.rationalFormMatrix_det_ne_zero)) Set.univ =
      _
  rw [subgroup_comap_measure_univ_eq_of_subtype_mspace
    (L.localPadicSpecialOrthogonalDifferentialStabilizerSubgroup p)
    (L.localPadicSpecialOrthogonalDifferentialStabilizerMeasurableSpace_eq p)
    (L.isOpen_localPadicSpecialOrthogonalDifferentialStabilizerSubgroup
      p).measurableSet]
  rfl

/-- The corrected differential measure restricted to the direct integral
stabilizer remains left invariant. -/
instance
    localPadicSpecialOrthogonalDifferentialStabilizerMeasure_isMulLeftInvariant
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    Measure.IsMulLeftInvariant
      (L.localPadicSpecialOrthogonalDifferentialStabilizerMeasure p) := by
  let F := L.rationalFormMatrix
  have hFsymm : F.IsSymm := L.form_symm.map _
  have hF : F.det ≠ 0 := L.rationalFormMatrix_det_ne_zero
  letI : Measure.IsMulLeftInvariant
      (padicCayleySpecialOrthogonalDifferentialMeasure p n F hF) :=
    padicCayleySpecialOrthogonalDifferentialMeasure_isMulLeftInvariant
      p n F hFsymm hF
  exact subgroup_comap_measure_isMulLeftInvariant_of_subtype_mspace
    (L.localPadicSpecialOrthogonalDifferentialStabilizerSubgroup p)
    (L.localPadicSpecialOrthogonalDifferentialStabilizerMeasurableSpace_eq p)
    (L.isOpen_localPadicSpecialOrthogonalDifferentialStabilizerSubgroup
      p).measurableSet

/-- Finite-index Haar algebra for an arbitrary measurable reduction kernel in
the direct corrected stabilizer.  The cardinality is that of the actual image
of the supplied reduction homomorphism. -/
theorem
    localPadicSpecialOrthogonalDifferentialStabilizerMeasure_ker_eq_volume_mul_inv_natCard_range
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)]
    {Q : Type*} [Group Q] [Finite Q]
    (f :
      L.localPadicSpecialOrthogonalDifferentialStabilizerSubgroup p →* Q)
    (hker : MeasurableSet
      (f.ker :
        Set
          (L.localPadicSpecialOrthogonalDifferentialStabilizerSubgroup p))) :
    L.localPadicSpecialOrthogonalDifferentialStabilizerMeasure p
        (f.ker :
          Set
            (L.localPadicSpecialOrthogonalDifferentialStabilizerSubgroup p)) =
      L.localPadicSpecialOrthogonalDifferentialStabilizerVolume p *
        (Nat.card f.range : ℝ≥0∞)⁻¹ := by
  letI : f.ker.FiniteIndex := inferInstance
  have hindex := Subgroup.index_mul_measure f.ker hker
    (L.localPadicSpecialOrthogonalDifferentialStabilizerMeasure p)
  rw [Subgroup.index_ker,
    L.localPadicSpecialOrthogonalDifferentialStabilizerMeasure_univ p] at hindex
  have hc : (Nat.card f.range : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (Nat.card_pos : 0 < Nat.card f.range).ne'
  have hctop : (Nat.card f.range : ℝ≥0∞) ≠ ⊤ :=
    ENNReal.natCast_ne_top _
  calc
    L.localPadicSpecialOrthogonalDifferentialStabilizerMeasure p
          (f.ker :
            Set
              (L.localPadicSpecialOrthogonalDifferentialStabilizerSubgroup
                p)) =
        1 *
          L.localPadicSpecialOrthogonalDifferentialStabilizerMeasure p
            (f.ker :
              Set
                (L.localPadicSpecialOrthogonalDifferentialStabilizerSubgroup
                  p)) :=
      (one_mul _).symm
    _ =
        ((Nat.card f.range : ℝ≥0∞) *
            (Nat.card f.range : ℝ≥0∞)⁻¹) *
          L.localPadicSpecialOrthogonalDifferentialStabilizerMeasure p
            (f.ker :
              Set
                (L.localPadicSpecialOrthogonalDifferentialStabilizerSubgroup
                  p)) := by
      rw [ENNReal.mul_inv_cancel hc hctop]
    _ =
        (Nat.card f.range : ℝ≥0∞)⁻¹ *
          ((Nat.card f.range : ℝ≥0∞) *
            L.localPadicSpecialOrthogonalDifferentialStabilizerMeasure p
              (f.ker :
                Set
                  (L.localPadicSpecialOrthogonalDifferentialStabilizerSubgroup
                    p))) := by
      ac_rfl
    _ =
        (Nat.card f.range : ℝ≥0∞)⁻¹ *
          L.localPadicSpecialOrthogonalDifferentialStabilizerVolume p := by
      rw [hindex]
    _ =
        L.localPadicSpecialOrthogonalDifferentialStabilizerVolume p *
          (Nat.card f.range : ℝ≥0∞)⁻¹ :=
      mul_comm _ _

/-- The corrected differential mass of the depth-`k` direct principal
congruence subgroup is the full stabilizer volume divided by the cardinality
of the actual finite special reduction image. -/
theorem
    localPadicSpecialOrthogonalDifferentialPrincipalCongruenceSubgroup_measure
    (L : PositiveDefiniteIntegralLattice n) (p k : ℕ) [Fact (Nat.Prime p)] :
    L.localPadicSpecialOrthogonalDifferentialStabilizerMeasure p
        (L.localPadicSpecialOrthogonalDifferentialPrincipalCongruenceSubgroup
            p k :
          Set
            (L.localPadicSpecialOrthogonalDifferentialStabilizerSubgroup p)) =
      L.localPadicSpecialOrthogonalDifferentialStabilizerVolume p *
        (Nat.card
          (L.localPadicSpecialOrthogonalDifferentialStabilizerReduction
            p k).range : ℝ≥0∞)⁻¹ := by
  exact
    L.localPadicSpecialOrthogonalDifferentialStabilizerMeasure_ker_eq_volume_mul_inv_natCard_range
      p
      (L.localPadicSpecialOrthogonalDifferentialStabilizerReduction p k)
      (L.measurableSet_localPadicSpecialOrthogonalDifferentialPrincipalCongruenceSubgroup
        p k)

end PositiveDefiniteIntegralLattice
