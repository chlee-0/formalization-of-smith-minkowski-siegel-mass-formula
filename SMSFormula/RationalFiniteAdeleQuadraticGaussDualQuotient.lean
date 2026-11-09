import SMSFormula.RationalFiniteAdeleQuadraticGaussDualCovolume

/-!
# The polar-dual finite quadratic Gauss integral as an exact quotient sum

This file applies the section-free finite-quotient Haar average to the raw
polar-dual additive carrier.  Multiplication by the exact polar matrix then
identifies its denominator quotient with the literal coordinate quotient by
the algebraic subgroup `m * C * Zhat^n`.

The raw coset mass stays `m^-n`, while the target quotient has exactly
`|polarDeterminant(L)| * m^n` elements.  No residue representatives, probability
renormalization, finite Gauss value, reciprocity phase, or Weil index are
introduced here.
-/

noncomputable section

open PositiveDefiniteIntegralLattice MeasureTheory Matrix Set
open scoped ENNReal

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

private noncomputable def quotientMapAddEquiv
    {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (e : A ≃+ B) (H : AddSubgroup A) :
    (A ⧸ H) ≃+ (B ⧸ H.map e.toAddMonoidHom) := by
  let f : A ⧸ H →+ B ⧸ H.map e.toAddMonoidHom :=
    QuotientAddGroup.map H (H.map e.toAddMonoidHom) e.toAddMonoidHom <| by
      intro x hx
      exact ⟨x, hx, rfl⟩
  let g : B ⧸ H.map e.toAddMonoidHom →+ A ⧸ H :=
    QuotientAddGroup.map (H.map e.toAddMonoidHom) H e.symm.toAddMonoidHom <| by
      rintro y ⟨x, hx, rfl⟩
      simpa using hx
  exact
    { toFun := f
      invFun := g
      left_inv := by
        intro q
        induction q using Quotient.inductionOn' with
        | _ x =>
          change (e.symm (e x) : A ⧸ H) = (x : A ⧸ H)
          rw [e.symm_apply_apply]
      right_inv := by
        intro q
        induction q using Quotient.inductionOn' with
        | _ x =>
          change (e (e.symm x) : B ⧸ H.map e.toAddMonoidHom) =
            (x : B ⧸ H.map e.toAddMonoidHom)
          rw [e.apply_symm_apply]
      map_add' := f.map_add }

@[simp]
private theorem quotientMapAddEquiv_mk
    {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (e : A ≃+ B) (H : AddSubgroup A) (x : A) :
    quotientMapAddEquiv e H (x : A ⧸ H) =
      (e x : B ⧸ H.map e.toAddMonoidHom) := by
  rfl

/-- The algebraic denominator subgroup `m * C * Zhat^n` in standard
integral finite-adelic coordinates. -/
def integralFiniteAdelePolarDenDilationAddSubgroup
    (L : PositiveDefiniteIntegralLattice n) (m : ℕ) :
    AddSubgroup (Fin n → IntegralFiniteAdele) :=
  ((integralFiniteAdelePolarMatrixEnd L).comp
    (integralFiniteAdeleCoordinateNatDilation n m)).range

/-- The polar matrix identifies the intrinsic polar-dual denominator quotient
with the literal coordinate quotient by `m * C * Zhat^n`. -/
noncomputable def finitePolarDualDenQuotientEquivIntegralCoordinates
    (L : PositiveDefiniteIntegralLattice n) (m : ℕ) :
    (FinitePolarDualAdeleVector L ⧸
      (integralFiniteAdeleCoordinateNatDilationToPolarDual L m).range) ≃+
      ((Fin n → IntegralFiniteAdele) ⧸
        integralFiniteAdelePolarDenDilationAddSubgroup L m) :=
  (quotientMapAddEquiv (finitePolarDualEquivIntegralCoordinates L)
    (integralFiniteAdeleCoordinateNatDilationToPolarDual L m).range).trans
      (QuotientAddGroup.quotientAddEquivOfEq
        (finitePolarDualEquivIntegralCoordinates_map_denDilation_range L m))

@[simp]
theorem finitePolarDualDenQuotientEquivIntegralCoordinates_mk
    (L : PositiveDefiniteIntegralLattice n) (m : ℕ)
    (x : FinitePolarDualAdeleVector L) :
    finitePolarDualDenQuotientEquivIntegralCoordinates L m
        (x : FinitePolarDualAdeleVector L ⧸
          (integralFiniteAdeleCoordinateNatDilationToPolarDual L m).range) =
      (finitePolarDualEquivIntegralCoordinates L x :
        (Fin n → IntegralFiniteAdele) ⧸
          integralFiniteAdelePolarDenDilationAddSubgroup L m) := by
  rfl

noncomputable instance finitePolarDualDenQuotientFintype
    (L : PositiveDefiniteIntegralLattice n) (m : ℕ) [NeZero m] :
    Fintype (FinitePolarDualAdeleVector L ⧸
      (integralFiniteAdeleCoordinateNatDilationToPolarDual L m).range) :=
  AddSubgroup.fintypeQuotientOfFiniteIndex

noncomputable instance integralFiniteAdelePolarDenQuotientFintype
    (L : PositiveDefiniteIntegralLattice n) (m : ℕ) [NeZero m] :
    Fintype ((Fin n → IntegralFiniteAdele) ⧸
      integralFiniteAdelePolarDenDilationAddSubgroup L m) :=
  Fintype.ofEquiv
    (FinitePolarDualAdeleVector L ⧸
      (integralFiniteAdeleCoordinateNatDilationToPolarDual L m).range)
    (finitePolarDualDenQuotientEquivIntegralCoordinates L m).toEquiv

/-- Exact cardinality of the literal coordinate quotient by
`m * C * Zhat^n`. -/
theorem integralFiniteAdelePolarDenQuotient_card
    (L : PositiveDefiniteIntegralLattice n) (m : ℕ) [NeZero m] :
    Fintype.card ((Fin n → IntegralFiniteAdele) ⧸
      integralFiniteAdelePolarDenDilationAddSubgroup L m) =
        L.polarDeterminant.natAbs * m ^ n := by
  rw [← Nat.card_eq_fintype_card]
  rw [← Nat.card_congr
    (finitePolarDualDenQuotientEquivIntegralCoordinates L m).toEquiv]
  rw [← AddSubgroup.index_eq_card]
  exact finitePolarDualDenDilationRange_index L m

noncomputable instance finitePolarDualAddHaarMeasure_isFinite
    (L : PositiveDefiniteIntegralLattice n) :
    IsFiniteMeasure (finitePolarDualAddHaarMeasure L) := by
  constructor
  rw [finitePolarDualAddHaarMeasure_univ_eq_natAbs_polarDeterminant]
  exact ENNReal.natCast_lt_top _

instance finitePolarDualMeasurableAdd
    (L : PositiveDefiniteIntegralLattice n) :
    MeasurableAdd₂ (FinitePolarDualAdeleVector L) := by
  constructor
  show Measurable
    (fun p : FinitePolarDualAdeleVector L × FinitePolarDualAdeleVector L ↦
      p.1 + p.2)
  have hfst : Measurable
      (fun p : FinitePolarDualAdeleVector L × FinitePolarDualAdeleVector L ↦
        (p.1 : Fin n → RationalFiniteAdele)) :=
    measurable_subtype_coe.comp measurable_fst
  have hsnd : Measurable
      (fun p : FinitePolarDualAdeleVector L × FinitePolarDualAdeleVector L ↦
        (p.2 : Fin n → RationalFiniteAdele)) :=
    measurable_subtype_coe.comp measurable_snd
  exact Measurable.subtype_mk (hfst.add hsnd)

/-- A function on the raw polar-dual lattice that is periodic modulo the
embedded denominator lattice integrates to the exact quotient sum. -/
theorem finitePolarDual_integral_periodic_eq_denQuotientSum
    (L : PositiveDefiniteIntegralLattice n) (m : ℕ) [NeZero m]
    (f : FinitePolarDualAdeleVector L → ℂ)
    (hperiod : ∀ x z,
      z ∈ (integralFiniteAdeleCoordinateNatDilationToPolarDual L m).range →
        f (x + z) = f x) :
    ∫ x, f x ∂finitePolarDualAddHaarMeasure L =
      (((m : ℝ) ^ n : ℂ)⁻¹) *
        ∑ q, addQuotientPeriodicLift
          (integralFiniteAdeleCoordinateNatDilationToPolarDual L m).range
          f hperiod q := by
  have h := integral_comp_quotientAddGroupMk_eq_measure_mul_sum
    (finitePolarDualAddHaarMeasure L)
    (integralFiniteAdeleCoordinateNatDilationToPolarDual L m).range
    (measurableSet_integralFiniteAdeleCoordinateNatDilationToPolarDual_range
      L m (NeZero.ne m))
    (addQuotientPeriodicLift
      (integralFiniteAdeleCoordinateNatDilationToPolarDual L m).range
      f hperiod)
  rw [finitePolarDualAddHaarMeasure_denDilation_range L m (NeZero.ne m)] at h
  simpa [ENNReal.toReal_pow, ENNReal.toReal_inv, inv_pow] using h

private noncomputable instance rationalDenNeZero (t : ℚ) : NeZero t.den :=
  ⟨t.den_nz⟩

/-- Exact finite quotient formula for the polar-dual Gauss integral on its
intrinsic polar-dual carrier. -/
theorem rationalFiniteAdeleDualQuadraticGaussIntegral_eq_denQuotientSum
    (L : PositiveDefiniteIntegralLattice n) (t : ℚ) :
    L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleDualQuadraticGaussIntegral t =
      (((t.den : ℝ) ^ n : ℂ)⁻¹) *
        ∑ q, addQuotientPeriodicLift
          (integralFiniteAdeleCoordinateNatDilationToPolarDual L t.den).range
          (rationalFiniteAdelePolarDualQuadraticPhase L t)
          (rationalFiniteAdelePolarDualQuadraticPhase_add_denDilation L t) q := by
  rw [rationalFiniteAdeleDualQuadraticGaussIntegral_eq_polarDualQuadraticPhase]
  exact finitePolarDual_integral_periodic_eq_denQuotientSum L t.den
    (rationalFiniteAdelePolarDualQuadraticPhase L t)
    (rationalFiniteAdelePolarDualQuadraticPhase_add_denDilation L t)

/-- The polar-dual quadratic phase transported section-freely to the literal
quotient by the algebraic subgroup `t.den * C * Zhat^n`. -/
noncomputable def rationalFiniteAdelePolarDualQuadraticPhaseOnPolarMatrixQuotient
    (L : PositiveDefiniteIntegralLattice n) (t : ℚ) :
    ((Fin n → IntegralFiniteAdele) ⧸
      integralFiniteAdelePolarDenDilationAddSubgroup L t.den) → ℂ :=
  fun q ↦ addQuotientPeriodicLift
    (integralFiniteAdeleCoordinateNatDilationToPolarDual L t.den).range
    (rationalFiniteAdelePolarDualQuadraticPhase L t)
    (rationalFiniteAdelePolarDualQuadraticPhase_add_denDilation L t)
    ((finitePolarDualDenQuotientEquivIntegralCoordinates L t.den).symm q)

@[simp]
theorem rationalFiniteAdelePolarDualQuadraticPhaseOnPolarMatrixQuotient_mk
    (L : PositiveDefiniteIntegralLattice n) (t : ℚ)
    (x : FinitePolarDualAdeleVector L) :
    rationalFiniteAdelePolarDualQuadraticPhaseOnPolarMatrixQuotient L t
        (finitePolarDualEquivIntegralCoordinates L x :
          (Fin n → IntegralFiniteAdele) ⧸
            integralFiniteAdelePolarDenDilationAddSubgroup L t.den) =
      rationalFiniteAdelePolarDualQuadraticPhase L t x := by
  change addQuotientPeriodicLift
      (integralFiniteAdeleCoordinateNatDilationToPolarDual L t.den).range
      (rationalFiniteAdelePolarDualQuadraticPhase L t)
      (rationalFiniteAdelePolarDualQuadraticPhase_add_denDilation L t)
      ((finitePolarDualDenQuotientEquivIntegralCoordinates L t.den).symm
        (finitePolarDualDenQuotientEquivIntegralCoordinates L t.den
          (x : FinitePolarDualAdeleVector L ⧸
            (integralFiniteAdeleCoordinateNatDilationToPolarDual L t.den).range))) = _
  rw [(finitePolarDualDenQuotientEquivIntegralCoordinates L t.den).symm_apply_apply]
  rfl

/-- Exact finite quotient formula for the polar-dual Gauss integral, written
on the coordinate quotient by the literal range `t.den * C * Zhat^n`. -/
theorem rationalFiniteAdeleDualQuadraticGaussIntegral_eq_polarMatrixQuotientSum
    (L : PositiveDefiniteIntegralLattice n) (t : ℚ) :
    L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleDualQuadraticGaussIntegral t =
      (((t.den : ℝ) ^ n : ℂ)⁻¹) *
        ∑ q, rationalFiniteAdelePolarDualQuadraticPhaseOnPolarMatrixQuotient
          L t q := by
  rw [rationalFiniteAdeleDualQuadraticGaussIntegral_eq_denQuotientSum]
  congr 1
  exact (Equiv.sum_comp
    (finitePolarDualDenQuotientEquivIntegralCoordinates L t.den).symm.toEquiv
    (addQuotientPeriodicLift
      (integralFiniteAdeleCoordinateNatDilationToPolarDual L t.den).range
      (rationalFiniteAdelePolarDualQuadraticPhase L t)
      (rationalFiniteAdelePolarDualQuadraticPhase_add_denDilation L t))).symm

end RationalQuadraticSpaceMatrix
