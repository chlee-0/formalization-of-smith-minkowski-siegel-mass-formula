import SMSFormula.RationalAdeleFiniteLocalTruncation
import SMSFormula.RationalFiniteAdeleQuadraticGaussRectangularQuotient

/-!
# The level-`m` congruence measure is a residue count

The finite local integral is an explicit limit of level-`m` congruence measures.  This
file turns each of those measures into the arithmetic count it is classically: the number
of residue vectors mod `m` solving `Q(z) = M`, divided by `m^n`.

Everything is existing: the form matrix is an integer matrix, the existing polarization
makes the congruence indicator periodic modulo the `m`-dilation, the existing
section-free quotient averaging turns the integral into a finite quotient sum, and the
existing residue model `(ZMod m)^n ~ Zhat^n / m Zhat^n` reindexes it.  No representative of
any quotient is chosen.

Negative scope: this identifies one truncation.  No Euler product over places is asserted,
the limit is not evaluated in closed form, and no comparison with the representation number
follows.
-/

noncomputable section

set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 1000000

open MeasureTheory RationalQuadraticSpaceMatrix Matrix

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- The existing integral quadratic form reduced modulo `m`. -/
def zmodQuadForm (L : PositiveDefiniteIntegralLattice n) (m : ℕ) (z : Fin n → ZMod m) : ZMod m :=
  ∑ i, ∑ j, z i * ((L.pairingMatrix i j : ℤ) : ZMod m) * z j

theorem zmodQuadForm_intCast (L : PositiveDefiniteIntegralLattice n) (m : ℕ) (z : Fin n → ℤ) :
    L.zmodQuadForm m (fun i => ((z i : ℤ) : ZMod m)) = ((L.quadForm z : ℤ) : ZMod m) := by
  rw [L.quadForm_eq_dotProduct, zmodQuadForm]
  simp only [dotProduct, Matrix.mulVec, Int.cast_sum, Int.cast_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- The adelic quadratic value at an integer vector is the integer value. -/
theorem finiteAdelicQuadraticFormValue_intVector (L : PositiveDefiniteIntegralLattice n) (z : Fin n → ℤ) :
    L.rationalQuadraticSpaceMatrix.finiteAdelicQuadraticFormValue
        (fun i => algebraMap ℚ RationalFiniteAdele ((z i : ℤ) : ℚ)) =
      algebraMap ℚ RationalFiniteAdele ((L.quadForm z : ℤ) : ℚ) := by
  rw [L.quadForm_eq_dotProduct]
  simp only [RationalQuadraticSpaceMatrix.finiteAdelicQuadraticFormValue,
    RationalQuadraticSpaceMatrix.finiteAdelicFormMatrix, rationalQuadraticSpaceMatrix,
    rationalFormMatrix, Matrix.map_apply, Matrix.mulVec, dotProduct, eq_intCast]
  push_cast
  ring

/-- Divisibility criterion for the indicator at a rational multiple. -/
theorem integralIndicator_intDiv (m : ℕ) (hm : m ≠ 0) (k : ℤ) :
    rationalFiniteAdeleIntegralIndicator
        (algebraMap ℚ RationalFiniteAdele ((m : ℚ))⁻¹ *
          algebraMap ℚ RationalFiniteAdele ((k : ℤ) : ℚ)) =
      if ((m : ℤ)) ∣ k then 1 else 0 := by
  have hmq : ((m : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr hm
  have hval : algebraMap ℚ RationalFiniteAdele ((m : ℚ))⁻¹ *
      algebraMap ℚ RationalFiniteAdele ((k : ℤ) : ℚ) =
      algebraMap ℚ RationalFiniteAdele (((k : ℤ) : ℚ) / (m : ℚ)) := by
    rw [← map_mul]
    congr 1
    field_simp
  rw [hval]
  by_cases hd : ((m : ℤ)) ∣ k
  · obtain ⟨c, rfl⟩ := hd
    have hq : (((m : ℤ) * c : ℤ) : ℚ) / (m : ℚ) = ((c : ℤ) : ℚ) := by
      push_cast
      field_simp
    rw [hq, if_pos ⟨c, rfl⟩]
    exact rationalFiniteAdeleIntegralIndicator_of_mem
      ((rational_mem_integralFiniteAdeleSubring_iff ((c : ℤ) : ℚ)).mpr ⟨c, by simp⟩)
  · rw [if_neg hd]
    refine rationalFiniteAdeleIntegralIndicator_of_not_mem ?_
    intro hmem
    obtain ⟨c, hc⟩ := (rational_mem_integralFiniteAdeleSubring_iff _).mp hmem
    rw [eq_intCast] at hc
    apply hd
    refine ⟨c, ?_⟩
    have hq : ((k : ℤ) : ℚ) = ((m : ℤ) : ℚ) * ((c : ℤ) : ℚ) := by
      rw [hc]
      push_cast
      field_simp
    exact_mod_cast hq

/-! ## The congruence indicator and its periodicity -/

private theorem finiteAdelicQuadraticFormValue_nsmul'
    (V : RationalQuadraticSpaceMatrix n) (m : ℕ) (x : Fin n → RationalFiniteAdele) :
    V.finiteAdelicQuadraticFormValue (m • x) =
      (m : RationalFiniteAdele) ^ 2 * V.finiteAdelicQuadraticFormValue x := by
  simp only [RationalQuadraticSpaceMatrix.finiteAdelicQuadraticFormValue, Matrix.mulVec,
    dotProduct, Pi.smul_apply, nsmul_eq_mul, Finset.mul_sum]
  ring_nf

private theorem dotProduct_polar_nsmul
    (V : RationalQuadraticSpaceMatrix n) (m : ℕ) (x u : Fin n → RationalFiniteAdele) :
    dotProduct x (V.finiteAdelicPolarMatrix.mulVec (m • u)) =
      (m : RationalFiniteAdele) * dotProduct x (V.finiteAdelicPolarMatrix.mulVec u) := by
  simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, nsmul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- The level-`m` congruence indicator on the integral coordinate lattice. -/
def congruenceIndicator (L : PositiveDefiniteIntegralLattice n) (m : ℕ) (M : ℤ)
    (x : Fin n → IntegralFiniteAdele) : ℂ :=
  rationalFiniteAdeleIntegralIndicator
    (algebraMap ℚ RationalFiniteAdele ((m : ℚ))⁻¹ *
      (L.rationalQuadraticSpaceMatrix.finiteAdelicQuadraticFormValue
          (fun i => ((x i : IntegralFiniteAdele) : RationalFiniteAdele)) -
        algebraMap ℚ RationalFiniteAdele ((M : ℤ) : ℚ)))

/-- The congruence indicator is periodic modulo the `m`-dilated lattice. -/
theorem congruenceIndicator_add_dilation (L : PositiveDefiniteIntegralLattice n) (m : ℕ) (M : ℤ)
    (x w : Fin n → IntegralFiniteAdele)
    (hw : w ∈ (integralFiniteAdeleCoordinateNatDilation n m).range) :
    L.congruenceIndicator m M (x + w) = L.congruenceIndicator m M x := by
  obtain ⟨u, rfl⟩ := hw
  set X : Fin n → RationalFiniteAdele :=
    fun i => ((x i : IntegralFiniteAdele) : RationalFiniteAdele) with hX
  set U : Fin n → RationalFiniteAdele :=
    fun i => ((u i : IntegralFiniteAdele) : RationalFiniteAdele) with hU
  have hXmem : X ∈ integralFiniteAdeleVectors n := fun i => (x i).2
  have hUmem : U ∈ integralFiniteAdeleVectors n := fun i => (u i).2
  have hcoe : (fun i => (((x + integralFiniteAdeleCoordinateNatDilation n m u) i :
      IntegralFiniteAdele) : RationalFiniteAdele)) = X + m • U := by
    funext i
    show ((x i : RationalFiniteAdele)) +
      ((integralFiniteAdeleNatDilation m (u i) : IntegralFiniteAdele) :
        RationalFiniteAdele) = X i + m • U i
    rw [integralFiniteAdeleNatDilation_apply]
  have hQ : L.rationalQuadraticSpaceMatrix.finiteAdelicQuadraticFormValue (X + m • U) =
      L.rationalQuadraticSpaceMatrix.finiteAdelicQuadraticFormValue X +
        ((m : RationalFiniteAdele) *
          ((m : RationalFiniteAdele) *
            L.rationalQuadraticSpaceMatrix.finiteAdelicQuadraticFormValue U +
            dotProduct X
              (L.rationalQuadraticSpaceMatrix.finiteAdelicPolarMatrix.mulVec U))) := by
    rw [RationalQuadraticSpaceMatrix.finiteAdelicQuadraticFormValue_add,
      finiteAdelicQuadraticFormValue_nsmul', dotProduct_polar_nsmul]
    ring
  have hshift : (m : RationalFiniteAdele) *
      L.rationalQuadraticSpaceMatrix.finiteAdelicQuadraticFormValue U +
      dotProduct X (L.rationalQuadraticSpaceMatrix.finiteAdelicPolarMatrix.mulVec U) ∈
      integralFiniteAdeleSubring := by
    refine Subring.add_mem _ ?_ ?_
    · refine Subring.mul_mem _ (natCast_mem integralFiniteAdeleSubring m) ?_
      exact L.finiteAdelicBilinearFormValue_mem_integralFiniteAdeleSubring U U hUmem hUmem
    · rw [L.rationalQuadraticSpaceMatrix.finiteAdelicPolarMatrix_eq_two_smul,
        Matrix.smul_mulVec, dotProduct_smul]
      exact Subring.mul_mem _ (by norm_num)
        (L.finiteAdelicBilinearFormValue_mem_integralFiniteAdeleSubring X U hXmem hUmem)
  have hmq : ((m : ℚ)) ≠ 0 ∨ True := Or.inr trivial
  unfold congruenceIndicator
  rw [hcoe, hQ]
  by_cases hm : m = 0
  · subst hm
    simp
  · have hmq' : ((m : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr hm
    have hcancel : algebraMap ℚ RationalFiniteAdele ((m : ℚ))⁻¹ *
        (m : RationalFiniteAdele) = 1 := by
      have hcast : (m : RationalFiniteAdele) = algebraMap ℚ RationalFiniteAdele ((m : ℚ)) := by
        norm_num
      rw [hcast, ← map_mul, inv_mul_cancel₀ hmq', map_one]
    have hsplit : algebraMap ℚ RationalFiniteAdele ((m : ℚ))⁻¹ *
        (L.rationalQuadraticSpaceMatrix.finiteAdelicQuadraticFormValue X +
          ((m : RationalFiniteAdele) *
            ((m : RationalFiniteAdele) *
              L.rationalQuadraticSpaceMatrix.finiteAdelicQuadraticFormValue U +
              dotProduct X
                (L.rationalQuadraticSpaceMatrix.finiteAdelicPolarMatrix.mulVec U))) -
          algebraMap ℚ RationalFiniteAdele ((M : ℤ) : ℚ)) =
        algebraMap ℚ RationalFiniteAdele ((m : ℚ))⁻¹ *
          (L.rationalQuadraticSpaceMatrix.finiteAdelicQuadraticFormValue X -
            algebraMap ℚ RationalFiniteAdele ((M : ℤ) : ℚ)) +
          ((m : RationalFiniteAdele) *
            L.rationalQuadraticSpaceMatrix.finiteAdelicQuadraticFormValue U +
            dotProduct X
              (L.rationalQuadraticSpaceMatrix.finiteAdelicPolarMatrix.mulVec U)) := by
      rw [show algebraMap ℚ RationalFiniteAdele ((m : ℚ))⁻¹ *
          (L.rationalQuadraticSpaceMatrix.finiteAdelicQuadraticFormValue X +
            ((m : RationalFiniteAdele) * (((m : RationalFiniteAdele) *
              L.rationalQuadraticSpaceMatrix.finiteAdelicQuadraticFormValue U +
              dotProduct X
                (L.rationalQuadraticSpaceMatrix.finiteAdelicPolarMatrix.mulVec U)))) -
            algebraMap ℚ RationalFiniteAdele ((M : ℤ) : ℚ)) =
          algebraMap ℚ RationalFiniteAdele ((m : ℚ))⁻¹ *
            (L.rationalQuadraticSpaceMatrix.finiteAdelicQuadraticFormValue X -
              algebraMap ℚ RationalFiniteAdele ((M : ℤ) : ℚ)) +
            (algebraMap ℚ RationalFiniteAdele ((m : ℚ))⁻¹ *
              (m : RationalFiniteAdele)) *
              ((m : RationalFiniteAdele) *
                L.rationalQuadraticSpaceMatrix.finiteAdelicQuadraticFormValue U +
                dotProduct X
                  (L.rationalQuadraticSpaceMatrix.finiteAdelicPolarMatrix.mulVec U)) from by
        ring, hcancel, one_mul]
    rw [hsplit]
    exact rationalFiniteAdeleIntegralIndicator_add_of_mem _ _ hshift

/-! ## From the ambient integral to the residue count -/

theorem integral_congruence_eq_subtype (L : PositiveDefiniteIntegralLattice n) (m : ℕ) (M : ℤ) :
    (∫ x : Fin n → RationalFiniteAdele,
        rationalFiniteAdeleVectorIntegralIndicator x *
          rationalFiniteAdeleIntegralIndicator
            (algebraMap ℚ RationalFiniteAdele ((m : ℚ))⁻¹ *
              (L.rationalQuadraticSpaceMatrix.finiteAdelicQuadraticFormValue x -
                algebraMap ℚ RationalFiniteAdele ((M : ℤ) : ℚ)))
        ∂rationalFiniteAdeleCoordinateAddHaarMeasure n) =
      ∫ x : Fin n → IntegralFiniteAdele, L.congruenceIndicator m M x
        ∂integralFiniteAdeleCoordinateAddHaarMeasure n := by
  set f : (Fin n → RationalFiniteAdele) → ℂ := fun x =>
    rationalFiniteAdeleIntegralIndicator
      (algebraMap ℚ RationalFiniteAdele ((m : ℚ))⁻¹ *
        (L.rationalQuadraticSpaceMatrix.finiteAdelicQuadraticFormValue x -
          algebraMap ℚ RationalFiniteAdele ((M : ℤ) : ℚ))) with hf
  have hmeasf : Measurable f := by
    rw [hf]
    have hcont : Continuous fun x : Fin n → RationalFiniteAdele =>
        algebraMap ℚ RationalFiniteAdele ((m : ℚ))⁻¹ *
          (L.rationalQuadraticSpaceMatrix.finiteAdelicQuadraticFormValue x -
            algebraMap ℚ RationalFiniteAdele ((M : ℤ) : ℚ)) := by
      unfold RationalQuadraticSpaceMatrix.finiteAdelicQuadraticFormValue
      fun_prop
    have hind : Measurable rationalFiniteAdeleIntegralIndicator := by
      have heq : rationalFiniteAdeleIntegralIndicator =
          Set.indicator (integralFiniteAdeleSubring : Set RationalFiniteAdele)
            (fun _ => (1 : ℂ)) := rfl
      rw [heq]
      exact measurable_const.indicator isOpen_integralFiniteAdeleSubring.measurableSet
    exact hind.comp hcont.measurable
  have hpoint : ∀ x : Fin n → RationalFiniteAdele,
      rationalFiniteAdeleVectorIntegralIndicator x * f x =
        Set.indicator (integralFiniteAdeleVectors n) f x := by
    intro x
    by_cases hx : x ∈ integralFiniteAdeleVectors n
    · rw [rationalFiniteAdeleVectorIntegralIndicator_of_mem hx, one_mul,
        Set.indicator_of_mem hx]
    · rw [rationalFiniteAdeleVectorIntegralIndicator_of_not_mem hx, zero_mul,
        Set.indicator_of_notMem hx]
  rw [integral_congr_ae (Filter.Eventually.of_forall hpoint),
    integral_indicator (measurableSet_integralFiniteAdeleVectors n),
    ← (measurePreserving_integralFiniteAdeleCoordinateCoe n).map_eq,
    integral_map (measurePreserving_integralFiniteAdeleCoordinateCoe n).aemeasurable
      hmeasf.aestronglyMeasurable]
  rfl

/-- The congruence indicator pulled back to the canonical residue cube. -/
def congruenceResidueIndicator (L : PositiveDefiniteIntegralLattice n) (m : ℕ) (hm : m ≠ 0) (M : ℤ)
    (z : Fin n → ZMod m) : ℂ :=
  addQuotientPeriodicLift (integralFiniteAdeleCoordinateNatDilation n m).range
    (L.congruenceIndicator m M) (L.congruenceIndicator_add_dilation m M)
    (coordinateResidueEquivIntegralFiniteAdeleModDilation n m hm z)

theorem congruenceResidueIndicator_intCast (L : PositiveDefiniteIntegralLattice n) (m : ℕ) (hm : m ≠ 0)
    (M : ℤ) (z : Fin n → ℤ) :
    L.congruenceResidueIndicator m hm M (fun i => ((z i : ℤ) : ZMod m)) =
      L.congruenceIndicator m M (integerToIntegralFiniteAdeleVector n z) := by
  rw [congruenceResidueIndicator,
    coordinateResidueEquivIntegralFiniteAdeleModDilation_apply_intCast]
  rfl

theorem congruenceIndicator_integerVector (L : PositiveDefiniteIntegralLattice n) {m : ℕ} (hm : m ≠ 0)
    (M : ℤ) (z : Fin n → ℤ) :
    L.congruenceIndicator m M (integerToIntegralFiniteAdeleVector n z) =
      if ((m : ℤ)) ∣ (L.quadForm z - M) then 1 else 0 := by
  unfold congruenceIndicator
  have hcoe : (fun i => ((integerToIntegralFiniteAdeleVector n z i : IntegralFiniteAdele) :
      RationalFiniteAdele)) =
      fun i => algebraMap ℚ RationalFiniteAdele ((z i : ℤ) : ℚ) := by
    funext i
    rfl
  rw [hcoe, L.finiteAdelicQuadraticFormValue_intVector z, ← map_sub]
  rw [show ((L.quadForm z : ℤ) : ℚ) - ((M : ℤ) : ℚ) = (((L.quadForm z - M : ℤ)) : ℚ) from by
    push_cast; ring]
  exact integralIndicator_intDiv m hm (L.quadForm z - M)

theorem congruenceResidueIndicator_eq_ite (L : PositiveDefiniteIntegralLattice n) {m : ℕ} (hm : m ≠ 0)
    (M : ℤ) (z : Fin n → ZMod m) :
    L.congruenceResidueIndicator m hm M z =
      if L.zmodQuadForm m z = ((M : ℤ) : ZMod m) then 1 else 0 := by
  haveI : NeZero m := ⟨hm⟩
  have hrep : (fun i => (((((z i).val : ℕ) : ℤ)) : ZMod m)) = z := by
    funext i
    push_cast
    simp [ZMod.natCast_val, ZMod.cast_id]
  rw [← hrep, congruenceResidueIndicator_intCast,
    congruenceIndicator_integerVector L hm M, zmodQuadForm_intCast]
  congr 1
  rw [eq_iff_iff, ← sub_eq_zero, ← Int.cast_sub,
    ZMod.intCast_zmod_eq_zero_iff_dvd]

set_option maxHeartbeats 2000000 in
/-- The level-`m` congruence measure is the residue count. -/
theorem measure_congruenceSet_eq_residueCount (L : PositiveDefiniteIntegralLattice n) {m : ℕ} (hm : m ≠ 0)
    (M : ℤ) :
    (∫ x : Fin n → RationalFiniteAdele,
        rationalFiniteAdeleVectorIntegralIndicator x *
          rationalFiniteAdeleIntegralIndicator
            (algebraMap ℚ RationalFiniteAdele ((m : ℚ))⁻¹ *
              (L.rationalQuadraticSpaceMatrix.finiteAdelicQuadraticFormValue x -
                algebraMap ℚ RationalFiniteAdele ((M : ℤ) : ℚ)))
        ∂rationalFiniteAdeleCoordinateAddHaarMeasure n) =
      (((m : ℝ) ^ n : ℂ))⁻¹ *
        (Nat.card {z : Fin n → ZMod m // L.zmodQuadForm m z = ((M : ℤ) : ZMod m)} : ℂ) := by
  haveI : NeZero m := ⟨hm⟩
  classical
  rw [integral_congruence_eq_subtype L m M,
    integralFiniteAdeleCoordinate_integral_periodic_eq_inv_pow_sum n m
      (L.congruenceIndicator m M) (L.congruenceIndicator_add_dilation m M)]
  congr 1
  rw [← Equiv.sum_comp
    (coordinateResidueEquivIntegralFiniteAdeleModDilation n m hm).toEquiv
    (addQuotientPeriodicLift (integralFiniteAdeleCoordinateNatDilation n m).range
      (L.congruenceIndicator m M) (L.congruenceIndicator_add_dilation m M))]
  have hterm : ∀ z : Fin n → ZMod m,
      addQuotientPeriodicLift (integralFiniteAdeleCoordinateNatDilation n m).range
          (L.congruenceIndicator m M) (L.congruenceIndicator_add_dilation m M)
          ((coordinateResidueEquivIntegralFiniteAdeleModDilation n m hm).toEquiv z) =
        if L.zmodQuadForm m z = ((M : ℤ) : ZMod m) then 1 else 0 := by
    intro z
    exact L.congruenceResidueIndicator_eq_ite hm M z
  rw [Finset.sum_congr rfl fun z _ => hterm z, Finset.sum_boole]
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

set_option maxHeartbeats 2000000 in
/-- The finite local integral is the limit of the normalized residue counts:
`lim_k k!^(1-n) * #{z mod k! : Q(z) = M mod k!}`.  This is the classical singular series,
with no Euler product assumed. -/
theorem tendsto_finiteLocal_residueCount (L : PositiveDefiniteIntegralLattice n) {scale : ℝ}
    (hscale : 0 < scale) (hrank : 5 ≤ n) (M : ℤ) :
    Filter.Tendsto (fun k : ℕ =>
        ((Nat.factorial k : ℕ) : ℂ) * ((((Nat.factorial k : ℕ) : ℝ) ^ n : ℂ))⁻¹ *
          (Nat.card {z : Fin n → ZMod (Nat.factorial k) //
            L.zmodQuadForm (Nat.factorial k) z =
              ((M : ℤ) : ZMod (Nat.factorial k))} : ℂ))
      Filter.atTop
      (nhds (∫ y : RationalFiniteAdele,
        ((rationalFiniteAdeleFourierChar
            (algebraMap ℚ RationalFiniteAdele (-((M : ℤ) : ℚ)) * y) : Circle) : ℂ) *
          L.rationalQuadraticSpaceMatrix.rationalFiniteAdeleQuadraticGaussIntegralAt y
        ∂rationalFiniteAdeleAddHaarMeasure)) := by
  refine (L.tendsto_natScaleTruncated_finiteLocal hscale hrank ((M : ℤ) : ℚ)).congr fun k => ?_
  rw [L.measure_congruenceSet_eq_residueCount (Nat.factorial_ne_zero k) M]
  ring

end PositiveDefiniteIntegralLattice
