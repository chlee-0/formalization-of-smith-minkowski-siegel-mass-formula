import SMSFormula.RationalPadicUnitSquareBranchChangeOfVariables

/-!
# Branchwise real unit-square change of variables

The positive square range in `ℝˣ` is continuously multiplicatively
equivalent to the additive real line through exponential and logarithm.
Pulling its restricted Haar measure back along this equivalence reduces the
positive-sheet square map to additive doubling, whose determinant gives the
factor `1/2`.  The positive and negative sheets therefore make the full
square-map pushforward onto its positive range have scalar one.

Restricting that global identity to the chosen identity chart gives inverse
transport coefficient two.  This is the isolated archimedean input required
by the horizontal local `GSpin` differential chart; no Spin or sheet-count
coefficient remains.
-/

noncomputable section

open MeasureTheory Topology
open scoped ENNReal NNReal

namespace Rat

set_option maxHeartbeats 1600000

noncomputable local instance : MeasurableSpace ℝˣ := borel _
noncomputable local instance : BorelSpace ℝˣ := ⟨rfl⟩

def realExpSquareRange (t : Multiplicative ℝ) :
    (unitSquareMonoidHom ℝ).range := by
  let u : ℝˣ := Units.mk0 (Real.exp t.toAdd) (Real.exp_ne_zero _)
  refine ⟨u, ?_⟩
  let z : ℝˣ := Units.mk0 (Real.exp (t.toAdd / 2)) (Real.exp_ne_zero _)
  refine ⟨z, ?_⟩
  apply Units.ext
  change Real.exp (t.toAdd / 2) ^ 2 = Real.exp t.toAdd
  rw [pow_two, ← Real.exp_add]
  congr 1
  ring

@[simp] theorem realExpSquareRange_coe (t : Multiplicative ℝ) :
    ((realExpSquareRange t : ℝˣ) : ℝ) = Real.exp t.toAdd := rfl

theorem unitSquareMonoidHom_range_pos
    (u : (unitSquareMonoidHom ℝ).range) : 0 < ((u : ℝˣ) : ℝ) := by
  rcases u.property with ⟨z, hz⟩
  rw [← hz]
  change 0 < ((z : ℝ) ^ 2)
  exact sq_pos_of_ne_zero z.ne_zero

def realLogSquareRange (u : (unitSquareMonoidHom ℝ).range) : Multiplicative ℝ :=
  Multiplicative.ofAdd (Real.log ((u : ℝˣ) : ℝ))

def realExpSquareRangeMulEquiv :
    Multiplicative ℝ ≃* (unitSquareMonoidHom ℝ).range where
  toFun := realExpSquareRange
  invFun := realLogSquareRange
  left_inv t := by
    apply Multiplicative.toAdd.injective
    exact Real.log_exp t.toAdd
  right_inv u := by
    apply Subtype.ext
    apply Units.ext
    exact Real.exp_log (unitSquareMonoidHom_range_pos u)
  map_mul' x y := by
    apply Subtype.ext
    apply Units.ext
    exact Real.exp_add x.toAdd y.toAdd

def realExpSquareRangeContinuousMulEquiv :
    Multiplicative ℝ ≃ₜ* (unitSquareMonoidHom ℝ).range :=
  ContinuousMulEquiv.mk'
    { toEquiv := realExpSquareRangeMulEquiv.toEquiv
      continuous_toFun := by
        apply Continuous.subtype_mk
        apply Units.continuous_iff.mpr
        constructor
        · exact Real.continuous_exp
        · change Continuous (fun t : Multiplicative ℝ => (Real.exp t.toAdd)⁻¹)
          simpa only [← Real.exp_neg] using
            Real.continuous_exp.comp continuous_neg
      continuous_invFun := by
        change Continuous (fun u : (unitSquareMonoidHom ℝ).range =>
          Multiplicative.ofAdd (Real.log ((u : ℝˣ) : ℝ)))
        have hlog : Continuous (fun u : ℝˣ => Real.log (u : ℝ)) := by
          rw [continuous_iff_continuousAt]
          intro u
          exact (Real.continuousAt_log u.ne_zero).comp
            (Units.continuous_val.continuousAt)
        simpa only [Function.comp_apply] using
          continuous_ofAdd.comp (hlog.comp continuous_subtype_val) }
    realExpSquareRangeMulEquiv.map_mul

def realExpSquareRangeContinuousAddEquiv :
    ℝ ≃ₜ+ Additive (unitSquareMonoidHom ℝ).range :=
  ContinuousAddEquiv.mk'
    { toEquiv :=
        { toFun := fun x => Additive.ofMul
            (realExpSquareRangeContinuousMulEquiv (Multiplicative.ofAdd x))
          invFun := fun u => (realExpSquareRangeContinuousMulEquiv.symm u.toMul).toAdd
          left_inv := fun x => by simp
          right_inv := fun u => by simp }
      continuous_toFun := by
        exact continuous_ofMul.comp
          (realExpSquareRangeContinuousMulEquiv.continuous.comp continuous_ofAdd)
      continuous_invFun := by
        exact continuous_toAdd.comp
          (realExpSquareRangeContinuousMulEquiv.symm.continuous.comp continuous_toMul) }
    (by
      intro x y
      change Additive.ofMul
        (realExpSquareRangeContinuousMulEquiv
          (Multiplicative.ofAdd (x + y))) = _
      rw [show Multiplicative.ofAdd (x + y) =
          Multiplicative.ofAdd x * Multiplicative.ofAdd y from rfl,
        map_mul]
      rfl)

noncomputable local instance : MeasurableSpace (Multiplicative ℝ) := borel _
noncomputable local instance : BorelSpace (Multiplicative ℝ) := ⟨rfl⟩
noncomputable local instance :
    MeasurableSpace (Additive (unitSquareMonoidHom ℝ).range) := borel _
noncomputable local instance :
    BorelSpace (Additive (unitSquareMonoidHom ℝ).range) := ⟨rfl⟩

theorem unitSquareMonoidHom_range_isOpen :
    IsOpen ((unitSquareMonoidHom ℝ).range : Set ℝˣ) :=
  (unitSquareMonoidHom_isCoveringMap ℝ).isOpenMap.isOpen_range

noncomputable def realSquareRangeHaarMeasure :
    Measure (unitSquareMonoidHom ℝ).range :=
  Measure.comap (unitSquareMonoidHom ℝ).range.subtype
    (Measure.haar : Measure ℝˣ)

noncomputable instance : Measure.IsHaarMeasure realSquareRangeHaarMeasure := by
  letI : MeasurableMul ℝˣ :=
    ⟨fun _ => (continuous_const.mul continuous_id).measurable,
      fun _ => (continuous_id.mul continuous_const).measurable⟩
  apply Measure.IsHaarMeasure.comap (mH := ‹MeasurableMul ℝˣ›)
    (Measure.haar : Measure ℝˣ)
  exact unitSquareMonoidHom_range_isOpen.isOpenEmbedding_subtypeVal

def realSquareRangeAdditiveHomeomorph :
    (unitSquareMonoidHom ℝ).range ≃ₜ
      Additive (unitSquareMonoidHom ℝ).range where
  toFun := Additive.ofMul
  invFun := Additive.toMul
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_ofMul
  continuous_invFun := continuous_toMul

noncomputable def realSquareRangeAddHaarMeasure :
    Measure (Additive (unitSquareMonoidHom ℝ).range) :=
  Measure.map realSquareRangeAdditiveHomeomorph realSquareRangeHaarMeasure

noncomputable instance :
    Measure.IsAddHaarMeasure realSquareRangeAddHaarMeasure where
  map_add_left_eq_self g := by
    let e := realSquareRangeAdditiveHomeomorph
    have he : Measurable e := e.measurable
    have hm : Measurable (fun x : (unitSquareMonoidHom ℝ).range => g.toMul * x) :=
      continuous_const.mul continuous_id |>.measurable
    calc
      Measure.map (fun x => g + x) (Measure.map e realSquareRangeHaarMeasure) =
          Measure.map ((fun x => g + x) ∘ e) realSquareRangeHaarMeasure := by
        exact Measure.map_map (continuous_const.add continuous_id).measurable he
      _ = Measure.map (e ∘ fun x => g.toMul * x) realSquareRangeHaarMeasure := by
        rfl
      _ = Measure.map e
          (Measure.map (fun x => g.toMul * x) realSquareRangeHaarMeasure) := by
        rw [Measure.map_map he hm]
      _ = Measure.map e realSquareRangeHaarMeasure := by
        rw [Measure.IsMulLeftInvariant.map_mul_left_eq_self]
  toIsFiniteMeasureOnCompacts :=
    Measure.IsFiniteMeasureOnCompacts.map realSquareRangeHaarMeasure
      realSquareRangeAdditiveHomeomorph
  toIsOpenPosMeasure :=
    realSquareRangeAdditiveHomeomorph.continuous.isOpenPosMeasure_map
      realSquareRangeAdditiveHomeomorph.surjective

noncomputable def realSquareRangeLogHaarMeasure : Measure ℝ :=
  Measure.map realExpSquareRangeContinuousAddEquiv.symm
    realSquareRangeAddHaarMeasure

noncomputable instance :
    Measure.IsAddHaarMeasure realSquareRangeLogHaarMeasure :=
  realExpSquareRangeContinuousAddEquiv.symm.isAddHaarMeasure_map
    realSquareRangeAddHaarMeasure

theorem map_double_realSquareRangeLogHaarMeasure :
    Measure.map (fun x : ℝ => 2 * x) realSquareRangeLogHaarMeasure =
      (2 : NNReal)⁻¹ • realSquareRangeLogHaarMeasure := by
  let f : ℝ →ₗ[ℝ] ℝ := 2 • LinearMap.id
  have hdet : LinearMap.det f ≠ 0 := by
    simp [f]
  have h := Measure.map_linearMap_addHaar_eq_smul_addHaar
    realSquareRangeLogHaarMeasure hdet
  rw [show (fun x : ℝ => 2 * x) = f from by
    funext x
    simp [f]]
  calc
    Measure.map f realSquareRangeLogHaarMeasure =
        ENNReal.ofReal |(LinearMap.det f)⁻¹| •
          realSquareRangeLogHaarMeasure := h
    _ = (2 : NNReal)⁻¹ • realSquareRangeLogHaarMeasure := by
      congr 1
      simp [f, ENNReal.ofReal_inv_of_pos]

theorem map_realSquareRangeAddHaarMeasure :
    Measure.map (fun u : Additive (unitSquareMonoidHom ℝ).range => u + u)
        realSquareRangeAddHaarMeasure =
      (2 : NNReal)⁻¹ • realSquareRangeAddHaarMeasure := by
  let e := realExpSquareRangeContinuousAddEquiv
  have he : Measurable e := e.measurable
  have heinv : Measurable e.symm := e.symm.measurable
  have hd : Measurable (fun x : ℝ => 2 * x) :=
    (continuous_const.mul continuous_id).measurable
  have hs : Measurable
      (fun u : Additive (unitSquareMonoidHom ℝ).range => u + u) :=
    (continuous_id.add continuous_id).measurable
  have hrecover : Measure.map e realSquareRangeLogHaarMeasure =
      realSquareRangeAddHaarMeasure := by
    rw [realSquareRangeLogHaarMeasure,
      Measure.map_map he heinv]
    convert Measure.map_id
    funext u
    exact e.apply_symm_apply u
  calc
    Measure.map (fun u : Additive (unitSquareMonoidHom ℝ).range => u + u)
        realSquareRangeAddHaarMeasure =
        Measure.map (fun u => u + u)
          (Measure.map e realSquareRangeLogHaarMeasure) := by rw [hrecover]
    _ = Measure.map e
        (Measure.map (fun x : ℝ => 2 * x) realSquareRangeLogHaarMeasure) := by
      rw [Measure.map_map hs he, Measure.map_map he hd]
      congr 1
      funext x
      apply Additive.toMul.injective
      apply Subtype.ext
      apply Units.ext
      change Real.exp x * Real.exp x = Real.exp (2 * x)
      rw [← Real.exp_add]
      congr 1
      ring
    _ = Measure.map e
        ((2 : NNReal)⁻¹ • realSquareRangeLogHaarMeasure) := by
      rw [map_double_realSquareRangeLogHaarMeasure]
    _ = (2 : NNReal)⁻¹ • realSquareRangeAddHaarMeasure := by
      rw [Measure.map_smul, hrecover]

def realSquareRangeMap (u : (unitSquareMonoidHom ℝ).range) :
    (unitSquareMonoidHom ℝ).range :=
  (unitSquareMonoidHom ℝ).rangeRestrict u

theorem continuous_realSquareRangeMap : Continuous realSquareRangeMap := by
  apply Continuous.subtype_mk
  exact (continuous_pow 2 : Continuous (fun x : ℝˣ => x ^ 2)).comp
    continuous_subtype_val

theorem map_realSquareRangeHaarMeasure :
    Measure.map realSquareRangeMap realSquareRangeHaarMeasure =
      (2 : NNReal)⁻¹ • realSquareRangeHaarMeasure := by
  let e := realSquareRangeAdditiveHomeomorph
  apply e.measurableEmbedding.map_injective
  calc
    Measure.map e
        (Measure.map realSquareRangeMap realSquareRangeHaarMeasure) =
        Measure.map (e ∘ realSquareRangeMap) realSquareRangeHaarMeasure := by
      exact Measure.map_map e.measurable continuous_realSquareRangeMap.measurable
    _ = Measure.map
        ((fun u : Additive (unitSquareMonoidHom ℝ).range => u + u) ∘ e)
          realSquareRangeHaarMeasure := by
      congr 1
      funext u
      apply Additive.toMul.injective
      apply Subtype.ext
      apply Units.ext
      change ((u : ℝˣ) : ℝ) ^ 2 = ((u : ℝˣ) : ℝ) * ((u : ℝˣ) : ℝ)
      exact pow_two _
    _ = Measure.map (fun u : Additive (unitSquareMonoidHom ℝ).range => u + u)
          (Measure.map e realSquareRangeHaarMeasure) := by
      exact (Measure.map_map (continuous_id.add continuous_id).measurable
        e.measurable).symm
    _ = (2 : NNReal)⁻¹ •
        Measure.map e realSquareRangeHaarMeasure := by
      exact map_realSquareRangeAddHaarMeasure
    _ = Measure.map e ((2 : NNReal)⁻¹ • realSquareRangeHaarMeasure) := by
      rw [Measure.map_smul]

theorem mem_unitSquareMonoidHom_range_real_iff_pos (u : ℝˣ) :
    u ∈ (unitSquareMonoidHom ℝ).range ↔ 0 < (u : ℝ) := by
  constructor
  · rintro ⟨z, hz⟩
    rw [← hz]
    change 0 < ((z : ℝ) ^ 2)
    exact sq_pos_of_ne_zero z.ne_zero
  · intro hu
    let z : ℝˣ := Units.mk0 (Real.sqrt (u : ℝ))
      (Real.sqrt_ne_zero'.mpr hu)
    refine ⟨z, ?_⟩
    apply Units.ext
    change Real.sqrt (u : ℝ) ^ 2 = (u : ℝ)
    exact Real.sq_sqrt hu.le

def realNegativeUnits : Set ℝˣ := {u | (u : ℝ) < 0}

theorem isOpen_realNegativeUnits : IsOpen realNegativeUnits := by
  exact isOpen_Iio.preimage Units.continuous_val

theorem disjoint_unitSquareMonoidHom_range_realNegativeUnits :
    Disjoint ((unitSquareMonoidHom ℝ).range : Set ℝˣ) realNegativeUnits := by
  rw [Set.disjoint_left]
  intro u hu hneg
  exact (not_lt_of_ge (mem_unitSquareMonoidHom_range_real_iff_pos u |>.mp hu).le) hneg

theorem union_unitSquareMonoidHom_range_realNegativeUnits :
    ((unitSquareMonoidHom ℝ).range : Set ℝˣ) ∪ realNegativeUnits = Set.univ := by
  ext u
  simp only [Set.mem_union, Set.mem_univ, iff_true]
  rcases lt_or_gt_of_ne u.ne_zero with hneg | hpos
  · exact Or.inr hneg
  · exact Or.inl ((mem_unitSquareMonoidHom_range_real_iff_pos u).mpr hpos)

theorem preimage_mulLeft_neg_one_realNegativeUnits :
    Homeomorph.mulLeft (-1 : ℝˣ) ⁻¹' realNegativeUnits =
      ((unitSquareMonoidHom ℝ).range : Set ℝˣ) := by
  ext u
  simp only [Set.mem_preimage, realNegativeUnits, Set.mem_setOf_eq,
    Homeomorph.coe_mulLeft, Units.val_mul, Units.val_neg, Units.val_one]
  rw [neg_one_mul]
  exact neg_lt_zero.trans (mem_unitSquareMonoidHom_range_real_iff_pos u).symm

theorem map_mulLeft_neg_one_restrict_squareRange :
    Measure.map (Homeomorph.mulLeft (-1 : ℝˣ))
        ((Measure.haar : Measure ℝˣ).restrict
          ((unitSquareMonoidHom ℝ).range : Set ℝˣ)) =
      (Measure.haar : Measure ℝˣ).restrict realNegativeUnits := by
  calc
    Measure.map (Homeomorph.mulLeft (-1 : ℝˣ))
        ((Measure.haar : Measure ℝˣ).restrict
          ((unitSquareMonoidHom ℝ).range : Set ℝˣ)) =
        (Measure.map (Homeomorph.mulLeft (-1 : ℝˣ))
          (Measure.haar : Measure ℝˣ)).restrict realNegativeUnits := by
      symm
      rw [Measure.restrict_map (Homeomorph.mulLeft (-1 : ℝˣ)).measurable
        isOpen_realNegativeUnits.measurableSet,
        preimage_mulLeft_neg_one_realNegativeUnits]
    _ = (Measure.haar : Measure ℝˣ).restrict realNegativeUnits := by
      have hmap : Measure.map (Homeomorph.mulLeft (-1 : ℝˣ))
          (Measure.haar : Measure ℝˣ) = Measure.haar := by
        simpa only [Homeomorph.coe_mulLeft] using
          (Measure.IsMulLeftInvariant.map_mul_left_eq_self
            (μ := (Measure.haar : Measure ℝˣ)) (-1 : ℝˣ))
      rw [hmap]

theorem map_unitSquareMonoidHom_restrict_realNegativeUnits :
    Measure.map (unitSquareMonoidHom ℝ)
        ((Measure.haar : Measure ℝˣ).restrict realNegativeUnits) =
      Measure.map (unitSquareMonoidHom ℝ)
        ((Measure.haar : Measure ℝˣ).restrict
          ((unitSquareMonoidHom ℝ).range : Set ℝˣ)) := by
  rw [← map_mulLeft_neg_one_restrict_squareRange]
  calc
    Measure.map (unitSquareMonoidHom ℝ)
        (Measure.map (Homeomorph.mulLeft (-1 : ℝˣ))
          ((Measure.haar : Measure ℝˣ).restrict
            ((unitSquareMonoidHom ℝ).range : Set ℝˣ))) =
        Measure.map ((unitSquareMonoidHom ℝ) ∘
          (Homeomorph.mulLeft (-1 : ℝˣ)))
          ((Measure.haar : Measure ℝˣ).restrict
            ((unitSquareMonoidHom ℝ).range : Set ℝˣ)) := by
      exact Measure.map_map (continuous_pow 2).measurable
        (Homeomorph.mulLeft (-1 : ℝˣ)).measurable
    _ = Measure.map (unitSquareMonoidHom ℝ)
        ((Measure.haar : Measure ℝˣ).restrict
          ((unitSquareMonoidHom ℝ).range : Set ℝˣ)) := by
      congr 1
      funext u
      simp [unitSquareMonoidHom, pow_two]

theorem map_unitSquareMonoidHom_restrict_range :
    Measure.map (unitSquareMonoidHom ℝ)
        ((Measure.haar : Measure ℝˣ).restrict
          ((unitSquareMonoidHom ℝ).range : Set ℝˣ)) =
      (2 : NNReal)⁻¹ •
        (Measure.haar : Measure ℝˣ).restrict
          ((unitSquareMonoidHom ℝ).range : Set ℝˣ) := by
  let i := (unitSquareMonoidHom ℝ).range.subtype
  have hi : Measure.map i realSquareRangeHaarMeasure =
      (Measure.haar : Measure ℝˣ).restrict
        ((unitSquareMonoidHom ℝ).range : Set ℝˣ) := by
    exact map_comap_subtype_coe unitSquareMonoidHom_range_isOpen.measurableSet _
  calc
    Measure.map (unitSquareMonoidHom ℝ)
        ((Measure.haar : Measure ℝˣ).restrict
          ((unitSquareMonoidHom ℝ).range : Set ℝˣ)) =
        Measure.map (unitSquareMonoidHom ℝ)
          (Measure.map i realSquareRangeHaarMeasure) := by rw [hi]
    _ = Measure.map i
        (Measure.map realSquareRangeMap realSquareRangeHaarMeasure) := by
      calc
        Measure.map (unitSquareMonoidHom ℝ)
            (Measure.map i realSquareRangeHaarMeasure) =
            Measure.map ((unitSquareMonoidHom ℝ) ∘ i)
              realSquareRangeHaarMeasure := by
          exact Measure.map_map (continuous_pow 2).measurable
            continuous_subtype_val.measurable
        _ = Measure.map (i ∘ realSquareRangeMap)
              realSquareRangeHaarMeasure := by
          congr 1
        _ = Measure.map i
            (Measure.map realSquareRangeMap realSquareRangeHaarMeasure) := by
          exact (Measure.map_map continuous_subtype_val.measurable
            continuous_realSquareRangeMap.measurable).symm
    _ = Measure.map i ((2 : NNReal)⁻¹ • realSquareRangeHaarMeasure) := by
      rw [map_realSquareRangeHaarMeasure]
    _ = (2 : NNReal)⁻¹ •
        (Measure.haar : Measure ℝˣ).restrict
          ((unitSquareMonoidHom ℝ).range : Set ℝˣ) := by
      rw [Measure.map_smul, hi]

theorem map_unitSquareMonoidHom_realHaar :
    Measure.map (unitSquareMonoidHom ℝ) (Measure.haar : Measure ℝˣ) =
      (Measure.haar : Measure ℝˣ).restrict
        ((unitSquareMonoidHom ℝ).range : Set ℝˣ) := by
  have hsplit : (Measure.haar : Measure ℝˣ) =
      (Measure.haar : Measure ℝˣ).restrict
          ((unitSquareMonoidHom ℝ).range : Set ℝˣ) +
        (Measure.haar : Measure ℝˣ).restrict realNegativeUnits := by
    calc
      (Measure.haar : Measure ℝˣ) =
          (Measure.haar : Measure ℝˣ).restrict Set.univ := by
        rw [Measure.restrict_univ]
      _ = (Measure.haar : Measure ℝˣ).restrict
          (((unitSquareMonoidHom ℝ).range : Set ℝˣ) ∪ realNegativeUnits) := by
        rw [union_unitSquareMonoidHom_range_realNegativeUnits]
      _ = (Measure.haar : Measure ℝˣ).restrict
          ((unitSquareMonoidHom ℝ).range : Set ℝˣ) +
          (Measure.haar : Measure ℝˣ).restrict realNegativeUnits := by
        rw [Measure.restrict_union disjoint_unitSquareMonoidHom_range_realNegativeUnits
          isOpen_realNegativeUnits.measurableSet]
  conv_lhs => rw [hsplit]
  calc
    Measure.map (unitSquareMonoidHom ℝ)
        ((Measure.haar : Measure ℝˣ).restrict
            ((unitSquareMonoidHom ℝ).range : Set ℝˣ) +
          (Measure.haar : Measure ℝˣ).restrict realNegativeUnits) =
        Measure.map (unitSquareMonoidHom ℝ)
            ((Measure.haar : Measure ℝˣ).restrict
              ((unitSquareMonoidHom ℝ).range : Set ℝˣ)) +
          Measure.map (unitSquareMonoidHom ℝ)
            ((Measure.haar : Measure ℝˣ).restrict realNegativeUnits) := by
      exact Measure.map_add _ _ (continuous_pow 2).measurable
    _ = ((2 : NNReal)⁻¹ •
          (Measure.haar : Measure ℝˣ).restrict
            ((unitSquareMonoidHom ℝ).range : Set ℝˣ)) +
        ((2 : NNReal)⁻¹ •
          (Measure.haar : Measure ℝˣ).restrict
            ((unitSquareMonoidHom ℝ).range : Set ℝˣ)) := by
      rw [map_unitSquareMonoidHom_restrict_realNegativeUnits,
        map_unitSquareMonoidHom_restrict_range]
    _ = (Measure.haar : Measure ℝˣ).restrict
          ((unitSquareMonoidHom ℝ).range : Set ℝˣ) := by
      rw [← add_smul]
      norm_num

theorem map_unitSquareMonoidHom_rangeRestrict_realHaar :
    Measure.map (unitSquareMonoidHom ℝ).rangeRestrict
        (Measure.haar : Measure ℝˣ) =
      realSquareRangeHaarMeasure := by
  let i := (unitSquareMonoidHom ℝ).range.subtype
  apply (unitSquareMonoidHom_range_isOpen.isOpenEmbedding_subtypeVal
    |>.measurableEmbedding).map_injective
  calc
    Measure.map i
        (Measure.map (unitSquareMonoidHom ℝ).rangeRestrict
          (Measure.haar : Measure ℝˣ)) =
        Measure.map (unitSquareMonoidHom ℝ) (Measure.haar : Measure ℝˣ) := by
      calc
        Measure.map i
            (Measure.map (unitSquareMonoidHom ℝ).rangeRestrict
              (Measure.haar : Measure ℝˣ)) =
            Measure.map (i ∘ (unitSquareMonoidHom ℝ).rangeRestrict)
              (Measure.haar : Measure ℝˣ) := by
          exact Measure.map_map continuous_subtype_val.measurable
            ((continuous_pow 2).subtype_mk _).measurable
        _ = Measure.map (unitSquareMonoidHom ℝ)
            (Measure.haar : Measure ℝˣ) := by
          congr 1
    _ = (Measure.haar : Measure ℝˣ).restrict
        ((unitSquareMonoidHom ℝ).range : Set ℝˣ) :=
      map_unitSquareMonoidHom_realHaar
    _ = Measure.map i realSquareRangeHaarMeasure := by
      exact (map_comap_subtype_coe unitSquareMonoidHom_range_isOpen.measurableSet _).symm

@[simp] theorem unitSquareMonoidHom_neg_one_real :
    unitSquareMonoidHom ℝ (-1) = 1 := by
  simp [unitSquareMonoidHom, pow_two]

theorem neg_one_ne_one_realUnit : (-1 : ℝˣ) ≠ 1 := by
  intro h
  have hv := congrArg Units.val h
  norm_num at hv

theorem eq_one_or_neg_one_of_unitSquareMonoidHom_real_eq_one
    (z : ℝˣ) (hz : unitSquareMonoidHom ℝ z = 1) :
    z = 1 ∨ z = -1 := by
  have hzval : (z : ℝ) ^ 2 = 1 := congrArg Units.val hz
  rcases sq_eq_one_iff.mp hzval with h | h
  · left
    apply Units.ext
    exact h
  · right
    apply Units.ext
    exact h

end Rat

namespace RationalQuadraticSpaceMatrix

noncomputable local instance : MeasurableSpace ℝˣ := borel _
noncomputable local instance : BorelSpace ℝˣ := ⟨rfl⟩

theorem two_smul_map_realUnitSquareIdentityChartAmbientSourceMeasure :
    (2 : NNReal) •
        Measure.map
          (Rat.unitSquareIdentityChart ℝ).toHomeomorphSourceTarget
          realUnitSquareIdentityChartAmbientSourceMeasure =
      realUnitSquareIdentityChartTargetMeasure := by
  have h :=
    MeasureTheory.TranslatedHomChart.two_smul_map_identityChart_comap_eq_smul_comap_of_rangeRestrict
      (Rat.unitSquareMonoidHom ℝ)
      (Rat.unitSquareIdentityChart ℝ)
      (continuous_pow 2)
      (Rat.unitSquareIdentityChart_coe ℝ)
      Rat.unitSquareMonoidHom_range_isOpen
      (-1 : ℝˣ)
      Rat.unitSquareMonoidHom_neg_one_real
      Rat.neg_one_ne_one_realUnit
      Rat.eq_one_or_neg_one_of_unitSquareMonoidHom_real_eq_one
      (Measure.haar : Measure ℝˣ)
      (Measure.haar : Measure ℝˣ)
      1
      (by simpa [Rat.realSquareRangeHaarMeasure] using
        Rat.map_unitSquareMonoidHom_rangeRestrict_realHaar)
  simpa using h

theorem realUnitSquareBranchChangeOfVariables :
    RealUnitSquareBranchChangeOfVariables := by
  let chart := Rat.unitSquareIdentityChart ℝ
  rw [RealUnitSquareBranchChangeOfVariables,
    rationalIdeleRealSquareModulus_eq_two]
  apply chart.toHomeomorphSourceTarget.measurableEmbedding.map_injective
  calc
    Measure.map chart.toHomeomorphSourceTarget
        realUnitSquareIdentityChartSourceMeasure =
        realUnitSquareIdentityChartTargetMeasure :=
      map_realUnitSquareIdentityChartSourceMeasure
    _ = (2 : NNReal) •
        Measure.map chart.toHomeomorphSourceTarget
          realUnitSquareIdentityChartAmbientSourceMeasure :=
      two_smul_map_realUnitSquareIdentityChartAmbientSourceMeasure.symm
    _ = Measure.map chart.toHomeomorphSourceTarget
        ((2 : NNReal) • realUnitSquareIdentityChartAmbientSourceMeasure) := by
      rw [Measure.map_smul]

end RationalQuadraticSpaceMatrix
