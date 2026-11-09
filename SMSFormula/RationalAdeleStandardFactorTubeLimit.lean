import SMSFormula.RationalAdeleResidueTubeDecomposition
import SMSFormula.RationalFiniteAdeleHaarScaling

/-!
# The tube limit of every standard finite factor

For a finite factor `g` carried by `(1/c)Ẑⁿ` and periodic modulo `dẐⁿ` (the finite factors of the
real Gaussian core) and `M ≠ 0` in lattice rank at least four, the `k!`-tube masses
`T_{k!}(g)(M) = k! · ∫ g(x) 1_Ẑ((Q(x) − M)/k!) dx` converge
(`exists_tendsto_finiteTubeMass_factorial`).

* Dilation (`finiteTubeMass_mul_sq_eq_dilate`): `x = y/c` turns `T_w(g)(M)` into
  `c^n/c² · T_{c²w}(g̃)(c²M)` with `g̃ = g(·/c)` carried by `Ẑⁿ` and periodic modulo `cdẐⁿ`
  (Haar substitution `integral_rationalFiniteAdeleCoordinateScale_inv`, `Q(y/c) = Q(y)/c²`).
* Residue decomposition (`eq_sum_residueRestrictedIndicator`): a factor carried by `Ẑⁿ` and periodic
  modulo `NẐⁿ` is `Σ_ρ g̃(ρ) · 1_{ρ + NẐⁿ}` (residue quotient `integralVectorResidue`).
* At the CRT level `N = cd` every class has one tube limit along the cofinal widths `c²k!`
  (`RationalAdeleResidueTubeDecomposition`), so the sum converges. No residue representative, width
  or normalization is chosen in any statement.
-/

noncomputable section

open MeasureTheory Filter Topology RationalQuadraticSpaceMatrix
open scoped ENNReal Matrix

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- The finite `w`-tube mass of a finite factor at the value `M`. -/
def finiteTubeMass (L : PositiveDefiniteIntegralLattice n) (g : (Fin n → RationalFiniteAdele) → ℂ) (w : ℕ)
    (M : ℤ) : ℂ :=
  (w : ℂ) * ∫ x : Fin n → RationalFiniteAdele,
    g x * rationalFiniteAdeleIntegralIndicator
      (algebraMap ℚ RationalFiniteAdele ((w : ℚ))⁻¹ *
        (L.rationalQuadraticSpaceMatrix.finiteAdelicQuadraticFormValue x -
          algebraMap ℚ RationalFiniteAdele ((M : ℤ) : ℚ)))
    ∂rationalFiniteAdeleCoordinateAddHaarMeasure n

/-- Homogeneity of the finite quadratic value under rational scaling. -/
theorem finiteAdelicQuadraticFormValue_coordinateScale (V : RationalQuadraticSpaceMatrix n) (q : ℚ)
    (x : Fin n → RationalFiniteAdele) :
    V.finiteAdelicQuadraticFormValue (rationalFiniteAdeleCoordinateScale q x) =
      algebraMap ℚ RationalFiniteAdele (q ^ 2) * V.finiteAdelicQuadraticFormValue x := by
  have hs : rationalFiniteAdeleCoordinateScale q x = algebraMap ℚ RationalFiniteAdele q • x := rfl
  unfold finiteAdelicQuadraticFormValue
  rw [hs, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul, map_pow]
  ring

/-- `c • (x/c) = x` for the rational scaling of finite-adelic vectors. -/
theorem nsmul_coordinateScale_inv {c : ℕ} (hc : c ≠ 0) (x : Fin n → RationalFiniteAdele) :
    c • rationalFiniteAdeleCoordinateScale ((c : ℚ))⁻¹ x = x := by
  funext i
  have hcq : (c : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hc
  change c • (algebraMap ℚ RationalFiniteAdele ((c : ℚ))⁻¹ * x i) = x i
  rw [nsmul_eq_mul, ← mul_assoc, show (c : RationalFiniteAdele) = algebraMap ℚ RationalFiniteAdele c
    by norm_num, ← map_mul, mul_inv_cancel₀ hcq, map_one, one_mul]

/-- `(c d • u)/c = d • u`. -/
theorem coordinateScale_inv_nsmul_mul {c : ℕ} (hc : c ≠ 0) (d : ℕ) (u : Fin n → RationalFiniteAdele) :
    rationalFiniteAdeleCoordinateScale ((c : ℚ))⁻¹ ((c * d) • u) = d • u := by
  funext i
  have hcq : (c : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hc
  change algebraMap ℚ RationalFiniteAdele ((c : ℚ))⁻¹ * ((c * d) • u i) = d • u i
  rw [nsmul_eq_mul, nsmul_eq_mul, Nat.cast_mul, ← mul_assoc, ← mul_assoc,
    show (c : RationalFiniteAdele) = algebraMap ℚ RationalFiniteAdele c by norm_num, ← map_mul,
    inv_mul_cancel₀ hcq, map_one, one_mul]

theorem coordinateScale_add (q : ℚ) (x y : Fin n → RationalFiniteAdele) :
    rationalFiniteAdeleCoordinateScale q (x + y) =
      rationalFiniteAdeleCoordinateScale q x + rationalFiniteAdeleCoordinateScale q y := by
  funext i
  exact mul_add _ _ _

/-- The dilated factor of a `(1/c)Ẑⁿ`-carried factor is `Ẑⁿ`-carried. -/
theorem isStandardCarried_one_comp_scale {c : ℕ} (hc : c ≠ 0)
    {g : (Fin n → RationalFiniteAdele) → ℂ} (hg : IsStandardCarried c g) :
    IsStandardCarried 1 (fun y ↦ g (rationalFiniteAdeleCoordinateScale ((c : ℚ))⁻¹ y)) := by
  intro y hy
  refine hg _ fun h ↦ hy ?_
  change 1 • y ∈ integralFiniteAdeleVectors n
  rw [one_smul, ← nsmul_coordinateScale_inv hc y]
  exact h

/-- The dilated factor of a `dẐⁿ`-periodic factor is `cdẐⁿ`-periodic. -/
theorem isStandardPeriodic_mul_comp_scale {c d : ℕ} (hc : c ≠ 0)
    {g : (Fin n → RationalFiniteAdele) → ℂ} (hg : IsStandardPeriodic d g) :
    IsStandardPeriodic (c * d) (fun y ↦ g (rationalFiniteAdeleCoordinateScale ((c : ℚ))⁻¹ y)) := by
  intro y u hu
  simp only
  rw [coordinateScale_add, coordinateScale_inv_nsmul_mul hc d u]
  exact hg _ u hu

set_option maxHeartbeats 1600000 in
/-- The dilation law of tube masses: `T_w(g)(M) · c² = c^n · T_{c²w}(g(·/c))(c²M)`. -/
theorem finiteTubeMass_mul_sq_eq_dilate (L : PositiveDefiniteIntegralLattice n) (g : (Fin n → RationalFiniteAdele) → ℂ)
    {c : ℕ} (hc : c ≠ 0) (w : ℕ) (M : ℤ) :
    L.finiteTubeMass g w M * (c : ℂ) ^ 2 =
      (c : ℂ) ^ n * L.finiteTubeMass (fun y ↦ g (rationalFiniteAdeleCoordinateScale ((c : ℚ))⁻¹ y))
        (c ^ 2 * w) ((c : ℤ) ^ 2 * M) := by
  have hcq : (c : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hc
  have hq : ((c : ℚ))⁻¹ ≠ 0 := inv_ne_zero hcq
  have hcC : (c : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hc
  set F : (Fin n → RationalFiniteAdele) → ℂ := fun x ↦ g x *
    rationalFiniteAdeleIntegralIndicator (algebraMap ℚ RationalFiniteAdele ((w : ℚ))⁻¹ *
      (L.rationalQuadraticSpaceMatrix.finiteAdelicQuadraticFormValue x -
        algebraMap ℚ RationalFiniteAdele ((M : ℤ) : ℚ))) with hF
  have h := integral_rationalFiniteAdeleCoordinateScale_inv n hc hq F
  have harg : ∀ y, algebraMap ℚ RationalFiniteAdele ((w : ℚ))⁻¹ *
      (L.rationalQuadraticSpaceMatrix.finiteAdelicQuadraticFormValue
          (rationalFiniteAdeleCoordinateScale ((c : ℚ))⁻¹ y) -
        algebraMap ℚ RationalFiniteAdele ((M : ℤ) : ℚ)) =
      algebraMap ℚ RationalFiniteAdele (((c ^ 2 * w : ℕ) : ℚ))⁻¹ *
        (L.rationalQuadraticSpaceMatrix.finiteAdelicQuadraticFormValue y -
          algebraMap ℚ RationalFiniteAdele ((((c : ℤ) ^ 2 * M : ℤ)) : ℚ)) := by
    intro y
    rw [finiteAdelicQuadraticFormValue_coordinateScale]
    have e1 : (((c ^ 2 * w : ℕ) : ℚ))⁻¹ = ((w : ℚ))⁻¹ * ((c : ℚ))⁻¹ ^ 2 := by
      push_cast; rw [mul_inv, inv_pow]; ring
    have e2 : ((((c : ℤ) ^ 2 * M : ℤ)) : ℚ) = (c : ℚ) ^ 2 * (M : ℚ) := by push_cast; ring
    rw [e1, e2, map_mul, map_mul]
    have hc1 : algebraMap ℚ RationalFiniteAdele (((c : ℚ))⁻¹ ^ 2) *
        algebraMap ℚ RationalFiniteAdele ((c : ℚ) ^ 2) = 1 := by
      rw [← map_mul, inv_pow, inv_mul_cancel₀ (pow_ne_zero 2 hcq), map_one]
    linear_combination (algebraMap ℚ RationalFiniteAdele ((w : ℚ))⁻¹ *
      algebraMap ℚ RationalFiniteAdele ((M : ℤ) : ℚ)) * hc1
  unfold finiteTubeMass
  have hlhs : (∫ x, F x ∂rationalFiniteAdeleCoordinateAddHaarMeasure n) =
      (c : ℂ) ^ n * ∫ y, F (rationalFiniteAdeleCoordinateScale ((c : ℚ))⁻¹ y)
        ∂rationalFiniteAdeleCoordinateAddHaarMeasure n := by
    rw [h, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ hcC, one_pow, one_mul]
  change ((w : ℂ) * ∫ x, F x ∂rationalFiniteAdeleCoordinateAddHaarMeasure n) * (c : ℂ) ^ 2 = _
  rw [hlhs]
  simp_rw [hF, harg]
  push_cast
  ring

/-! ## Residue decomposition of an `Ẑⁿ`-carried periodic factor -/

/-- The integral lift of a residue class: the integral vector with coordinates `(ρ i).val`. -/
def residueFiniteAdeleLift (N : ℕ) (ρ : Fin n → ZMod N) : Fin n → RationalFiniteAdele :=
  fun i ↦ ((integerToIntegralFiniteAdeleVector n (fun i ↦ ((ρ i).val : ℤ)) i : IntegralFiniteAdele) :
    RationalFiniteAdele)

/-- A factor carried by `Ẑⁿ` and periodic modulo `NẐⁿ` is the sum of its class values times the
class indicators. -/
theorem eq_sum_residueRestrictedIndicator {N : ℕ} [NeZero N] {g : (Fin n → RationalFiniteAdele) → ℂ}
    (hcar : IsStandardCarried 1 g) (hper : IsStandardPeriodic N g) (x : Fin n → RationalFiniteAdele) :
    g x = ∑ ρ : Fin n → ZMod N, g (residueFiniteAdeleLift N ρ) * residueRestrictedIndicator n N {ρ} x := by
  classical
  by_cases hx : x ∈ integralFiniteAdeleVectors n
  · set xh : Fin n → IntegralFiniteAdele := fun i ↦ ⟨x i, hx i⟩ with hxh
    have hind : ∀ ρ : Fin n → ZMod N, residueRestrictedIndicator n N {ρ} x =
        if integralVectorResidue n N xh = ρ then 1 else 0 := by
      intro ρ
      simp only [residueRestrictedIndicator, dif_pos hx, Set.mem_singleton_iff, xh]
    simp_rw [hind, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ _)]
    -- the lift of the residue differs from `x` by the `N`-dilated lattice
    set ρ₀ := integralVectorResidue n N xh with hρ₀
    set w : Fin n → IntegralFiniteAdele :=
      integerToIntegralFiniteAdeleVector n (fun i ↦ ((ρ₀ i).val : ℤ)) with hw
    have hres : integralVectorResidue n N w = integralVectorResidue n N xh := by
      rw [hw, integralVectorResidue_intCast]
      funext i
      simp only [Int.cast_natCast, ZMod.natCast_zmod_val]
      exact congrFun hρ₀ i
    have hq : (w : (Fin n → IntegralFiniteAdele) ⧸
          (integralFiniteAdeleCoordinateNatDilation n N).range) =
        (xh : (Fin n → IntegralFiniteAdele) ⧸
          (integralFiniteAdeleCoordinateNatDilation n N).range) :=
      (coordinateResidueEquivIntegralFiniteAdeleModDilation n N (NeZero.ne N)).symm.injective hres
    obtain ⟨u, hu⟩ := QuotientAddGroup.eq.1 hq.symm
    have hwx : w = xh + integralFiniteAdeleCoordinateNatDilation n N u := by
      rw [hu]; abel
    have hlift : residueFiniteAdeleLift N ρ₀ = x + N • (fun i ↦ ((u i : IntegralFiniteAdele) : RationalFiniteAdele)) := by
      funext i
      have hi := congrArg (fun v : Fin n → IntegralFiniteAdele ↦ ((v i : IntegralFiniteAdele) :
        RationalFiniteAdele)) hwx
      simp only [residueFiniteAdeleLift] at hi ⊢
      rw [← hw, hi]
      rfl
    rw [hlift, hper x _ fun i ↦ (u i).property]
  · have hx1 : x ∉ standardDividedLattice n 1 := by simpa [standardDividedLattice] using hx
    rw [hcar x hx1]
    refine (Finset.sum_eq_zero fun ρ _ ↦ ?_).symm
    rw [residueRestrictedIndicator, dif_neg hx, mul_zero]

theorem continuous_finiteAdelicQuadraticFormValue (V : RationalQuadraticSpaceMatrix n) :
    Continuous V.finiteAdelicQuadraticFormValue := by
  unfold finiteAdelicQuadraticFormValue
  exact continuous_id.dotProduct (continuous_const.matrix_mulVec continuous_id)

theorem integrable_residueRestrictedIndicator_mul_tube (L : PositiveDefiniteIntegralLattice n) (N : ℕ) [NeZero N]
    (R : Set (Fin n → ZMod N)) (a b : RationalFiniteAdele) :
    Integrable (fun x : Fin n → RationalFiniteAdele ↦ residueRestrictedIndicator n N R x *
        rationalFiniteAdeleIntegralIndicator (a * (L.rationalQuadraticSpaceMatrix.finiteAdelicQuadraticFormValue x - b)))
      (rationalFiniteAdeleCoordinateAddHaarMeasure n) := by
  have hI : Integrable (residueRestrictedIndicator n N R)
      (rationalFiniteAdeleCoordinateAddHaarMeasure n) :=
    integrable_of_isStandardCarried_isStandardPeriodic one_ne_zero (NeZero.ne N)
      (isStandardCarried_residueRestrictedIndicator N R) (isStandardPeriodic_residueRestrictedIndicator N R)
  refine hI.mul_bdd (c := 1) ?_ (Filter.Eventually.of_forall fun x ↦ ?_)
  · exact (measurable_rationalFiniteAdeleIntegralIndicator.comp
      ((continuous_const.mul ((continuous_finiteAdelicQuadraticFormValue _).sub
        continuous_const)).measurable)).aestronglyMeasurable
  · unfold rationalFiniteAdeleIntegralIndicator
    by_cases h : a * (L.rationalQuadraticSpaceMatrix.finiteAdelicQuadraticFormValue x - b) ∈
        (integralFiniteAdeleSubring : Set RationalFiniteAdele)
    · rw [Set.indicator_of_mem h]; simp
    · rw [Set.indicator_of_notMem h]; simp

set_option maxHeartbeats 4000000 in
/-- The tube limit of every standard finite factor exists (rank at least four, `M ≠ 0`). -/
theorem exists_tendsto_finiteTubeMass_factorial (L : PositiveDefiniteIntegralLattice (n + 1)) (hn : 3 ≤ n)
    {M : ℤ} (hM : M ≠ 0) {c d : ℕ} (hc : c ≠ 0) (hd : d ≠ 0)
    {g : (Fin (n + 1) → RationalFiniteAdele) → ℂ}
    (hcar : IsStandardCarried c g) (hper : IsStandardPeriodic d g) :
    ∃ D : ℂ, Tendsto (fun k ↦ L.finiteTubeMass g (Nat.factorial k) M) atTop (𝓝 D) := by
  classical
  set gt : (Fin (n + 1) → RationalFiniteAdele) → ℂ :=
    fun y ↦ g (rationalFiniteAdeleCoordinateScale ((c : ℚ))⁻¹ y) with hgt
  have hcar1 : IsStandardCarried 1 gt := isStandardCarried_one_comp_scale hc hcar
  -- the CRT level of `c d`
  set P := (c * d).primeFactors with hPdef
  set e := (c * d).factorization with hedef
  have hP : ∀ p ∈ P, p.Prime ∧ 1 ≤ e p := fun p hp ↦
    ⟨Nat.prime_of_mem_primeFactors hp,
      (Nat.Prime.factorization_pos_of_dvd (Nat.prime_of_mem_primeFactors hp)
        (mul_ne_zero hc hd) (Nat.dvd_of_mem_primeFactors hp))⟩
  have hlevel : localRestrictionLevel P e = c * d :=
    Nat.factorization_prod_pow_eq_self (mul_ne_zero hc hd)
  haveI : NeZero (localRestrictionLevel P e) :=
    ⟨localRestrictionLevel_ne_zero fun p hp ↦ (hP p hp).1⟩
  have hper' : IsStandardPeriodic (localRestrictionLevel P e) gt := by
    rw [hlevel]; exact isStandardPeriodic_mul_comp_scale hc hper
  have hM' : (c : ℤ) ^ 2 * M ≠ 0 := mul_ne_zero (pow_ne_zero 2 (by exact_mod_cast hc)) hM
  have hsing := fun ρ : Fin (n + 1) → ZMod (localRestrictionLevel P e) ↦
    L.exists_forall_tendsto_mul_residueTube_of_eventually_dvd hn hM' P e hP {ρ}
  choose D hD using hsing
  -- the cofinal widths `c² k!`
  set m : ℕ → ℕ := fun k ↦ c ^ 2 * Nat.factorial k with hmdef
  have hm0 : ∀ k, m k ≠ 0 := fun k ↦ mul_ne_zero (pow_ne_zero 2 hc) (Nat.factorial_ne_zero k)
  have hmdvd : ∀ N : ℕ, N ≠ 0 → ∀ᶠ k in atTop, N ∣ m k := fun N hN ↦ by
    filter_upwards [eventually_ge_atTop N] with k hk
    exact (Nat.dvd_factorial (Nat.pos_of_ne_zero hN) hk).mul_left _
  have hcC : (c : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hc
  refine ⟨(c : ℂ) ^ (n + 1) / (c : ℂ) ^ 2 * ∑ ρ, gt (residueFiniteAdeleLift _ ρ) * D ρ, ?_⟩
  have hlim := (tendsto_finset_sum Finset.univ fun ρ _ ↦
    (hD ρ m hm0 hmdvd).const_mul (gt (residueFiniteAdeleLift _ ρ))).const_mul ((c : ℂ) ^ (n + 1) / (c : ℂ) ^ 2)
  refine hlim.congr fun k ↦ ?_
  have hdil := L.finiteTubeMass_mul_sq_eq_dilate g hc (Nat.factorial k) M
  have hT : L.finiteTubeMass g (Nat.factorial k) M =
      (c : ℂ) ^ (n + 1) / (c : ℂ) ^ 2 * L.finiteTubeMass gt (c ^ 2 * Nat.factorial k)
        ((c : ℤ) ^ 2 * M) := by
    rw [div_mul_eq_mul_div, eq_div_iff (pow_ne_zero 2 hcC), hdil]
  rw [hT]
  congr 1
  unfold finiteTubeMass
  have hdecomp : ∀ x, gt x = ∑ ρ, gt (residueFiniteAdeleLift _ ρ) *
      residueRestrictedIndicator (n + 1) (localRestrictionLevel P e) {ρ} x :=
    eq_sum_residueRestrictedIndicator hcar1 hper'
  have hint : (fun x ↦ gt x * rationalFiniteAdeleIntegralIndicator
      (algebraMap ℚ RationalFiniteAdele (((c ^ 2 * Nat.factorial k : ℕ) : ℚ))⁻¹ *
        (L.rationalQuadraticSpaceMatrix.finiteAdelicQuadraticFormValue x -
          algebraMap ℚ RationalFiniteAdele ((((c : ℤ) ^ 2 * M : ℤ)) : ℚ)))) =
      fun x ↦ ∑ ρ, gt (residueFiniteAdeleLift _ ρ) *
        residueRestrictedIndicator (n + 1) (localRestrictionLevel P e) {ρ} x *
          rationalFiniteAdeleIntegralIndicator
            (algebraMap ℚ RationalFiniteAdele (((c ^ 2 * Nat.factorial k : ℕ) : ℚ))⁻¹ *
              (L.rationalQuadraticSpaceMatrix.finiteAdelicQuadraticFormValue x -
                algebraMap ℚ RationalFiniteAdele ((((c : ℤ) ^ 2 * M : ℤ)) : ℚ))) := by
    funext x
    rw [hdecomp x, Finset.sum_mul]
  rw [hint, integral_finset_sum _ fun ρ _ ↦ ?_]
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun ρ _ ↦ ?_
    simp_rw [mul_assoc]
    rw [integral_const_mul]
    ring
  · simp_rw [mul_assoc]
    exact (L.integrable_residueRestrictedIndicator_mul_tube _ _ _ _).const_mul _

end PositiveDefiniteIntegralLattice
