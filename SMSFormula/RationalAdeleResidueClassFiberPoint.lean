import SMSFormula.RationalAdeleResidueTubeDecomposition
import SMSFormula.RationalAdeleFiniteResidueLocalComponent
import SMSFormula.AdelicGaussianResidueRestrictedOrbitRatioAssembly

/-!
# Residue classes that meet the finite fiber

For the positivity of the rank-four density, a residue class `ρ` at a CRT level whose tube limit is
nonzero must contain a point of the finite fiber `{x ∈ Ẑⁿ : Q_f(x) = M}`.  This file proves the
local part:

* `zmodQuadForm_eq_dotProduct_toZModPow`, `toZModPow_padicQuadratic`: the residue form is the
  reduction of the `p`-adic Gram form;
* `exists_padicInt_eq_and_reduction_of_frequently` (compactness of `ℤ_pⁿ`): if for arbitrarily large
  `k` there is a residue solution modulo `p^k` in a fixed class modulo `p^e`, then there is a
  `p`-adic integral solution in that class.

Nothing is chosen.
-/

noncomputable section

open MeasureTheory Filter Topology RationalQuadraticSpaceMatrix Matrix
open scoped ENNReal

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- The residue form is the `p`-adic Gram form reduced modulo `p^k`. -/
theorem zmodQuadForm_eq_dotProduct_toZModPow (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact p.Prime]
    (k : ℕ) (r : Fin n → ZMod (p ^ k)) :
    L.zmodQuadForm (p ^ k) r =
      r ⬝ᵥ ((L.pairingMatrix.map (Int.castRingHom ℤ_[p])).map (PadicInt.toZModPow k)) *ᵥ r := by
  simp only [zmodQuadForm, dotProduct, mulVec, Matrix.map_apply, eq_intCast, map_intCast,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  ring

/-- Reduction of the `p`-adic Gram form modulo `p^k` is the residue form of the reduction. -/
theorem toZModPow_padicQuadratic (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact p.Prime] (k : ℕ)
    (x : Fin n → ℤ_[p]) :
    PadicInt.toZModPow k (x ⬝ᵥ (L.pairingMatrix.map (Int.castRingHom ℤ_[p])) *ᵥ x) =
      L.zmodQuadForm (p ^ k) (fun j ↦ PadicInt.toZModPow k (x j)) := by
  rw [zmodQuadForm_eq_dotProduct_toZModPow, RingHom.map_dotProduct]
  congr 1
  funext i
  exact RingHom.map_mulVec _ _ _ i

/-- A natural-number lift reduces to itself. -/
theorem toZModPow_natCast_val (p : ℕ) [Fact p.Prime] (k : ℕ) (a : ZMod (p ^ k)) :
    PadicInt.toZModPow k ((a.val : ℕ) : ℤ_[p]) = a := by
  haveI : NeZero (p ^ k) := ⟨pow_ne_zero k (Fact.out : p.Prime).ne_zero⟩
  rw [map_natCast, ZMod.natCast_zmod_val]

/-- Membership in the kernel of the reduction modulo `p^e`, as a norm bound. -/
theorem norm_sub_le_of_toZModPow_eq (p : ℕ) [Fact p.Prime] (e : ℕ) {x y : ℤ_[p]}
    (h : PadicInt.toZModPow e x = PadicInt.toZModPow e y) :
    ‖x - y‖ ≤ (p : ℝ) ^ (-(e : ℤ)) := by
  rw [PadicInt.norm_le_pow_iff_mem_span_pow, ← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub,
    h, sub_self]

theorem toZModPow_eq_of_norm_sub_le (p : ℕ) [Fact p.Prime] (e : ℕ) {x y : ℤ_[p]}
    (h : ‖x - y‖ ≤ (p : ℝ) ^ (-(e : ℤ))) :
    PadicInt.toZModPow e x = PadicInt.toZModPow e y := by
  rw [PadicInt.norm_le_pow_iff_mem_span_pow, ← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub,
    sub_eq_zero] at h
  exact h

/-- Local solvability in a class by compactness: residue solutions modulo arbitrarily large `p^k`
in a fixed class modulo `p^e` give a `p`-adic integral solution in that class. -/
theorem exists_padicInt_eq_and_reduction_of_frequently (L : PositiveDefiniteIntegralLattice n) (p : ℕ)
    [Fact p.Prime] (M : ℤ) (e : ℕ) (ρp : Fin n → ZMod (p ^ e))
    (h : ∀ k₀ : ℕ, ∃ k, k₀ ≤ k ∧ ∃ hk : e ≤ k, ∃ z : Fin n → ZMod (p ^ k),
      L.zmodQuadForm (p ^ k) z = ((M : ℤ) : ZMod (p ^ k)) ∧
        (fun j ↦ ZMod.castHom (pow_dvd_pow p hk) (ZMod (p ^ e)) (z j)) = ρp) :
    ∃ x : Fin n → ℤ_[p],
      x ⬝ᵥ (L.pairingMatrix.map (Int.castRingHom ℤ_[p])) *ᵥ x = ((M : ℤ) : ℤ_[p]) ∧
        (fun j ↦ PadicInt.toZModPow e (x j)) = ρp := by
  classical
  set F := L.pairingMatrix.map (Int.castRingHom ℤ_[p]) with hFdef
  let lift : Fin n → ℤ_[p] := fun j ↦ (((ρp j).val : ℕ) : ℤ_[p])
  have hlift : ∀ j, PadicInt.toZModPow e (lift j) = ρp j := fun j ↦ toZModPow_natCast_val p e _
  let t : ℕ → Set (Fin n → ℤ_[p]) := fun i ↦
    {x | ‖x ⬝ᵥ F *ᵥ x - ((M : ℤ) : ℤ_[p])‖ ≤ (p : ℝ) ^ (-(i : ℤ)) ∧
      ∀ j, ‖x j - lift j‖ ≤ (p : ℝ) ^ (-(e : ℤ))}
  have hQ : Continuous fun x : Fin n → ℤ_[p] ↦ x ⬝ᵥ F *ᵥ x - ((M : ℤ) : ℤ_[p]) := by
    simp only [dotProduct, Matrix.mulVec]
    fun_prop
  have hP : (1 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).one_lt.le
  have htd : ∀ i, t (i + 1) ⊆ t i := by
    intro i x hx
    refine ⟨le_trans hx.1 (zpow_le_zpow_right₀ hP ?_), hx.2⟩
    push_cast
    omega
  have htn : ∀ i, (t i).Nonempty := by
    intro i
    obtain ⟨k, hik, hk, z, hz, hzρ⟩ := h i
    let x : Fin n → ℤ_[p] := fun j ↦ (((z j).val : ℕ) : ℤ_[p])
    have hx : ∀ j, PadicInt.toZModPow k (x j) = z j := fun j ↦ toZModPow_natCast_val p k _
    refine ⟨x, ?_, fun j ↦ ?_⟩
    · have hred : PadicInt.toZModPow k (x ⬝ᵥ F *ᵥ x) =
          PadicInt.toZModPow k ((M : ℤ) : ℤ_[p]) := by
        rw [hFdef, toZModPow_padicQuadratic, map_intCast]
        have hfx : (fun j ↦ PadicInt.toZModPow k (x j)) = z := funext hx
        rw [hfx, hz]
      have hk' := norm_sub_le_of_toZModPow_eq p k hred
      exact le_trans hk' (zpow_le_zpow_right₀ hP (by omega))
    · refine norm_sub_le_of_toZModPow_eq p e ?_
      rw [hlift, ← PadicInt.cast_toZModPow e k hk, hx]
      have := congrFun hzρ j
      rw [ZMod.castHom_apply] at this
      exact this
  have htcl : ∀ i, IsClosed (t i) := by
    intro i
    have hset : t i = {x | ‖x ⬝ᵥ F *ᵥ x - ((M : ℤ) : ℤ_[p])‖ ≤ (p : ℝ) ^ (-(i : ℤ))} ∩
        ⋂ j, {x : Fin n → ℤ_[p] | ‖x j - lift j‖ ≤ (p : ℝ) ^ (-(e : ℤ))} := by
      ext x
      simp only [t, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
    rw [hset]
    refine (isClosed_le (continuous_norm.comp hQ) continuous_const).inter ?_
    exact isClosed_iInter fun j ↦
      isClosed_le (continuous_norm.comp ((continuous_apply j).sub continuous_const)) continuous_const
  obtain ⟨x, hx⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed t htd htn
    (isCompact_univ.of_isClosed_subset (htcl 0) (Set.subset_univ _)) htcl
  rw [Set.mem_iInter] at hx
  refine ⟨x, sub_eq_zero.1 (PadicInt.ext_of_toZModPow.1 fun m ↦ ?_), funext fun j ↦ ?_⟩
  · have hmem := (PadicInt.norm_le_pow_iff_mem_span_pow _ m).1 (hx m).1
    rw [map_zero, ← RingHom.mem_ker, PadicInt.ker_toZModPow]
    exact hmem
  · rw [toZModPow_eq_of_norm_sub_le p e ((hx 0).2 j), hlift]

/-! ## A class without a local solution has eventually vanishing tube masses -/

theorem restrictedResidueCount_le_fullResidueCount (L : PositiveDefiniteIntegralLattice n) (M : ℤ) (P : Finset ℕ)
    (e : ℕ → ℕ) (R : ∀ p : ℕ, Set (Fin n → ZMod (p ^ e p))) (N : ℕ) [NeZero N] :
    L.restrictedResidueCount M P e R N ≤ L.fullResidueCount M N :=
  Nat.card_le_card_of_injective (fun z ↦ ⟨z.1, z.2.1⟩) fun z w h ↦
    Subtype.ext (by simpa using congrArg Subtype.val h)

set_option maxHeartbeats 1600000 in
/-- No local solution in the class at `p ∈ P` ⇒ the restricted counts at every level with large
`p`-adic valuation vanish (CRT through the product identity). -/
theorem eventually_restrictedResidueCount_eq_zero_of_no_local_class_solution (L : PositiveDefiniteIntegralLattice n)
    (M : ℤ) (P : Finset ℕ) (e : ℕ → ℕ) (hP : ∀ p ∈ P, p.Prime ∧ 1 ≤ e p)
    (ρ : Fin n → ZMod (localRestrictionLevel P e)) {p : ℕ} (hp : p ∈ P) [Fact p.Prime]
    (hno : ¬ ∃ x : Fin n → ℤ_[p],
      x ⬝ᵥ (L.pairingMatrix.map (Int.castRingHom ℤ_[p])) *ᵥ x = ((M : ℤ) : ℤ_[p]) ∧
        (fun j ↦ PadicInt.toZModPow (e p) (x j)) =
          fun j ↦ ZMod.castHom (primePow_dvd_localRestrictionLevel hp) (ZMod (p ^ e p)) (ρ j))
    {m : ℕ → ℕ} (hm0 : ∀ k, m k ≠ 0)
    (hv : Tendsto (fun k ↦ (m k).factorization p) atTop atTop) :
    ∀ᶠ k in atTop, L.restrictedResidueCount M P e (localSingletonSets P e ρ) (m k) = 0 := by
  classical
  have hloc : ¬ ∀ k₀ : ℕ, ∃ k, k₀ ≤ k ∧ ∃ hk : e p ≤ k, ∃ z : Fin n → ZMod (p ^ k),
      L.zmodQuadForm (p ^ k) z = ((M : ℤ) : ZMod (p ^ k)) ∧
        (fun j ↦ ZMod.castHom (pow_dvd_pow p hk) (ZMod (p ^ e p)) (z j)) =
          fun j ↦ ZMod.castHom (primePow_dvd_localRestrictionLevel hp) (ZMod (p ^ e p)) (ρ j) :=
    fun h ↦ hno (L.exists_padicInt_eq_and_reduction_of_frequently p M (e p) _ h)
  push_neg at hloc
  obtain ⟨k₀, hk₀⟩ := hloc
  -- the local restricted counts vanish beyond `max k₀ (e p)`
  have hzero : ∀ k, max k₀ (e p) ≤ k →
      L.restrictedResidueCount M P e (localSingletonSets P e ρ) (p ^ k) = 0 := by
    intro k hk
    have hk1 : k₀ ≤ k := le_trans (le_max_left _ _) hk
    have hk2 : e p ≤ k := le_trans (le_max_right _ _) hk
    rw [restrictedResidueCount, Nat.card_eq_zero]
    left
    refine ⟨fun z ↦ ?_⟩
    obtain ⟨z, hz, hadm⟩ := z
    have hmem := hadm p hp (pow_dvd_pow p hk2)
    have heq := hmem hp
    exact hk₀ k hk1 hk2 z hz heq
  filter_upwards [hv.eventually_ge_atTop (max k₀ (e p))] with k hk
  haveI : NeZero (m k) := ⟨hm0 k⟩
  have hprod := L.restrictedResidueCount_mul_prod_eq M P e (localSingletonSets P e ρ) hP (hm0 k)
  have hP0 : (∏ q ∈ P, L.restrictedResidueCount M P e (localSingletonSets P e ρ)
      (q ^ (m k).factorization q)) = 0 := Finset.prod_eq_zero hp (hzero _ hk)
  rw [hP0, mul_zero] at hprod
  rcases mul_eq_zero.1 hprod with h | h
  · exact h
  · obtain ⟨q, hq, hq0⟩ := Finset.prod_eq_zero_iff.1 h
    by_cases hqm : q ∣ m k
    · have hfull : L.fullResidueCount M (m k) = 0 :=
        L.card_residueSet_eq_zero_of_primePow M (hm0 k) (hP q hq).1 hqm hq0
      exact Nat.eq_zero_of_le_zero
        (hfull ▸ L.restrictedResidueCount_le_fullResidueCount M P e _ (m k))
    · have hv0 : (m k).factorization q = 0 := Nat.factorization_eq_zero_of_not_dvd hqm
      rw [hv0, pow_zero] at hq0
      exact absurd hq0 (by rw [fullResidueCount, L.card_residueSet_one M]; exact one_ne_zero)

set_option maxHeartbeats 1600000 in
/-- The tube masses of such a class vanish eventually along divisibility-cofinal widths. -/
theorem eventually_residueTube_eq_zero_of_no_local_class_solution (L : PositiveDefiniteIntegralLattice n)
    (M : ℤ) (P : Finset ℕ) (e : ℕ → ℕ) (hP : ∀ p ∈ P, p.Prime ∧ 1 ≤ e p)
    (ρ : Fin n → ZMod (localRestrictionLevel P e)) {p : ℕ} (hp : p ∈ P) [Fact p.Prime]
    (hno : ¬ ∃ x : Fin n → ℤ_[p],
      x ⬝ᵥ (L.pairingMatrix.map (Int.castRingHom ℤ_[p])) *ᵥ x = ((M : ℤ) : ℤ_[p]) ∧
        (fun j ↦ PadicInt.toZModPow (e p) (x j)) =
          fun j ↦ ZMod.castHom (primePow_dvd_localRestrictionLevel hp) (ZMod (p ^ e p)) (ρ j))
    {m : ℕ → ℕ} (hm0 : ∀ k, m k ≠ 0) (hdvd : ∀ N : ℕ, N ≠ 0 → ∀ᶠ k in atTop, N ∣ m k) :
    haveI : NeZero (localRestrictionLevel P e) :=
      ⟨localRestrictionLevel_ne_zero fun p hp ↦ (hP p hp).1⟩
    ∀ᶠ k in atTop, ((m k : ℕ) : ℂ) *
        ∫ x : Fin n → RationalFiniteAdele,
          residueRestrictedIndicator n (localRestrictionLevel P e) {ρ} x *
            rationalFiniteAdeleIntegralIndicator
              (algebraMap ℚ RationalFiniteAdele (((m k : ℕ) : ℚ))⁻¹ *
                (L.rationalQuadraticSpaceMatrix.finiteAdelicQuadraticFormValue x -
                  algebraMap ℚ RationalFiniteAdele ((M : ℤ) : ℚ)))
          ∂rationalFiniteAdeleCoordinateAddHaarMeasure n = 0 := by
  haveI : NeZero (localRestrictionLevel P e) :=
    ⟨localRestrictionLevel_ne_zero fun p hp ↦ (hP p hp).1⟩
  have hv := tendsto_factorization_of_eventually_dvd hm0 hdvd (hP p hp).1
  filter_upwards [L.eventually_restrictedResidueCount_eq_zero_of_no_local_class_solution M P e hP ρ
    hp hno hm0 hv, hdvd (localRestrictionLevel P e) (NeZero.ne _)] with k hk hdvdk
  rw [← localRestrictionSet_localSingletonSets P e (fun q hq ↦ (hP q hq).1) ρ,
    L.measure_restrictedCongruenceSet_eq_residueCount (hm0 k) hdvdk _ M]
  have hcardR : Nat.card {z : Fin n → ZMod (m k) //
      L.zmodQuadForm (m k) z = ((M : ℤ) : ZMod (m k)) ∧
      (fun i ↦ ZMod.castHom hdvdk (ZMod (localRestrictionLevel P e)) (z i)) ∈
        localRestrictionSet P e (localSingletonSets P e ρ)} =
      L.restrictedResidueCount M P e (localSingletonSets P e ρ) (m k) :=
    Nat.card_congr (Equiv.subtypeEquivRight fun z ↦
      and_congr_right' (castHom_mem_localRestrictionSet_iff P e _ hdvdk z))
  rw [hcardR, hk]
  simp

/-! ## Assembling a finite-adelic fiber point from local solutions -/

open Rat.HeightOneSpectrum in
/-- A `p`-adic integer comes from an integer of the adic completion. -/
theorem padicEquiv_symm_mem_adicCompletionIntegers (v : IsDedekindDomain.HeightOneSpectrum ℤ)
    (a : ℤ_[primesEquiv v]) :
    (adicCompletion.padicEquiv v).symm (a : ℚ_[primesEquiv v]) ∈ v.adicCompletionIntegers ℚ := by
  obtain ⟨b, hb, hba⟩ := (adicCompletion.padicEquiv_bijOn v).surjOn
    (show (a : ℚ_[primesEquiv v]) ∈ PadicInt.subring (primesEquiv v) from a.2)
  rw [← hba, ContinuousAlgEquiv.symm_apply_apply]
  exact hb

open Rat.HeightOneSpectrum in
/-- The integral finite adele with prescribed `ℤ_p` components at every place. -/
def integralFiniteAdeleOfPadic (x : ∀ v : IsDedekindDomain.HeightOneSpectrum ℤ, ℤ_[primesEquiv v]) :
    IntegralFiniteAdele :=
  ⟨RestrictedProduct.structureMap (fun v : IsDedekindDomain.HeightOneSpectrum ℤ ↦ v.adicCompletion ℚ)
      (fun v ↦ (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ))) Filter.cofinite
      (fun v ↦ ⟨(adicCompletion.padicEquiv v).symm (x v : ℚ_[primesEquiv v]),
        padicEquiv_symm_mem_adicCompletionIntegers v (x v)⟩),
    fun v ↦ padicEquiv_symm_mem_adicCompletionIntegers v (x v)⟩

open Rat.HeightOneSpectrum in
theorem integralFiniteAdelePadicComponent_ofPadic
    (x : ∀ v : IsDedekindDomain.HeightOneSpectrum ℤ, ℤ_[primesEquiv v])
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    integralFiniteAdelePadicComponent v (integralFiniteAdeleOfPadic x) = x v := by
  apply Subtype.ext
  rw [coe_integralFiniteAdelePadicComponent]
  change (adicCompletion.padicEquiv v) ((adicCompletion.padicEquiv v).symm (x v : ℚ_[primesEquiv v])) = _
  rw [ContinuousAlgEquiv.apply_symm_apply]

open Rat.HeightOneSpectrum in
/-- The assembled point Lies on the finite fiber: local solutions `Q(x_v) = M` at every place give
`Q_f(y) = M` for the assembled integral vector. -/
theorem finiteAdelicQuadraticFormValue_ofPadic (L : PositiveDefiniteIntegralLattice n) (M : ℤ)
    (x : ∀ v : IsDedekindDomain.HeightOneSpectrum ℤ, Fin n → ℤ_[primesEquiv v])
    (hx : ∀ v, x v ⬝ᵥ (L.pairingMatrix.map (Int.castRingHom ℤ_[primesEquiv v])) *ᵥ x v =
      ((M : ℤ) : ℤ_[primesEquiv v])) :
    L.rationalQuadraticSpaceMatrix.finiteAdelicQuadraticFormValue
        (fun i ↦ ((integralFiniteAdeleOfPadic fun v ↦ x v i : IntegralFiniteAdele) :
          RationalFiniteAdele)) =
      algebraMap ℚ RationalFiniteAdele ((M : ℤ) : ℚ) := by
  ext v
  suffices hv : (adicCompletion.padicEquiv v) (L.rationalQuadraticSpaceMatrix.finiteAdelicQuadraticFormValue
      (fun i ↦ ((integralFiniteAdeleOfPadic fun v ↦ x v i : IntegralFiniteAdele) :
        RationalFiniteAdele)) v) =
      (adicCompletion.padicEquiv v) ((algebraMap ℚ RationalFiniteAdele ((M : ℤ) : ℚ)) v) from
    (adicCompletion.padicEquiv v).injective hv
  rw [padicEquiv_finiteAdelicQuadraticFormValue,
    IntegralFiniteAdelePhase.commutativeScalarExtensionQuadraticForm_padic_eq L]
  have hcomp : (fun i ↦ (adicCompletion.padicEquiv v)
      (((integralFiniteAdeleOfPadic fun w ↦ x w i : IntegralFiniteAdele) : RationalFiniteAdele) v)) =
      fun i ↦ ((x v i : ℤ_[primesEquiv v]) : ℚ_[primesEquiv v]) := by
    funext i
    rw [← coe_integralFiniteAdelePadicComponent, integralFiniteAdelePadicComponent_ofPadic]
  rw [hcomp]
  have hrhs : (adicCompletion.padicEquiv v) ((algebraMap ℚ RationalFiniteAdele ((M : ℤ) : ℚ)) v) =
      (((M : ℤ) : ℤ_[primesEquiv v]) : ℚ_[primesEquiv v]) := by
    change (adicCompletion.padicEquiv v) (algebraMap ℚ (v.adicCompletion ℚ) ((M : ℤ) : ℚ)) = _
    rw [map_intCast, map_intCast, PadicInt.coe_intCast]
  rw [hrhs, ← hx v, Matrix.toQuadraticMap', Matrix.toQuadraticForm', LinearMap.BilinMap.toQuadraticMap_apply,
    Matrix.toLinearMap₂'_apply']
  have hc : (fun i ↦ ((x v i : ℤ_[primesEquiv v]) : ℚ_[primesEquiv v])) =
      (PadicInt.Coe.ringHom : ℤ_[primesEquiv v] →+* ℚ_[primesEquiv v]) ∘ x v := rfl
  change _ = (PadicInt.Coe.ringHom : ℤ_[primesEquiv v] →+* ℚ_[primesEquiv v]) _
  rw [hc, RingHom.map_dotProduct]
  congr 1
  funext i
  exact (RingHom.map_mulVec _ _ _ i).symm

open Rat.HeightOneSpectrum in
/-- The assembled point Lies in the prescribed class when its components reduce correctly over `P`. -/
theorem integralVectorResidue_ofPadic_eq (P : Finset ℕ) (e : ℕ → ℕ) (hP : ∀ p ∈ P, p.Prime)
    (ρ : Fin n → ZMod (localRestrictionLevel P e))
    (x : ∀ v : IsDedekindDomain.HeightOneSpectrum ℤ, Fin n → ℤ_[primesEquiv v])
    (hred : ∀ v (hv : (primesEquiv v : ℕ) ∈ P),
      (fun j ↦ PadicInt.toZModPow (e (primesEquiv v)) (x v j)) =
        fun j ↦ ZMod.castHom (primePow_dvd_localRestrictionLevel hv)
          (ZMod ((primesEquiv v : ℕ) ^ e (primesEquiv v))) (ρ j)) :
    haveI : NeZero (localRestrictionLevel P e) := ⟨localRestrictionLevel_ne_zero hP⟩
    integralVectorResidue n (localRestrictionLevel P e)
      (fun i ↦ integralFiniteAdeleOfPadic fun v ↦ x v i) = ρ := by
  haveI : NeZero (localRestrictionLevel P e) := ⟨localRestrictionLevel_ne_zero hP⟩
  have hmem : integralVectorResidue n (localRestrictionLevel P e)
      (fun i ↦ integralFiniteAdeleOfPadic fun v ↦ x v i) ∈
        localRestrictionSet P e (localSingletonSets P e ρ) := by
    rw [integralVectorResidue_mem_localRestrictionSet_iff P e _ hP]
    intro v hv hv'
    have hc : (fun i ↦ integralFiniteAdelePadicComponent v
        (integralFiniteAdeleOfPadic fun w ↦ x w i)) = x v := by
      funext i
      exact integralFiniteAdelePadicComponent_ofPadic _ v
    rw [hc]
    funext j
    exact congrFun (hred v hv') j
  rwa [localRestrictionSet_localSingletonSets P e hP ρ, Set.mem_singleton_iff] at hmem

/-! ## The dichotomy -/

open Rat.HeightOneSpectrum in
set_option maxHeartbeats 1600000 in
/-- A residue class either meets the finite fiber or has eventually vanishing tube masses along every
divisibility-cofinal width sequence. -/
theorem exists_fiberPoint_or_eventually_residueTube_eq_zero (L : PositiveDefiniteIntegralLattice n) (M : ℤ)
    (P : Finset ℕ) (e : ℕ → ℕ) (hP : ∀ p ∈ P, p.Prime ∧ 1 ≤ e p)
    (ρ : Fin n → ZMod (localRestrictionLevel P e))
    {m : ℕ → ℕ} (hm0 : ∀ k, m k ≠ 0) (hdvd : ∀ N : ℕ, N ≠ 0 → ∀ᶠ k in atTop, N ∣ m k) :
    haveI : NeZero (localRestrictionLevel P e) :=
      ⟨localRestrictionLevel_ne_zero fun p hp ↦ (hP p hp).1⟩
    (∃ y : Fin n → IntegralFiniteAdele,
        integralVectorResidue n (localRestrictionLevel P e) y = ρ ∧
        L.rationalQuadraticSpaceMatrix.finiteAdelicQuadraticFormValue
            (fun i ↦ ((y i : IntegralFiniteAdele) : RationalFiniteAdele)) =
          algebraMap ℚ RationalFiniteAdele ((M : ℤ) : ℚ)) ∨
      ∀ᶠ k in atTop, ((m k : ℕ) : ℂ) *
        ∫ x : Fin n → RationalFiniteAdele,
          residueRestrictedIndicator n (localRestrictionLevel P e) {ρ} x *
            rationalFiniteAdeleIntegralIndicator
              (algebraMap ℚ RationalFiniteAdele (((m k : ℕ) : ℚ))⁻¹ *
                (L.rationalQuadraticSpaceMatrix.finiteAdelicQuadraticFormValue x -
                  algebraMap ℚ RationalFiniteAdele ((M : ℤ) : ℚ)))
          ∂rationalFiniteAdeleCoordinateAddHaarMeasure n = 0 := by
  haveI : NeZero (localRestrictionLevel P e) :=
    ⟨localRestrictionLevel_ne_zero fun p hp ↦ (hP p hp).1⟩
  classical
  by_cases hall : ∀ v : IsDedekindDomain.HeightOneSpectrum ℤ, ∃ x : Fin n → ℤ_[primesEquiv v],
      x ⬝ᵥ (L.pairingMatrix.map (Int.castRingHom ℤ_[primesEquiv v])) *ᵥ x =
        ((M : ℤ) : ℤ_[primesEquiv v]) ∧
      ∀ hv : (primesEquiv v : ℕ) ∈ P,
        (fun j ↦ PadicInt.toZModPow (e (primesEquiv v)) (x j)) =
          fun j ↦ ZMod.castHom (primePow_dvd_localRestrictionLevel hv)
            (ZMod ((primesEquiv v : ℕ) ^ e (primesEquiv v))) (ρ j)
  · left
    choose x hx hred using hall
    exact ⟨fun i ↦ integralFiniteAdeleOfPadic fun v ↦ x v i,
      integralVectorResidue_ofPadic_eq P e (fun p hp ↦ (hP p hp).1) ρ x hred,
      finiteAdelicQuadraticFormValue_ofPadic L M x hx⟩
  · right
    push_neg at hall
    obtain ⟨v, hv⟩ := hall
    haveI : Fact ((primesEquiv v : ℕ)).Prime := ⟨(primesEquiv v).2⟩
    by_cases hvP : (primesEquiv v : ℕ) ∈ P
    · refine L.eventually_residueTube_eq_zero_of_no_local_class_solution M P e hP ρ hvP ?_ hm0 hdvd
      rintro ⟨x, hx, hxr⟩
      obtain ⟨hv', hne⟩ := hv x hx
      exact hne hxr
    · refine L.eventually_restrictedTube_eq_zero_of_not_represented_of_dvd {ρ} M
        (primesEquiv v : ℕ) ?_ hm0 hdvd
      rintro ⟨x, hx⟩
      obtain ⟨hv', -⟩ := hv x hx
      exact hvP hv'

end PositiveDefiniteIntegralLattice
