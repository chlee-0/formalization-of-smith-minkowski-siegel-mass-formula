import SMSFormula.RationalLatticeCosetResidueCount

/-!
# Class-restricted residue counts are coset counts (dual test, finite combinatorics)

Let `S` be the polar Gram matrix, `d = |det S|` and `u ∈ ℤⁿ`.  The residue class of `adj(S) u` modulo `d`
is parametrized by `t ↦ d t + adj(S) u`, and by the completion of the square without denominators
`q(d t + adj(S) u) = d² (q(t) + uᵀt) + q(adj(S) u)` (`quadForm_det_smul_add_adjugate`):

* `card_adjugateClass_congruence`: at level `d · (d K)`,
  `#{x : q(x) ≡ q(adj(S)u) + d² λ, x ≡ adj(S) u (mod d)} = dⁿ · #{y mod K : q(y) + uᵀy ≡ λ}`;
* `card_adjugateClass_congruence_eq_zero`: if the target is not `≡ q(adj(S)u) (mod d²)`, the count vanishes
  at every level divisible by `d²`.

The fibers of the reduction `(ℤ/kK)ⁿ → (ℤ/K)ⁿ` all have `kⁿ` points (`card_fiber_zmodPiReduce`).
Nothing is chosen.
-/

noncomputable section

open Finset
open scoped Matrix

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-! ## Fibers of the coordinatewise reduction -/

/-- The coordinatewise reduction `(ℤ/kK)ⁿ → (ℤ/K)ⁿ`. -/
def zmodPiReduce (n k K : ℕ) : (Fin n → ZMod (k * K)) →+ (Fin n → ZMod K) :=
  (ZMod.castHom (dvd_mul_left K k) (ZMod K)).toAddMonoidHom.compLeft (Fin n)

theorem zmodPiReduce_apply (k K : ℕ) (y : Fin n → ZMod (k * K)) (i : Fin n) :
    zmodPiReduce n k K y i = ZMod.castHom (dvd_mul_left K k) (ZMod K) (y i) := rfl

theorem zmodPiReduce_surjective (k K : ℕ) [NeZero K] : Function.Surjective (zmodPiReduce n k K) := by
  intro y
  refine ⟨fun i ↦ ((y i).val : ZMod (k * K)), funext fun i ↦ ?_⟩
  rw [zmodPiReduce_apply, map_natCast, ZMod.natCast_zmod_val]

/-- Every fiber of the reduction `(ℤ/kK)ⁿ → (ℤ/K)ⁿ` has `kⁿ` points. -/
theorem card_fiber_zmodPiReduce {k K : ℕ} (hk : k ≠ 0) (hK : K ≠ 0) (y : Fin n → ZMod K) :
    Nat.card {x : Fin n → ZMod (k * K) // zmodPiReduce n k K x = y} = k ^ n := by
  classical
  haveI : NeZero K := ⟨hK⟩
  haveI : NeZero (k * K) := ⟨mul_ne_zero hk hK⟩
  have hsurj := zmodPiReduce_surjective (n := n) k K
  have hall : ∀ y', (univ.filter fun x ↦ zmodPiReduce n k K x = y').card =
      (univ.filter fun x ↦ zmodPiReduce n k K x = y).card := fun y' ↦
    AddMonoidHom.card_fiber_eq_of_mem_range (zmodPiReduce n k K) (hsurj y') (hsurj y)
  have htot : Fintype.card (Fin n → ZMod (k * K)) =
      Fintype.card (Fin n → ZMod K) * (univ.filter fun x ↦ zmodPiReduce n k K x = y).card := by
    rw [← Finset.card_univ, Finset.card_eq_sum_card_fiberwise (f := zmodPiReduce n k K) (t := univ)
      (fun _ _ ↦ mem_univ _)]
    rw [Finset.sum_congr rfl fun y' _ ↦ hall y', sum_const, card_univ, smul_eq_mul]
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have h1 : Fintype.card (Fin n → ZMod (k * K)) = (k * K) ^ n := by
    rw [Fintype.card_fun, ZMod.card, Fintype.card_fin]
  have h2 : Fintype.card (Fin n → ZMod K) = K ^ n := by
    rw [Fintype.card_fun, ZMod.card, Fintype.card_fin]
  rw [h1, h2, mul_pow] at htot
  have hKn : 0 < K ^ n := pow_pos (Nat.pos_of_ne_zero hK) n
  exact (Nat.eq_of_mul_eq_mul_left hKn (by rw [← htot]; ring)).symm

/-- Counting a predicate pulled back along the reduction: `#{x : p(x mod K)} = kⁿ · #{y : p y}`. -/
theorem card_subtype_zmodPiReduce {k K : ℕ} (hk : k ≠ 0) (hK : K ≠ 0)
    (p : (Fin n → ZMod K) → Prop) :
    Nat.card {x : Fin n → ZMod (k * K) // p (zmodPiReduce n k K x)} =
      k ^ n * Nat.card {y : Fin n → ZMod K // p y} := by
  classical
  haveI : NeZero K := ⟨hK⟩
  haveI : NeZero (k * K) := ⟨mul_ne_zero hk hK⟩
  let e : {x : Fin n → ZMod (k * K) // p (zmodPiReduce n k K x)} ≃
      Σ y : {y : Fin n → ZMod K // p y},
        {x : Fin n → ZMod (k * K) // zmodPiReduce n k K x = y.1} :=
    { toFun := fun x ↦ ⟨⟨_, x.2⟩, ⟨x.1, rfl⟩⟩
      invFun := fun w ↦ ⟨w.2.1, by rw [w.2.2]; exact w.1.2⟩
      left_inv := fun x ↦ rfl
      right_inv := fun w ↦ Sigma.subtype_ext (Subtype.ext w.2.2) rfl }
  rw [Nat.card_congr e, Nat.card_sigma]
  simp_rw [card_fiber_zmodPiReduce hk hK]
  rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_comm, Nat.card_eq_fintype_card]

/-! ## The adjugate class and its parametrization -/

/-- The residue of `adj(S) u` modulo `d = |det S|`. -/
def adjugateResidue (L : PositiveDefiniteIntegralLattice n) (u : Fin n → ℤ) :
    Fin n → ZMod L.polarGramMatrix.det.natAbs :=
  fun i ↦ (((L.polarGramMatrix.adjugate *ᵥ u) i : ℤ) : ZMod L.polarGramMatrix.det.natAbs)

/-- The coordinatewise reduction modulo `d` at the level `d · m`. -/
def reduceToDet (L : PositiveDefiniteIntegralLattice n) (m : ℕ) (x : Fin n → ZMod (L.polarGramMatrix.det.natAbs * m)) :
    Fin n → ZMod L.polarGramMatrix.det.natAbs :=
  fun i ↦ ZMod.castHom (dvd_mul_right _ m) (ZMod L.polarGramMatrix.det.natAbs) (x i)

/-- The parametrization `t ↦ d t + adj(S) u` of the class of `adj(S) u`, modulo `d · m`. -/
def adjugateClassParam (L : PositiveDefiniteIntegralLattice n) (u : Fin n → ℤ) (m : ℕ) (t : Fin n → ZMod m) :
    Fin n → ZMod (L.polarGramMatrix.det.natAbs * m) :=
  fun i ↦ (((L.polarGramMatrix.det.natAbs : ℤ) * ((t i).val : ℤ) + (L.polarGramMatrix.adjugate *ᵥ u) i : ℤ) :
    ZMod (L.polarGramMatrix.det.natAbs * m))

theorem natAbs_det_eq (L : PositiveDefiniteIntegralLattice n) : (L.polarGramMatrix.det.natAbs : ℤ) = L.polarGramMatrix.det :=
  Int.natAbs_of_nonneg (show 0 < L.polarGramMatrix.det from L.polarDeterminant_pos).le

theorem natAbs_det_ne_zero (L : PositiveDefiniteIntegralLattice n) : L.polarGramMatrix.det.natAbs ≠ 0 :=
  Int.natAbs_ne_zero.2 L.polarGramMatrix_det_ne_zero

instance natAbs_det_neZero (L : PositiveDefiniteIntegralLattice n) : NeZero L.polarGramMatrix.det.natAbs :=
  ⟨L.natAbs_det_ne_zero⟩

theorem reduceToDet_adjugateClassParam (L : PositiveDefiniteIntegralLattice n) (u : Fin n → ℤ) (m : ℕ)
    (t : Fin n → ZMod m) : L.reduceToDet m (L.adjugateClassParam u m t) = L.adjugateResidue u := by
  funext i
  simp only [reduceToDet, adjugateClassParam, adjugateResidue, map_intCast]
  rw [Int.cast_add, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self, zero_mul, zero_add]

theorem adjugateClassParam_injective (L : PositiveDefiniteIntegralLattice n) (u : Fin n → ℤ) (m : ℕ) [NeZero m] :
    Function.Injective (L.adjugateClassParam u m) := by
  intro t t' h
  funext i
  have hi := congrFun h i
  simp only [adjugateClassParam] at hi
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at hi
  have hd : (L.polarGramMatrix.det.natAbs : ℤ) ≠ 0 := by exact_mod_cast L.natAbs_det_ne_zero
  have h2 : ((L.polarGramMatrix.det.natAbs * m : ℕ) : ℤ) =
      (L.polarGramMatrix.det.natAbs : ℤ) * (m : ℤ) := by rw [Nat.cast_mul]
  rw [h2, show (L.polarGramMatrix.det.natAbs : ℤ) * ((t' i).val : ℤ) + (L.polarGramMatrix.adjugate *ᵥ u) i -
      ((L.polarGramMatrix.det.natAbs : ℤ) * ((t i).val : ℤ) + (L.polarGramMatrix.adjugate *ᵥ u) i) =
      (L.polarGramMatrix.det.natAbs : ℤ) * (((t' i).val : ℤ) - ((t i).val : ℤ)) by ring] at hi
  have hm := (Int.dvd_of_mul_dvd_mul_left hd hi)
  rw [← ZMod.intCast_eq_intCast_iff_dvd_sub] at hm
  simpa using hm

theorem exists_adjugateClassParam_eq (L : PositiveDefiniteIntegralLattice n) (u : Fin n → ℤ) (m : ℕ) [NeZero m]
    (x : Fin n → ZMod (L.polarGramMatrix.det.natAbs * m)) (hx : L.reduceToDet m x = L.adjugateResidue u) :
    ∃ t, L.adjugateClassParam u m t = x := by
  haveI : NeZero (L.polarGramMatrix.det.natAbs * m) := ⟨mul_ne_zero L.natAbs_det_ne_zero (NeZero.ne m)⟩
  have hdiv : ∀ i, (L.polarGramMatrix.det.natAbs : ℤ) ∣
      ((x i).val : ℤ) - (L.polarGramMatrix.adjugate *ᵥ u) i := by
    intro i
    have hi := congrFun hx i
    simp only [reduceToDet, adjugateResidue] at hi
    rw [← ZMod.natCast_zmod_val (x i), map_natCast, ← Int.cast_natCast,
      ZMod.intCast_eq_intCast_iff_dvd_sub] at hi
    have := dvd_neg.2 hi
    rwa [neg_sub] at this
  choose s hs using hdiv
  refine ⟨fun i ↦ ((s i : ℤ) : ZMod m), funext fun i ↦ ?_⟩
  simp only [adjugateClassParam]
  rw [← ZMod.natCast_zmod_val (x i), ← Int.cast_natCast (R := ZMod (L.polarGramMatrix.det.natAbs * m)),
    ZMod.intCast_eq_intCast_iff_dvd_sub]
  have hval : (((s i : ℤ) : ZMod m).val : ℤ) = s i % (m : ℤ) := by
    rw [ZMod.val_intCast]
  rw [hval]
  have hxi : ((x i).val : ℤ) = (L.polarGramMatrix.det.natAbs : ℤ) * s i + (L.polarGramMatrix.adjugate *ᵥ u) i := by
    have := hs i; linarith
  rw [hxi]
  refine ⟨s i / (m : ℤ), ?_⟩
  have hmod := Int.emod_add_mul_ediv (s i) (m : ℤ)
  rw [Nat.cast_mul]
  linear_combination (-(L.polarGramMatrix.det.natAbs : ℤ)) * hmod

/-- The class of `adj(S) u` modulo `d` is parametrized by `t ↦ d t + adj(S) u`. -/
def adjugateClassEquiv (L : PositiveDefiniteIntegralLattice n) (u : Fin n → ℤ) (m : ℕ) [NeZero m] :
    (Fin n → ZMod m) ≃
      {x : Fin n → ZMod (L.polarGramMatrix.det.natAbs * m) // L.reduceToDet m x = L.adjugateResidue u} :=
  Equiv.ofBijective (fun t ↦ ⟨L.adjugateClassParam u m t, L.reduceToDet_adjugateClassParam u m t⟩)
    ⟨fun t t' h ↦ L.adjugateClassParam_injective u m (congrArg Subtype.val h),
      fun x ↦ by
        obtain ⟨t, ht⟩ := L.exists_adjugateClassParam_eq u m x.1 x.2
        exact ⟨t, Subtype.ext ht⟩⟩

/-- The quadratic value along the parametrization: `q(d t + adj(S) u) = d² (q(t) + uᵀt) + q(adj(S) u)`. -/
theorem zmodQuadForm_adjugateClassParam (L : PositiveDefiniteIntegralLattice n) (u : Fin n → ℤ) (m : ℕ)
    (t : Fin n → ZMod m) :
    L.zmodQuadForm (L.polarGramMatrix.det.natAbs * m) (L.adjugateClassParam u m t) =
      ((L.polarGramMatrix.det ^ 2 * (L.quadForm (fun i ↦ ((t i).val : ℤ)) + u ⬝ᵥ (fun i ↦ ((t i).val : ℤ))) +
        L.quadForm (L.polarGramMatrix.adjugate *ᵥ u) : ℤ) : ZMod _) := by
  have h : L.adjugateClassParam u m t = fun i ↦
      (((L.polarGramMatrix.det • (fun i ↦ ((t i).val : ℤ)) + L.polarGramMatrix.adjugate *ᵥ u) i : ℤ) : ZMod _) := by
    funext i
    simp only [adjugateClassParam, Pi.add_apply, Pi.smul_apply, smul_eq_mul, L.natAbs_det_eq]
  rw [h, zmodQuadForm_intCast, quadForm_det_smul_add_adjugate]

set_option maxHeartbeats 800000 in
/-- The class count is a coset count: at level `d · (d K)`, the residues `x ≡ adj(S) u (mod d)` with
`q(x) ≡ q(adj(S) u) + d² λ` are `dⁿ` times the solutions of `q(y) + uᵀy ≡ λ (mod K)`. -/
theorem card_adjugateClass_congruence (L : PositiveDefiniteIntegralLattice n) (u : Fin n → ℤ) (lam : ℤ) {K : ℕ}
    (hK : K ≠ 0) :
    Nat.card {x : Fin n → ZMod (L.polarGramMatrix.det.natAbs * (L.polarGramMatrix.det.natAbs * K)) //
        L.zmodQuadForm _ x = ((L.cosetStandardTarget u lam : ℤ) : ZMod _) ∧
          L.reduceToDet _ x = L.adjugateResidue u} =
      L.polarGramMatrix.det.natAbs ^ n *
        Nat.card {y : Fin n → ZMod K // L.zmodCosetPoly u K y = ((lam : ℤ) : ZMod K)} := by
  classical
  set d : ℕ := L.polarGramMatrix.det.natAbs with hd
  have hd0 : d ≠ 0 := L.natAbs_det_ne_zero
  haveI : NeZero K := ⟨hK⟩
  haveI : NeZero (d * K) := ⟨mul_ne_zero hd0 hK⟩
  -- restrict to the class, then parametrize it
  let e₁ : {x : Fin n → ZMod (d * (d * K)) //
      L.zmodQuadForm _ x = ((L.cosetStandardTarget u lam : ℤ) : ZMod _) ∧
        L.reduceToDet _ x = L.adjugateResidue u} ≃
      {x : {x : Fin n → ZMod (d * (d * K)) // L.reduceToDet _ x = L.adjugateResidue u} //
        L.zmodQuadForm _ x.1 = ((L.cosetStandardTarget u lam : ℤ) : ZMod _)} :=
    { toFun := fun x ↦ ⟨⟨x.1, x.2.2⟩, x.2.1⟩
      invFun := fun x ↦ ⟨x.1.1, x.2, x.1.2⟩
      left_inv := fun x ↦ rfl
      right_inv := fun x ↦ rfl }
  have hiff : ∀ t : Fin n → ZMod (d * K),
      L.zmodCosetPoly u K (zmodPiReduce n d K t) = ((lam : ℤ) : ZMod K) ↔
        L.zmodQuadForm _ (L.adjugateClassEquiv u (d * K) t).1 =
          ((L.cosetStandardTarget u lam : ℤ) : ZMod _) := by
    intro t
    change _ ↔ L.zmodQuadForm _ (L.adjugateClassParam u (d * K) t) = _
    rw [zmodQuadForm_adjugateClassParam, cosetStandardTarget, ZMod.intCast_eq_intCast_iff_dvd_sub]
    set tl : Fin n → ℤ := fun i ↦ ((t i).val : ℤ) with htl
    have hred : zmodPiReduce n d K t = fun i ↦ ((tl i : ℤ) : ZMod K) := by
      funext i
      rw [zmodPiReduce_apply]
      change _ = ((((t i).val : ℕ) : ℤ) : ZMod K)
      rw [Int.cast_natCast, ← map_natCast (ZMod.castHom (dvd_mul_left K d) (ZMod K)),
        ZMod.natCast_zmod_val]
    rw [hred, zmodCosetPoly_intCast, ZMod.intCast_eq_intCast_iff_dvd_sub]
    have hD : (d : ℤ) = L.polarGramMatrix.det := L.natAbs_det_eq
    have hw : ((d * (d * K) : ℕ) : ℤ) = L.polarGramMatrix.det ^ 2 * (K : ℤ) := by
      rw [Nat.cast_mul, Nat.cast_mul, hD]; ring
    rw [hw, show L.quadForm (L.polarGramMatrix.adjugate *ᵥ u) + L.polarGramMatrix.det ^ 2 * lam -
        (L.polarGramMatrix.det ^ 2 * (L.quadForm tl + u ⬝ᵥ tl) + L.quadForm (L.polarGramMatrix.adjugate *ᵥ u)) =
        L.polarGramMatrix.det ^ 2 * (lam - (u ⬝ᵥ tl + L.quadForm tl)) by ring]
    have hD2 : L.polarGramMatrix.det ^ 2 ≠ 0 := pow_ne_zero 2 L.polarGramMatrix_det_ne_zero
    exact ⟨fun h ↦ mul_dvd_mul_left _ h, fun h ↦ Int.dvd_of_mul_dvd_mul_left hD2 h⟩
  rw [Nat.card_congr e₁, ← Nat.card_congr ((L.adjugateClassEquiv u (d * K)).subtypeEquiv hiff)]
  exact card_subtype_zmodPiReduce hd0 hK (fun y ↦ L.zmodCosetPoly u K y = ((lam : ℤ) : ZMod K))

/-- If the target is not `≡ q(adj(S) u) (mod d²)`, the class count vanishes at levels divisible by `d²`. -/
theorem card_adjugateClass_congruence_eq_zero (L : PositiveDefiniteIntegralLattice n) (u : Fin n → ℤ) {M : ℤ}
    (hM : ∀ lam : ℤ, M ≠ L.cosetStandardTarget u lam) {m : ℕ} (hm : m ≠ 0) :
    Nat.card {x : Fin n → ZMod (L.polarGramMatrix.det.natAbs * (L.polarGramMatrix.det.natAbs * m)) //
        L.zmodQuadForm _ x = ((M : ℤ) : ZMod _) ∧ L.reduceToDet _ x = L.adjugateResidue u} = 0 := by
  classical
  haveI : NeZero m := ⟨hm⟩
  haveI : NeZero (L.polarGramMatrix.det.natAbs * m) := ⟨mul_ne_zero L.natAbs_det_ne_zero hm⟩
  rw [Nat.card_eq_zero]
  left
  refine ⟨fun x ↦ ?_⟩
  obtain ⟨t, ht⟩ := L.exists_adjugateClassParam_eq u (L.polarGramMatrix.det.natAbs * m) x.1 x.2.2
  have hQ := x.2.1
  rw [← ht, zmodQuadForm_adjugateClassParam, ZMod.intCast_eq_intCast_iff_dvd_sub] at hQ
  have hD : (L.polarGramMatrix.det.natAbs : ℤ) = L.polarGramMatrix.det := L.natAbs_det_eq
  have hw : ((L.polarGramMatrix.det.natAbs * (L.polarGramMatrix.det.natAbs * m) : ℕ) : ℤ) =
      L.polarGramMatrix.det ^ 2 * (m : ℤ) := by rw [Nat.cast_mul, Nat.cast_mul, hD]; ring
  rw [hw] at hQ
  obtain ⟨c, hc⟩ := dvd_trans (dvd_mul_right _ _) hQ
  apply hM (L.quadForm (fun i ↦ ((t i).val : ℤ)) + u ⬝ᵥ (fun i ↦ ((t i).val : ℤ)) + c)
  unfold cosetStandardTarget
  linear_combination hc

end PositiveDefiniteIntegralLattice
