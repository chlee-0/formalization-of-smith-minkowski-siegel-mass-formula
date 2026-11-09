import SMSFormula.BinaryOrderUnitCounts
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Exact trace/norm fibers in the original quadratic algebra

The trace-one case reduces, without dividing by two, to a weighted
idempotent equation. Over prime-power scalar rings its two branches
are measured by the literal scalar annihilator.
-/

noncomputable section

namespace BinaryNormIdeal

variable {R : Type*} [CommRing R]

/-- The literal trace/norm fiber of the original coefficient generator. -/
def TraceNormFiber (T N : R) :=
  {z : CoefficientAlgebra 1 T N //
    Algebra.trace R (CoefficientAlgebra 1 T N) z = T ∧ z.norm = N}

/-- Exact coordinate equations; this works in characteristic two. -/
def traceNormFiberEquivPairs (T N : R) :
    TraceNormFiber T N ≃
      {v : R × R // 2*v.1+T*v.2=T ∧ v.1^2+T*v.1*v.2+N*v.2^2=N} where
  toFun z := ⟨(z.val.re,z.val.im),by
    have ht := z.prop.1
    rw [algebraTrace_eq_coefficients] at ht
    refine ⟨ht,?_⟩
    have hn := z.prop.2
    simp only [CoefficientAlgebra,QuadraticAlgebra.norm_def,neg_mul,one_mul] at hn
    linear_combination hn⟩
  invFun v := ⟨⟨v.val.1,v.val.2⟩,by
    constructor
    · rw [algebraTrace_eq_coefficients]
      exact v.prop.1
    · simp only [QuadraticAlgebra.norm_def,neg_mul,one_mul]
      linear_combination v.prop.2⟩
  left_inv z := by apply Subtype.ext; apply QuadraticAlgebra.ext <;> rfl
  right_inv v := by apply Subtype.ext; rfl

/-- Trace one eliminates the second coordinate integrally. -/
def traceOnePairsEquivWeightedIdempotents (N : R) :
    {v : R × R // 2*v.1+v.2=1 ∧ v.1^2+v.1*v.2+N*v.2^2=N} ≃
      {x : R // (1-4*N)*x*(1-x)=0} where
  toFun v := ⟨v.val.1,by
    have ht := v.prop.1
    have hn := v.prop.2
    linear_combination hn -
      (v.val.1+N*(v.val.2+1-2*v.val.1))*ht⟩
  invFun x := ⟨(x.val,1-2*x.val),by
    constructor
    · ring
    · linear_combination x.prop⟩
  left_inv v := by
    apply Subtype.ext
    change (v.val.1,1-2*v.val.1)=v.val
    apply Prod.ext
    · rfl
    · have h := v.prop.1
      linear_combination -h
  right_inv x := by apply Subtype.ext; rfl

/-- Exact weighted-idempotent reduction of the actual trace-one fiber. -/
def traceOneFiberEquivWeightedIdempotents (N : R) :
    TraceNormFiber (1 : R) N ≃ {x : R // (1-4*N)*x*(1-x)=0} :=
  (traceNormFiberEquivPairs 1 N).trans
    ((Equiv.subtypeEquivRight (fun v => by simp only [one_mul])).trans
      (traceOnePairsEquivWeightedIdempotents N))

/-- In a local scalar ring, the two factors select exactly two
annihilator branches. Nonzero D keeps those branches disjoint. -/
def weightedIdempotentsEquivAnnihilatorSum (D : R) (hD : D≠0)
    (hlocal : ∀ x : R, IsUnit x ∨ IsUnit (1-x)) :
    {x : R // D*x*(1-x)=0} ≃ {x : R // D*x=0} ⊕ {x : R // D*x=0} := by
  classical
  have hbranch (x : R) (hx : D*x*(1-x)=0) : D*x=0 ∨ D*(1-x)=0 := by
    rcases hlocal x with hu | hu
    · right
      apply hu.mul_right_eq_zero.mp
      linear_combination hx
    · left
      exact hu.mul_left_eq_zero.mp hx
  have hdisj (x : R) (hx : D*x=0) : D*(1-x)≠0 := by
    intro hh
    apply hD
    linear_combination hx+hh
  refine
    { toFun := fun x => if hx : D*x.val=0 then Sum.inl ⟨x.val,hx⟩ else
        Sum.inr ⟨1-x.val,(hbranch x.val x.prop).resolve_left hx⟩
      invFun := fun x => match x with
        | Sum.inl a => ⟨a.val,by rw [a.prop,zero_mul]⟩
        | Sum.inr a => ⟨1-a.val,by linear_combination (1-a.val)*a.prop⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro x
    dsimp only
    split_ifs <;> apply Subtype.ext <;> simp
  · intro x
    cases x with
    | inl a => simp only [dif_pos a.prop]
    | inr a =>
      have hh := hdisj a.val a.prop
      simp only [dif_neg hh]
      congr 1
      apply Subtype.ext
      ring

/-- The exact trace-one fiber cardinal before any valuation convention. -/
theorem card_traceOneFiber_eq_twice_annihilator [Finite R]
    (N : R) (hD : 1-4*N≠0) (hlocal : ∀ x : R, IsUnit x ∨ IsUnit (1-x)) :
    Nat.card (TraceNormFiber (1 : R) N) = 2*Nat.card {x : R // (1-4*N)*x=0} := by
  rw [Nat.card_congr (traceOneFiberEquivWeightedIdempotents N),
    Nat.card_congr (weightedIdempotentsEquivAnnihilatorSum _ hD hlocal),Nat.card_sum]
  omega

/-- Scalar prime-power rings inherit the actual local unit alternative. -/
theorem primePower_isUnit_or_one_sub (p : ℕ) [Fact p.Prime] (k : ℕ)
    (x : ZMod (p^k)) : IsUnit x ∨ IsUnit (1-x) := by
  obtain ⟨a,rfl⟩ := toZModPow_surjective p k x
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self a with h | h
  · exact Or.inl (h.map (PadicInt.toZModPow k))
  · right
    simpa only [map_sub,map_one] using h.map (PadicInt.toZModPow k)

/-- Integer multiplication and its absolute natural multiple have the
same zero fiber, over an arbitrary commutative scalar ring. -/
theorem int_mul_eq_zero_iff_natAbs_nsmul (D : ℤ) (x : R) :
    (D : R)*x=0 ↔ D.natAbs • x=0 := by
  cases D with
  | ofNat n => simp [nsmul_eq_mul]
  | negSucc n =>
    change ((Int.negSucc n : ℤ) : R)*x=0 ↔ (n+1) • x=0
    have hc : ((Int.negSucc n : ℤ) : R) = -((n+1 : ℕ) : R) := by
      simp [Int.negSucc_eq]
    rw [hc,nsmul_eq_mul,neg_mul,neg_eq_zero]

/-- The literal scalar annihilator has the exact cyclic-group gcd count. -/
theorem card_int_annihilator_zmod (n : ℕ) [NeZero n] (D : ℤ) :
    Nat.card {x : ZMod n // (D : ZMod n)*x=0} = n.gcd D.natAbs := by
  let e : {x : ZMod n // (D : ZMod n)*x=0} ≃
      (nsmulAddMonoidHom D.natAbs : ZMod n →+ ZMod n).ker :=
    { toFun := fun x => ⟨x.val,(int_mul_eq_zero_iff_natAbs_nsmul D x.val).mp x.prop⟩
      invFun := fun x => ⟨x.val,(int_mul_eq_zero_iff_natAbs_nsmul D x.val).mpr x.prop⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e,IsAddCyclic.card_nsmulAddMonoidHom_ker,Nat.card_zmod]

/-- Every odd original discriminant has this exact trace/norm count at
all positive depths where the discriminant residue is nonzero. -/
theorem card_traceNormFiber_odd_discriminant (p : ℕ) [Fact p.Prime] (k : ℕ)
    (hk : 0<k) (D : ℤ) (hD : D%4=1) (hn : ¬ (p^k : ℕ) ∣ D.natAbs) :
    Nat.card (TraceNormFiber ((D%2 : ℤ) : ZMod (p^k))
      ((((D%2)^2-D)/4 : ℤ) : ZMod (p^k))) = 2*(p^k).gcd D.natAbs := by
  letI : NeZero (p^k) := ⟨by
    obtain ⟨l,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
    exact pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  have hT : D%2=1 := by omega
  have hd := discriminantOrder_coefficients D (Or.inr hD)
  rw [hT] at hd
  norm_num only [one_pow, mul_one] at hd
  have hdelta : (1-4*((1-D)/4 : ℤ) : ℤ)=D := hd
  have hc : (1 : ZMod (p^k))-4*((((1-D)/4 : ℤ) : ZMod (p^k)))=(D : ZMod (p^k)) := by
    have hh := congrArg (fun z : ℤ => (z : ZMod (p^k))) hdelta
    push_cast at hh
    exact hh
  rw [hT,Int.cast_one,one_pow]
  rw [card_traceOneFiber_eq_twice_annihilator _ (by
      rw [hc]
      intro hz
      exact hn (Int.natAbs_dvd_natAbs.mpr ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hz)))
    (primePower_isUnit_or_one_sub p k)]
  rw [hc,card_int_annihilator_zmod]

/-- At a depth at least the exact valuation, the prime-power gcd has
its full valuation thickness. No squarefree hypothesis occurs. -/
theorem gcd_prime_power_eq_padicVal (p : ℕ) [Fact p.Prime]
    (a k : ℕ) (ha : a≠0) (hk : padicValNat p a≤k) :
    (p^k).gcd a = p^(padicValNat p a) := by
  have hp : p.Prime := Fact.out
  obtain ⟨j,hjk,hj⟩ := (Nat.dvd_prime_pow hp).mp (Nat.gcd_dvd_left (p^k) a)
  have hja : p^j ∣ a := by rw [← hj]; exact Nat.gcd_dvd_right _ _
  have hjv : j≤padicValNat p a := (padicValNat_dvd_iff_le ha).mp hja
  have hvj : padicValNat p a≤j := by
    apply (Nat.pow_dvd_pow_iff_le_right hp.one_lt).mp
    rw [← hj]
    exact Nat.dvd_gcd (pow_dvd_pow p hk) pow_padicValNat_dvd
  have he : j=padicValNat p a := by omega
  rw [hj,he]

/-- The reviewed 2*p^v_p(D) fiber count for every odd discriminant,
including arbitrary odd conductor primes and the dyadic place. -/
theorem card_traceNormFiber_odd_discriminant_of_depth (p : ℕ) [Fact p.Prime]
    (k : ℕ) (D : ℤ) (hD : D%4=1) (hk : padicValNat p D.natAbs<k) :
    Nat.card (TraceNormFiber ((D%2 : ℤ) : ZMod (p^k))
      ((((D%2)^2-D)/4 : ℤ) : ZMod (p^k))) = 2*p^(padicValNat p D.natAbs) := by
  have hn : D.natAbs≠0 := by
    intro hh
    have hz : D=0 := Int.natAbs_eq_zero.mp hh
    rw [hz] at hD
    norm_num at hD
  have hnot : ¬p^k ∣ D.natAbs := by
    intro hh
    exact (not_le_of_gt hk) ((padicValNat_dvd_iff_le hn).mp hh)
  rw [card_traceNormFiber_odd_discriminant p k (by omega) D hD hnot,
    gcd_prime_power_eq_padicVal p D.natAbs k hn (Nat.le_of_lt hk)]

/-- If two is invertible in the scalar ring, all generator traces have
an exact weighted-idempotent parameter. This is never used at two. -/
def tracePairsEquivWeightedIdempotents_of_two_inv (T N s : R) (hs : 2*s=1) :
    {v : R × R // 2*v.1+T*v.2=T ∧ v.1^2+T*v.1*v.2+N*v.2^2=N} ≃
      {x : R // (T^2-4*N)*x*(1-x)=0} where
  toFun v := ⟨s*(1-v.val.2),by
    have hx : v.val.1=T*(s*(1-v.val.2)) := by
      linear_combination s*v.prop.1-v.val.1*hs
    have hy : 1-2*(s*(1-v.val.2))=v.val.2 := by
      linear_combination -(1-v.val.2)*hs
    calc
      _ = (T*(s*(1-v.val.2)))^2+T*(T*(s*(1-v.val.2)))*(1-2*(s*(1-v.val.2)))+
          N*(1-2*(s*(1-v.val.2)))^2-N := by ring
      _ = 0 := by rw [← hx,hy,v.prop.2,sub_self]⟩
  invFun x := ⟨(T*x.val,1-2*x.val),by
    constructor
    · ring
    · linear_combination x.prop⟩
  left_inv v := by
    apply Subtype.ext
    change (T*(s*(1-v.val.2)),1-2*(s*(1-v.val.2)))=v.val
    apply Prod.ext
    · linear_combination -s*v.prop.1+v.val.1*hs
    · linear_combination -(1-v.val.2)*hs
  right_inv x := by
    apply Subtype.ext
    change s*(1-(1-2*x.val))=x.val
    linear_combination x.val*hs

/-- Every generator trace when two is a scalar unit has the same exact
annihilator count. No matrix invertibility is asserted. -/
theorem card_traceNormFiber_eq_twice_annihilator_of_two_inv [Finite R]
    (T N s : R) (hs : 2*s=1) (hD : T^2-4*N≠0)
    (hlocal : ∀ x : R, IsUnit x ∨ IsUnit (1-x)) :
    Nat.card (TraceNormFiber T N) = 2*Nat.card {x : R // (T^2-4*N)*x=0} := by
  rw [Nat.card_congr (traceNormFiberEquivPairs T N),
    Nat.card_congr (tracePairsEquivWeightedIdempotents_of_two_inv T N s hs),
    Nat.card_congr (weightedIdempotentsEquivAnnihilatorSum _ hD hlocal),Nat.card_sum]
  omega

/-- All valid discriminants at odd primes, including even original
orders and arbitrary conductor thickness, have the exact gcd fiber. -/
theorem card_traceNormFiber_odd_prime (p : ℕ) [Fact p.Prime] (hp2 : p≠2)
    (k : ℕ) (hk : 0<k) (D : ℤ) (hD : D%4=0 ∨ D%4=1)
    (hn : ¬ (p^k : ℕ) ∣ D.natAbs) :
    Nat.card (TraceNormFiber ((D%2 : ℤ) : ZMod (p^k))
      ((((D%2)^2-D)/4 : ℤ) : ZMod (p^k))) = 2*(p^k).gcd D.natAbs := by
  letI : NeZero (p^k) := ⟨by
    obtain ⟨l,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
    exact pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  have hd := discriminantOrder_coefficients D hD
  have hc : (((D%2 : ℤ) : ZMod (p^k)))^2-
      4*(((((D%2)^2-D)/4 : ℤ) : ZMod (p^k)))=(D : ZMod (p^k)) := by
    have hh := congrArg (fun z : ℤ => (z : ZMod (p^k))) hd
    push_cast at hh
    simpa only [mul_one] using hh
  have hp : p.Prime := Fact.out
  have hu : IsUnit (2 : ZMod (p^k)) :=
    (ZMod.isUnit_iff_coprime 2 (p^k)).mpr (hp.coprime_pow_of_not_dvd (by
      intro hh
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hh)))
  let s := ((hu.unit⁻¹ : (ZMod (p^k))ˣ) : ZMod (p^k))
  have hs : (2 : ZMod (p^k))*s=1 := by
    rw [← hu.unit_spec]
    exact Units.mul_inv hu.unit
  rw [card_traceNormFiber_eq_twice_annihilator_of_two_inv _ _ s hs (by
      rw [hc]
      intro hz
      exact hn (Int.natAbs_dvd_natAbs.mpr ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hz)))
    (primePower_isUnit_or_one_sub p k)]
  rw [hc,card_int_annihilator_zmod]

/-- The reviewed exact trace/norm fiber count at odd primes, with the
original discriminant valuation and explicit sufficient depth. -/
theorem card_traceNormFiber_odd_prime_of_depth (p : ℕ) [Fact p.Prime] (hp2 : p≠2)
    (k : ℕ) (D : ℤ) (hD : D%4=0 ∨ D%4=1) (hD0 : D≠0)
    (hk : padicValNat p D.natAbs<k) :
    Nat.card (TraceNormFiber ((D%2 : ℤ) : ZMod (p^k))
      ((((D%2)^2-D)/4 : ℤ) : ZMod (p^k))) = 2*p^(padicValNat p D.natAbs) := by
  have hn : D.natAbs≠0 := Int.natAbs_ne_zero.mpr hD0
  have hnot : ¬p^k ∣ D.natAbs := by
    intro hh
    exact (not_le_of_gt hk) ((padicValNat_dvd_iff_le hn).mp hh)
  rw [card_traceNormFiber_odd_prime p hp2 k (by omega) D hD hnot,
    gcd_prime_power_eq_padicVal p D.natAbs k hn (Nat.le_of_lt hk)]

private lemma dyadic_ker_toZModPow (k : ℕ) :
    RingHom.ker (PadicInt.toZModPow (p := 2) k)=
      Ideal.span {(2 : ℤ_[2])^k} := by
  simpa only [Nat.cast_ofNat] using (PadicInt.ker_toZModPow (p := 2) k)

/-- At dyadic depth at least two, every element killed by two has square
zero. The proof lifts only scalar elements to the actual p-adic ring. -/
theorem dyadic_square_eq_zero_of_two_mul (k : ℕ) (hk : 2≤k)
    (x : ZMod (2^k)) (hx : 2*x=0) : x^2=0 := by
  obtain ⟨a,rfl⟩ := toZModPow_surjective 2 k x
  have hd : (2 : ℤ_[2])^k ∣ 2*a := by
    rw [← Ideal.mem_span_singleton,← dyadic_ker_toZModPow]
    apply RingHom.mem_ker.mpr
    simpa only [map_mul,map_ofNat] using hx
  obtain ⟨b,hb⟩ := hd
  have he : (2 : ℤ_[2])*a=2*(2^(k-1)*b) := by
    rw [← mul_assoc,← pow_succ',Nat.sub_add_cancel (by omega)]
    exact hb
  have ha : a=(2 : ℤ_[2])^(k-1)*b := mul_left_cancel₀ (by norm_num) he
  have hp : (2 : ℤ_[2])^k ∣ a^2 := by
    rw [ha,mul_pow,← pow_mul]
    exact dvd_mul_of_dvd_left (pow_dvd_pow 2 (by omega : k≤(k-1)*2)) _
  have hz : PadicInt.toZModPow k (a^2)=0 := by
    apply RingHom.mem_ker.mp
    rw [dyadic_ker_toZModPow,Ideal.mem_span_singleton]
    exact hp
  simpa only [map_pow] using hz

/-- Every finite scalar unit has an affine doubling preimage. This is
not a claim about lifting norm-one order units. -/
theorem dyadic_unit_eq_one_sub_two_mul (k : ℕ) (hk : 0<k)
    (y : ZMod (2^k)) (hy : IsUnit y) : ∃ t : ZMod (2^k), 1-2*t=y := by
  obtain ⟨a,ha⟩ := toZModPow_surjective 2 k y
  have hu : IsUnit a := isUnit_of_toZModPow_isUnit 2 k hk a (ha ▸ hy)
  letI : Subsingleton (ZMod (2^1))ˣ := by
    simpa only [pow_one] using (inferInstance : Subsingleton (ZMod 2)ˣ)
  have hmap : (Units.map (PadicInt.toZModPow (p := 2) 1).toMonoidHom) hu.unit=1 :=
    Subsingleton.elim _ _
  have hval : PadicInt.toZModPow 1 a=1 := by
    have h := congrArg Units.val hmap
    simpa only [Units.coe_map,hu.unit_spec,Units.val_one] using h
  have hd : (2 : ℤ_[2]) ∣ 1-a := by
    rw [← Ideal.mem_span_singleton]
    have hm : 1-a ∈ RingHom.ker (PadicInt.toZModPow (p := 2) 1) := by
      apply RingHom.mem_ker.mpr
      rw [map_sub,map_one,hval,sub_self]
    simpa only [dyadic_ker_toZModPow,pow_one] using hm
  obtain ⟨t,ht⟩ := hd
  refine ⟨PadicInt.toZModPow k t,?_⟩
  have hh := congrArg (PadicInt.toZModPow k) ht
  simp only [map_sub,map_one,map_mul,map_ofNat,ha] at hh
  linear_combination hh

/-- Weighted idempotents are exactly a quadratic fiber together with the
kernel of doubling, once the affine preimages exist. -/
def weightedIdempotentsEquivQuadraticFiberProd (N : R)
    (hpre : ∀ y : R, N*(y^2-1)=0 → ∃ t : R, 1-2*t=y) :
    {t : R // (-4*N)*t*(1-t)=0} ≃
      {y : R // N*(y^2-1)=0} × {x : R // 2*x=0} := by
  classical
  let t0 (y : {y : R // N*(y^2-1)=0}) : R := Classical.choose (hpre y.val y.prop)
  have ht (y : {y : R // N*(y^2-1)=0}) : 1-2*t0 y=y.val :=
    Classical.choose_spec (hpre y.val y.prop)
  have hnorm (t : R) : N*((1-2*t)^2-1)=(-4*N)*t*(1-t) := by ring
  let yy (t : {t : R // (-4*N)*t*(1-t)=0}) : {y : R // N*(y^2-1)=0} :=
    ⟨1-2*t.val,by rw [hnorm,t.prop]⟩
  refine
    { toFun := fun t => (yy t,⟨t.val-t0 (yy t),by
        have hh := ht (yy t)
        change 1-2*t0 (yy t)=1-2*t.val at hh
        linear_combination hh⟩)
      invFun := fun z => ⟨t0 z.1+z.2.val,by
        rw [← hnorm]
        have he : 1-2*(t0 z.1+z.2.val)=z.1.val := by
          linear_combination ht z.1- z.2.prop
        rw [he]
        exact z.1.prop⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro t
    apply Subtype.ext
    change t0 (yy t)+(t.val-t0 (yy t))=t.val
    ring
  · intro z
    have he : yy ⟨t0 z.1+z.2.val,by
        rw [← hnorm]
        have hh : 1-2*(t0 z.1+z.2.val)=z.1.val := by
          linear_combination ht z.1-z.2.prop
        rw [hh]
        exact z.1.prop⟩ = z.1 := by
      apply Subtype.ext
      change 1-2*(t0 z.1+z.2.val)=z.1.val
      linear_combination ht z.1-z.2.prop
    apply Prod.ext
    · exact he
    · apply Subtype.ext
      change t0 z.1+z.2.val-t0 (yy _)=z.2.val
      rw [he]
      ring

/-- Trace zero separates the doubling kernel from the quadratic fiber
whenever that kernel squares to zero. -/
def traceZeroPairsEquivQuadraticFiberProd (N : R)
    (hsq : ∀ x : R, 2*x=0 → x^2=0) :
    {v : R × R // 2*v.1=0 ∧ v.1^2+N*v.2^2=N} ≃
      {x : R // 2*x=0} × {y : R // N*(y^2-1)=0} where
  toFun v := (⟨v.val.1,v.prop.1⟩,⟨v.val.2,by
    have hn := v.prop.2
    rw [hsq _ v.prop.1] at hn
    linear_combination hn⟩)
  invFun z := ⟨(z.1.val,z.2.val),⟨z.1.prop,by
    rw [hsq _ z.1.prop]
    linear_combination z.2.prop⟩⟩
  left_inv _ := by apply Subtype.ext; rfl
  right_inv _ := by apply Prod.ext <;> apply Subtype.ext <;> rfl

/-- The dyadic even-order trace/norm fiber has the same weighted-
idempotent count. Both appearances of the doubling kernel are retained. -/
theorem card_traceZeroFiber_eq_weightedIdempotents [Finite R] (N : R)
    (hsq : ∀ x : R, 2*x=0 → x^2=0)
    (hpre : ∀ y : R, N*(y^2-1)=0 → ∃ t : R, 1-2*t=y) :
    Nat.card (TraceNormFiber (0 : R) N) =
      Nat.card {t : R // (-4*N)*t*(1-t)=0} := by
  rw [Nat.card_congr (traceNormFiberEquivPairs 0 N)]
  have e : {v : R × R // 2*v.1+0*v.2=0 ∧ v.1^2+0*v.1*v.2+N*v.2^2=N} ≃
      {v : R × R // 2*v.1=0 ∧ v.1^2+N*v.2^2=N} :=
    Equiv.subtypeEquivRight (fun _ => by simp)
  rw [Nat.card_congr e,Nat.card_congr (traceZeroPairsEquivQuadraticFiberProd N hsq),
    Nat.card_congr (weightedIdempotentsEquivQuadraticFiberProd N hpre),Nat.card_prod,Nat.card_prod]
  exact Nat.mul_comm _ _

/-- The full remaining dyadic fiber for even valid D, at depth at least
two and strictly beyond the valuation, is exactly twice the scalar gcd. -/
theorem card_traceNormFiber_two_even_discriminant (k : ℕ) (hk : 2≤k)
    (D : ℤ) (hD : D%4=0) (hn : ¬ (2^k : ℕ) ∣ D.natAbs) :
    Nat.card (TraceNormFiber ((D%2 : ℤ) : ZMod (2^k))
      ((((D%2)^2-D)/4 : ℤ) : ZMod (2^k))) = 2*(2^k).gcd D.natAbs := by
  letI : NeZero (2^k) := ⟨pow_ne_zero _ (by decide)⟩
  have hT : D%2=0 := by omega
  have hd := discriminantOrder_coefficients D (Or.inl hD)
  rw [hT] at hd
  norm_num only [zero_pow (by decide : (2 : ℕ)≠0),zero_sub,mul_one] at hd
  let N : ZMod (2^k) := ((-D/4 : ℤ) : ZMod (2^k))
  have hc : (-4*N : ZMod (2^k))=(D : ZMod (2^k)) := by
    have hh := congrArg (fun z : ℤ => (z : ZMod (2^k))) hd
    push_cast at hh
    simpa only [N,neg_mul] using hh
  have hnon : (D : ZMod (2^k))≠0 := by
    intro hz
    exact hn (Int.natAbs_dvd_natAbs.mpr ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hz))
  have hN : N≠0 := by intro hz; apply hnon; rw [← hc,hz,mul_zero]
  have hpre : ∀ y : ZMod (2^k), N*(y^2-1)=0 → ∃ t, 1-2*t=y := by
    intro y hy
    have hu : IsUnit y := by
      rcases primePower_isUnit_or_one_sub 2 k (y^2) with h | h
      · exact isUnit_of_mul_isUnit_left (by simpa only [pow_two] using h)
      · exfalso
        apply hN
        apply h.mul_left_eq_zero.mp
        linear_combination -hy
    exact dyadic_unit_eq_one_sub_two_mul k (by omega) y hu
  rw [hT,Int.cast_zero,zero_pow (by decide : (2 : ℕ)≠0),zero_sub]
  change Nat.card (TraceNormFiber (0 : ZMod (2^k)) N)=_
  rw [card_traceZeroFiber_eq_weightedIdempotents N (dyadic_square_eq_zero_of_two_mul k hk) hpre,
    Nat.card_congr (weightedIdempotentsEquivAnnihilatorSum (-4*N) (by rwa [hc])
      (primePower_isUnit_or_one_sub 2 k)),Nat.card_sum]
  rw [hc,card_int_annihilator_zmod]
  omega

/-- The full reviewed trace/norm count for every valid nonzero D and
Every prime at depth beyond v_p(D), with dyadic depth at least two. -/
theorem card_traceNormFiber_prime_power (p : ℕ) [Fact p.Prime] (k : ℕ)
    (D : ℤ) (hD : D%4=0 ∨ D%4=1) (hD0 : D≠0)
    (hk : padicValNat p D.natAbs<k) (hk2 : p=2 → 2≤k) :
    Nat.card (TraceNormFiber ((D%2 : ℤ) : ZMod (p^k))
      ((((D%2)^2-D)/4 : ℤ) : ZMod (p^k))) = 2*p^(padicValNat p D.natAbs) := by
  by_cases hp : p=2
  · subst p
    rcases hD with hD | hD
    · have hn : D.natAbs≠0 := Int.natAbs_ne_zero.mpr hD0
      have hnot : ¬2^k ∣ D.natAbs := by
        intro hh
        exact (not_le_of_gt hk) ((padicValNat_dvd_iff_le hn).mp hh)
      rw [card_traceNormFiber_two_even_discriminant k (hk2 rfl) D hD hnot,
        gcd_prime_power_eq_padicVal 2 D.natAbs k hn (Nat.le_of_lt hk)]
    · exact card_traceNormFiber_odd_discriminant_of_depth 2 k D hD hk
  · exact card_traceNormFiber_odd_prime_of_depth p hp k D hD hD0 hk

/-- Exact executable coefficient-pair carrier for the actual finite
trace/norm fiber; no unit or matrix-invertibility filter is added. -/
def traceNormResiduePairs (n : ℕ) [NeZero n] (D : ℤ) : Finset (ZMod n × ZMod n) :=
  Finset.univ.filter (fun v =>
    2*v.1+((D%2 : ℤ) : ZMod n)*v.2=((D%2 : ℤ) : ZMod n) ∧
    v.1^2+((D%2 : ℤ) : ZMod n)*v.1*v.2+
      ((((D%2)^2-D)/4 : ℤ) : ZMod n)*v.2^2=((((D%2)^2-D)/4 : ℤ) : ZMod n))

/-- The displayed finite count uses the literal algebra trace and norm. -/
theorem card_traceNormFiber_eq_residuePairs (n : ℕ) [NeZero n] (D : ℤ) :
    Nat.card (TraceNormFiber ((D%2 : ℤ) : ZMod n)
      ((((D%2)^2-D)/4 : ℤ) : ZMod n))=(traceNormResiduePairs n D).card := by
  rw [Nat.card_congr (traceNormFiberEquivPairs _ _),Nat.card_eq_fintype_card]
  simp only [traceNormResiduePairs,Fintype.card_subtype]

end BinaryNormIdeal

namespace PositiveDefiniteIntegralLattice

open BinaryNormIdeal

/-- The actual original discriminant has the required fiber count at
the explicit content-adjusted depth h+v_p(D)+3 of the LOCAL proof plan. -/
theorem card_binaryTraceNormFiber_at_contentDepth (K : PositiveDefiniteIntegralLattice 2)
    (p : ℕ) [Fact p.Prime] :
    let k := padicValNat p K.binaryContent+padicValNat p K.binaryPrimitiveDiscriminant.natAbs+3
    Nat.card (TraceNormFiber ((K.binaryPrimitiveDiscriminant%2 : ℤ) : ZMod (p^k))
      ((((K.binaryPrimitiveDiscriminant%2)^2-K.binaryPrimitiveDiscriminant)/4 : ℤ) : ZMod (p^k))) =
        2*p^(padicValNat p K.binaryPrimitiveDiscriminant.natAbs) := by
  dsimp only
  apply card_traceNormFiber_prime_power p _ _ K.binaryPrimitiveDiscriminant_mod_four
    (ne_of_lt K.binaryPrimitiveDiscriminant_neg)
  · omega
  · intro _
    omega

end PositiveDefiniteIntegralLattice

#assert_standard_axioms BinaryNormIdeal.TraceNormFiber
#assert_standard_axioms BinaryNormIdeal.traceNormFiberEquivPairs
#assert_standard_axioms BinaryNormIdeal.traceOnePairsEquivWeightedIdempotents
#assert_standard_axioms BinaryNormIdeal.traceOneFiberEquivWeightedIdempotents
#assert_standard_axioms BinaryNormIdeal.weightedIdempotentsEquivAnnihilatorSum
#assert_standard_axioms BinaryNormIdeal.card_traceOneFiber_eq_twice_annihilator
#assert_standard_axioms BinaryNormIdeal.primePower_isUnit_or_one_sub
#assert_standard_axioms BinaryNormIdeal.int_mul_eq_zero_iff_natAbs_nsmul
#assert_standard_axioms BinaryNormIdeal.card_int_annihilator_zmod
#assert_standard_axioms BinaryNormIdeal.card_traceNormFiber_odd_discriminant

#assert_standard_axioms BinaryNormIdeal.gcd_prime_power_eq_padicVal
#assert_standard_axioms BinaryNormIdeal.card_traceNormFiber_odd_discriminant_of_depth
#assert_standard_axioms BinaryNormIdeal.tracePairsEquivWeightedIdempotents_of_two_inv
#assert_standard_axioms BinaryNormIdeal.card_traceNormFiber_eq_twice_annihilator_of_two_inv
#assert_standard_axioms BinaryNormIdeal.card_traceNormFiber_odd_prime
#assert_standard_axioms BinaryNormIdeal.card_traceNormFiber_odd_prime_of_depth
#assert_standard_axioms BinaryNormIdeal.dyadic_square_eq_zero_of_two_mul
#assert_standard_axioms BinaryNormIdeal.dyadic_unit_eq_one_sub_two_mul
#assert_standard_axioms BinaryNormIdeal.weightedIdempotentsEquivQuadraticFiberProd
#assert_standard_axioms BinaryNormIdeal.traceZeroPairsEquivQuadraticFiberProd
#assert_standard_axioms BinaryNormIdeal.card_traceZeroFiber_eq_weightedIdempotents
#assert_standard_axioms BinaryNormIdeal.card_traceNormFiber_two_even_discriminant
#assert_standard_axioms BinaryNormIdeal.card_traceNormFiber_prime_power
#assert_standard_axioms PositiveDefiniteIntegralLattice.card_binaryTraceNormFiber_at_contentDepth
#assert_standard_axioms BinaryNormIdeal.traceNormResiduePairs
#assert_standard_axioms BinaryNormIdeal.card_traceNormFiber_eq_residuePairs
