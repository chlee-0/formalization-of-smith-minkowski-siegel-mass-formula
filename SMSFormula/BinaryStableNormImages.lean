import SMSFormula.BinaryResidueNormImage

/-!
# Actual norm quotients at every stable prime-power depth

The finite quadratic-algebra norm quotient agrees with the original local
order-unit norm quotient at depth k>=1 for odd p and k>=3 at two.
No norm-one lifting statement is assumed. Finite kernel cardinalities
are obtained by the group homomorphism theorem.
-/

noncomputable section

namespace BinaryNormIdeal

/-- The coefficient map on actual units for any scalar ring homomorphism. -/
def discriminantAlgebraUnitsMap {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (D : ℤ) : (DiscriminantAlgebra R D)ˣ →* (DiscriminantAlgebra S D)ˣ :=
  Units.map (discriminantAlgebraMap f D).toMonoidHom

/-- Coefficient lifts of finite-order units are units whenever scalar
reduction is onto and reflects units. -/
theorem discriminantAlgebraUnitsMap_surjective {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : Function.Surjective f)
    (hunit : ∀ x, IsUnit (f x) → IsUnit x) (D : ℤ) :
    Function.Surjective (discriminantAlgebraUnitsMap f D) := by
  intro u
  obtain ⟨x,hx⟩ := hf u.val.re
  obtain ⟨y,hy⟩ := hf u.val.im
  let z : DiscriminantAlgebra R D := ⟨x,y⟩
  have hz : discriminantAlgebraMap f D z=u.val := QuadraticAlgebra.ext hx hy
  have hn : IsUnit (f z.norm) := by
    rw [discriminantAlgebraMap_norm,hz]
    exact QuadraticAlgebra.isUnit_iff_norm_isUnit.mp u.isUnit
  have hu : IsUnit z := QuadraticAlgebra.isUnit_iff_norm_isUnit.mpr (hunit _ hn)
  refine ⟨hu.unit,?_⟩
  apply Units.ext
  change discriminantAlgebraMap f D (hu.unit : DiscriminantAlgebra R D)=u.val
  rw [hu.unit_spec,hz]

/-- Norm commutes with coefficient base change on actual units. -/
theorem discriminantAlgebraUnitsMap_norm {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (D : ℤ) (z : (DiscriminantAlgebra R D)ˣ) :
    Units.map f.toMonoidHom (orderUnitNorm R D z)=
      orderUnitNorm S D (discriminantAlgebraUnitsMap f D z) := by
  apply Units.ext
  exact discriminantAlgebraMap_norm f D z.val

/-- Every scalar residue modulo p^k has an actual integral lift. -/
theorem toZModPow_surjective (p : ℕ) [Fact p.Prime] (k : ℕ) :
    Function.Surjective (PadicInt.toZModPow (p := p) k) := by
  intro z
  refine ⟨(z.val : ℤ_[p]),?_⟩
  simpa only [map_natCast] using ZMod.natCast_zmod_val z

/-- Scalar reduction at positive depth reflects units. -/
theorem isUnit_of_toZModPow_isUnit (p : ℕ) [Fact p.Prime] (k : ℕ) (hk : 0<k)
    (x : ℤ_[p]) (hx : IsUnit (PadicInt.toZModPow k x)) : IsUnit x := by
  by_contra hn
  have hd : (p : ℤ_[p]) ∣ x := by
    rw [← Ideal.mem_span_singleton,← PadicInt.maximalIdeal_eq_span_p]
    exact (IsLocalRing.mem_maximalIdeal x).mpr hn
  obtain ⟨y,rfl⟩ := hd
  have hu : IsUnit (p : ZMod (p^k)) :=
    isUnit_of_mul_isUnit_left (by simpa only [map_mul,map_natCast] using hx)
  have hc := (ZMod.isUnit_iff_coprime p (p^k)).mp hu
  have h := Nat.dvd_gcd (dvd_refl p) (dvd_pow_self p (Nat.ne_of_gt hk))
  rw [hc.gcd_eq_one] at h
  exact (Fact.out : p.Prime).ne_one (Nat.dvd_one.mp h)

/-- Reduction of actual scalar units at any depth. -/
def scalarPowResidueUnits (p : ℕ) [Fact p.Prime] (k : ℕ) :
    ℤ_[p]ˣ →* (ZMod (p^k))ˣ := Units.map (PadicInt.toZModPow k).toMonoidHom

theorem scalarPowResidueUnits_surjective (p : ℕ) [Fact p.Prime] (k : ℕ) (hk : 0<k) :
    Function.Surjective (scalarPowResidueUnits p k) := by
  intro u
  obtain ⟨x,hx⟩ := toZModPow_surjective p k u.val
  have hu : IsUnit x := isUnit_of_toZModPow_isUnit p k hk x (hx ▸ u.isUnit)
  refine ⟨hu.unit,?_⟩
  apply Units.ext
  change PadicInt.toZModPow k (hu.unit : ℤ_[p])=u.val
  rw [hu.unit_spec,hx]

/-- Actual order units reduce onto all finite order units at positive depth. -/
theorem orderPowResidueUnits_surjective (p : ℕ) [Fact p.Prime] (k : ℕ) (hk : 0<k) (D : ℤ) :
    Function.Surjective (discriminantAlgebraUnitsMap (PadicInt.toZModPow (p := p) k) D) :=
  discriminantAlgebraUnitsMap_surjective _ (toZModPow_surjective p k)
    (isUnit_of_toZModPow_isUnit p k hk) D

/-- The scalar reduction kernel consists of integral squares at stable depth. -/
theorem isSquare_of_scalarPowResidueUnits_eq_one (p : ℕ) [Fact p.Prime]
    (k : ℕ) (hk : 0<k) (hk2 : p=2 → 3≤k) (u : ℤ_[p]ˣ)
    (hu : scalarPowResidueUnits p k u=1) : IsSquare (u : ℤ_[p]) := by
  have h := congrArg Units.val hu
  change PadicInt.toZModPow k (u : ℤ_[p])=1 at h
  have hdiv : (p : ℤ_[p])^k ∣ (u : ℤ_[p])-1 := by
    rw [← Ideal.mem_span_singleton,← PadicInt.ker_toZModPow]
    apply RingHom.mem_ker.mpr
    rw [map_sub,map_one,h,sub_self]
  by_cases hp : p=2
  · subst p
    have hr : PadicInt.toZModPow 3 (u : ℤ_[2])=1 := by
      have hd : (2 : ℤ_[2])^3 ∣ (u : ℤ_[2])-1 :=
        dvd_trans (pow_dvd_pow 2 (hk2 rfl)) hdiv
      have hz : PadicInt.toZModPow 3 ((u : ℤ_[2])-1)=0 := by
        apply RingHom.mem_ker.mp
        rw [PadicInt.ker_toZModPow,Ideal.mem_span_singleton]
        exact hd
      simpa only [map_sub,map_one,sub_eq_zero] using hz
    exact (PadicInt.isSquare_coe_iff_isSquare_of_isUnit u.isUnit).mp
      ((PadicInt.isSquare_coe_iff_toZModPow_three_eq_one_of_isUnit u.isUnit).mpr hr)
  · have hr : PadicInt.toZMod (u : ℤ_[p])=1 := by
      have hd : (p : ℤ_[p]) ∣ (u : ℤ_[p])-1 :=
        dvd_trans (dvd_pow_self (p : ℤ_[p]) (Nat.ne_of_gt hk)) hdiv
      have hz : PadicInt.toZMod ((u : ℤ_[p])-1)=0 := by
        apply RingHom.mem_ker.mp
        rw [PadicInt.ker_toZMod,PadicInt.maximalIdeal_eq_span_p,Ideal.mem_span_singleton]
        exact hd
      simpa only [map_sub,map_one,sub_eq_zero] using hz
    apply (PadicInt.isSquare_iff_isSquare_toZMod_of_isUnit hp u.isUnit).mpr
    rw [hr]
    exact ⟨1,by simp⟩

/-- At stable depth the kernel is in the actual order-unit norm subgroup. -/
theorem scalarPowResidueUnits_ker_le (p : ℕ) [Fact p.Prime] (k : ℕ)
    (hk : 0<k) (hk2 : p=2 → 3≤k) (D : ℤ) :
    (scalarPowResidueUnits p k).ker ≤ orderUnitNormSubgroup ℤ_[p] D := by
  intro u hu
  exact mem_orderUnitNormSubgroup_of_isSquare _ _ u
    (isSquare_of_scalarPowResidueUnits_eq_one p k hk hk2 u hu)

/-- Exact image equality at every positive prime-power depth. -/
theorem orderUnitNormSubgroup_map_pow (p : ℕ) [Fact p.Prime] (k : ℕ) (hk : 0<k) (D : ℤ) :
    (orderUnitNormSubgroup ℤ_[p] D).map (scalarPowResidueUnits p k)=
      orderUnitNormSubgroup (ZMod (p^k)) D := by
  ext u
  constructor
  · rintro ⟨v,⟨z,rfl⟩,rfl⟩
    exact ⟨discriminantAlgebraUnitsMap (PadicInt.toZModPow k) D z,
      (discriminantAlgebraUnitsMap_norm (PadicInt.toZModPow k) D z).symm⟩
  · rintro ⟨z,rfl⟩
    obtain ⟨w,rfl⟩ := orderPowResidueUnits_surjective p k hk D z
    exact ⟨orderUnitNorm ℤ_[p] D w,⟨w,rfl⟩,
      discriminantAlgebraUnitsMap_norm (PadicInt.toZModPow k) D w⟩

/-- The original norm quotient is the finite norm quotient at every stable depth. -/
def orderUnitNormQuotientEquivPow (p : ℕ) [Fact p.Prime] (k : ℕ)
    (hk : 0<k) (hk2 : p=2 → 3≤k) (D : ℤ) :
    OrderUnitNormQuotient ℤ_[p] D ≃* OrderUnitNormQuotient (ZMod (p^k)) D := by
  let f := (QuotientGroup.mk' (orderUnitNormSubgroup (ZMod (p^k)) D)).comp
    (scalarPowResidueUnits p k)
  apply QuotientGroup.liftEquiv (φ := f) (orderUnitNormSubgroup ℤ_[p] D)
    ((QuotientGroup.mk'_surjective _).comp (scalarPowResidueUnits_surjective p k hk))
  dsimp only [f]
  rw [← MonoidHom.comap_ker,QuotientGroup.ker_mk',← orderUnitNormSubgroup_map_pow p k hk D]
  exact (Subgroup.comap_map_eq_self (scalarPowResidueUnits_ker_le p k hk hk2 D)).symm

theorem card_orderUnitNormQuotient_eq_pow (p : ℕ) [Fact p.Prime] (k : ℕ)
    (hk : 0<k) (hk2 : p=2 → 3≤k) (D : ℤ) :
    Nat.card (OrderUnitNormQuotient ℤ_[p] D)=
      Nat.card (OrderUnitNormQuotient (ZMod (p^k)) D) :=
  Nat.card_congr (orderUnitNormQuotientEquivPow p k hk hk2 D).toEquiv


/-- The finite homomorphism theorem keeps the actual norm-one kernel.
The cross-multiplied identity avoids division by any cardinal. -/
theorem card_orderUnitNorm_ker_mul_scalarUnits (R : Type*) [CommRing R] (D : ℤ) :
    Nat.card (orderUnitNorm R D).ker * Nat.card Rˣ =
      Nat.card (OrderUnitNormQuotient R D) * Nat.card (DiscriminantAlgebra R D)ˣ := by
  have h1 := (orderUnitNorm R D).ker.card_eq_card_quotient_mul_card_subgroup
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange (orderUnitNorm R D)).toEquiv] at h1
  have h2 := (orderUnitNormSubgroup R D).card_eq_card_quotient_mul_card_subgroup
  change Nat.card Rˣ=Nat.card (OrderUnitNormQuotient R D)*Nat.card (orderUnitNorm R D).range at h2
  rw [h1,h2]
  ring

/-- At every stable depth the local norm index supplies the exact finite
norm-one kernel count, retaining the literal finite order-unit numerator. -/
theorem card_orderUnitNorm_ker_pow_mul_scalarUnits (p : ℕ) [Fact p.Prime] (k : ℕ)
    (hk : 0<k) (hk2 : p=2 → 3≤k) (D : ℤ) :
    Nat.card (orderUnitNorm (ZMod (p^k)) D).ker * Nat.card (ZMod (p^k))ˣ =
      Nat.card (OrderUnitNormQuotient ℤ_[p] D) *
        Nat.card (DiscriminantAlgebra (ZMod (p^k)) D)ˣ := by
  rw [card_orderUnitNormQuotient_eq_pow p k hk hk2 D]
  exact card_orderUnitNorm_ker_mul_scalarUnits _ D

/-- Norm-one elements and the actual unit norm kernel are in bijection.
A norm-one element is a unit by its literal norm; no lift is used. -/
def orderUnitNormKernelEquivNormOne (R : Type*) [CommRing R] (D : ℤ) :
    (orderUnitNorm R D).ker ≃ {z : DiscriminantAlgebra R D // z.norm=1} :=
  Equiv.ofBijective (fun z => ⟨z.val.val,congrArg Units.val z.prop⟩) (by
    constructor
    · intro x y h
      apply Subtype.ext
      apply Units.ext
      exact congrArg Subtype.val h
    · rintro ⟨z,hz⟩
      have hu : IsUnit z := QuadraticAlgebra.isUnit_iff_norm_isUnit.mpr (hz ▸ isUnit_one)
      refine ⟨⟨hu.unit,?_⟩,?_⟩
      · apply Units.ext
        change (hu.unit : DiscriminantAlgebra R D).norm=1
        rw [hu.unit_spec,hz]
      · exact Subtype.ext hu.unit_spec)

/-- Explicit norm-one coefficient pairs in the finite original order. -/
def normOneResiduePairs (n : ℕ) [NeZero n] (D : ℤ) : Finset (ZMod n × ZMod n) :=
  Finset.univ.filter fun z =>
    (QuadraticAlgebra.mk z.1 z.2 : DiscriminantAlgebra (ZMod n) D).norm=1

/-- Coordinate bijection for the finite norm-one elements. -/
def normOneElementsEquivPairs (n : ℕ) [NeZero n] (D : ℤ) :
    {z : DiscriminantAlgebra (ZMod n) D // z.norm=1} ≃
      {z : ZMod n × ZMod n //
        (QuadraticAlgebra.mk z.1 z.2 : DiscriminantAlgebra (ZMod n) D).norm=1} where
  toFun z := ⟨(z.val.re,z.val.im),z.prop⟩
  invFun z := ⟨⟨z.val.1,z.val.2⟩,z.prop⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The finite norm-one kernel has the exact explicit coefficient count. -/
theorem card_orderUnitNorm_ker_eq_normOneResiduePairs (n : ℕ) [NeZero n] (D : ℤ) :
    Nat.card (orderUnitNorm (ZMod n) D).ker=(normOneResiduePairs n D).card := by
  rw [Nat.card_congr ((orderUnitNormKernelEquivNormOne (ZMod n) D).trans
    (normOneElementsEquivPairs n D))]
  simp only [Nat.card_eq_fintype_card,Fintype.card_subtype,normOneResiduePairs]


/-- The finite original quadratic algebra has exactly two finite coordinates. -/
theorem finite_discriminantAlgebra_residue (n : ℕ) [NeZero n] (D : ℤ) :
    Finite (DiscriminantAlgebra (ZMod n) D) :=
  Finite.of_equiv _ (QuadraticAlgebra.equivProd _ _).symm

/-- The actual finite norm-one kernel is finite and nonempty. -/
theorem card_orderUnitNorm_ker_residue_pos (n : ℕ) [NeZero n] (D : ℤ) :
    0<Nat.card (orderUnitNorm (ZMod n) D).ker := by
  letI := finite_discriminantAlgebra_residue n D
  exact Nat.card_pos

/-- The scalar unit denominator is evaluated exactly at every stable depth. -/
theorem card_orderUnitNorm_ker_pow_mul_primeUnits (p : ℕ) [Fact p.Prime] (k : ℕ)
    (hk : 0<k) (hk2 : p=2 → 3≤k) (D : ℤ) :
    Nat.card (orderUnitNorm (ZMod (p^k)) D).ker * (p^(k-1)*(p-1)) =
      Nat.card (OrderUnitNormQuotient ℤ_[p] D) *
        Nat.card (DiscriminantAlgebra (ZMod (p^k)) D)ˣ := by
  have hc : Nat.card (ZMod (p^k))ˣ=p^(k-1)*(p-1) := by
    rw [Nat.card_eq_fintype_card,ZMod.card_units_eq_totient,
      Nat.totient_prime_pow (Fact.out : p.Prime) hk]
  have h := card_orderUnitNorm_ker_pow_mul_scalarUnits p k hk hk2 D
  rwa [hc] at h


/-- Explicit coefficient pairs whose norm is a unit in the finite scalar ring. -/
def normUnitResiduePairs (n : ℕ) [NeZero n] (D : ℤ) : Finset (ZMod n × ZMod n) :=
  Finset.univ.filter fun z =>
    ((QuadraticAlgebra.mk z.1 z.2 : DiscriminantAlgebra (ZMod n) D).norm).val.Coprime n

/-- Actual finite order units correspond to pairs with coprime norm residue. -/
def orderUnitsEquivNormUnitPairs (n : ℕ) [NeZero n] (D : ℤ) :
    (DiscriminantAlgebra (ZMod n) D)ˣ ≃
      {z : ZMod n × ZMod n //
        ((QuadraticAlgebra.mk z.1 z.2 : DiscriminantAlgebra (ZMod n) D).norm).val.Coprime n} :=
  Equiv.ofBijective (fun u => ⟨(u.val.re,u.val.im),by
    change u.val.norm.val.Coprime n
    apply (ZMod.isUnit_iff_coprime _ _).mp
    simpa only [ZMod.natCast_zmod_val] using (u.isUnit.map QuadraticAlgebra.norm)⟩) (by
    constructor
    · intro u v h
      apply Units.ext
      apply QuadraticAlgebra.ext
      · exact congrArg (fun z => z.val.1) h
      · exact congrArg (fun z => z.val.2) h
    · rintro ⟨q,hq⟩
      let z : DiscriminantAlgebra (ZMod n) D := ⟨q.1,q.2⟩
      have hn : IsUnit z.norm := by
        have h := (ZMod.isUnit_iff_coprime z.norm.val n).mpr hq
        simpa only [ZMod.natCast_zmod_val] using h
      have hu : IsUnit z := QuadraticAlgebra.isUnit_iff_norm_isUnit.mpr hn
      refine ⟨hu.unit,Subtype.ext ?_⟩
      exact congrArg (fun z : DiscriminantAlgebra (ZMod n) D => (z.re,z.im)) hu.unit_spec)

/-- Exact finite-order unit numerator, with a computable coefficient predicate. -/
theorem card_orderUnits_eq_normUnitResiduePairs (n : ℕ) [NeZero n] (D : ℤ) :
    Nat.card (DiscriminantAlgebra (ZMod n) D)ˣ=(normUnitResiduePairs n D).card := by
  rw [Nat.card_congr (orderUnitsEquivNormUnitPairs n D)]
  simp only [Nat.card_eq_fintype_card,Fintype.card_subtype,normUnitResiduePairs]

end BinaryNormIdeal

#assert_standard_axioms BinaryNormIdeal.discriminantAlgebraUnitsMap
#assert_standard_axioms BinaryNormIdeal.discriminantAlgebraUnitsMap_surjective
#assert_standard_axioms BinaryNormIdeal.discriminantAlgebraUnitsMap_norm
#assert_standard_axioms BinaryNormIdeal.toZModPow_surjective
#assert_standard_axioms BinaryNormIdeal.isUnit_of_toZModPow_isUnit
#assert_standard_axioms BinaryNormIdeal.scalarPowResidueUnits
#assert_standard_axioms BinaryNormIdeal.scalarPowResidueUnits_surjective
#assert_standard_axioms BinaryNormIdeal.orderPowResidueUnits_surjective
#assert_standard_axioms BinaryNormIdeal.isSquare_of_scalarPowResidueUnits_eq_one
#assert_standard_axioms BinaryNormIdeal.scalarPowResidueUnits_ker_le
#assert_standard_axioms BinaryNormIdeal.orderUnitNormSubgroup_map_pow
#assert_standard_axioms BinaryNormIdeal.orderUnitNormQuotientEquivPow
#assert_standard_axioms BinaryNormIdeal.card_orderUnitNormQuotient_eq_pow

#assert_standard_axioms BinaryNormIdeal.card_orderUnitNorm_ker_mul_scalarUnits
#assert_standard_axioms BinaryNormIdeal.card_orderUnitNorm_ker_pow_mul_scalarUnits
#assert_standard_axioms BinaryNormIdeal.orderUnitNormKernelEquivNormOne
#assert_standard_axioms BinaryNormIdeal.normOneResiduePairs
#assert_standard_axioms BinaryNormIdeal.normOneElementsEquivPairs
#assert_standard_axioms BinaryNormIdeal.card_orderUnitNorm_ker_eq_normOneResiduePairs

#assert_standard_axioms BinaryNormIdeal.finite_discriminantAlgebra_residue
#assert_standard_axioms BinaryNormIdeal.card_orderUnitNorm_ker_residue_pos
#assert_standard_axioms BinaryNormIdeal.card_orderUnitNorm_ker_pow_mul_primeUnits

#assert_standard_axioms BinaryNormIdeal.normUnitResiduePairs
#assert_standard_axioms BinaryNormIdeal.orderUnitsEquivNormUnitPairs
#assert_standard_axioms BinaryNormIdeal.card_orderUnits_eq_normUnitResiduePairs
