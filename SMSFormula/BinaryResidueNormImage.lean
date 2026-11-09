import SMSFormula.BinaryLocalNormQuotient

/-!
# The actual finite quadratic-order norm image

Coefficient reduction lifts every finite order unit to an actual p-adic
order unit. Thus the finite residue image in BinaryLocalNormQuotient is
exactly the norm image of all units of the finite discriminant algebra.
-/

noncomputable section

namespace BinaryNormIdeal

/-- Base change on the two original discriminant-order coefficients. -/
def discriminantAlgebraMap {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (D : ℤ) : DiscriminantAlgebra R D →+* DiscriminantAlgebra S D where
  toFun z := ⟨f z.re,f z.im⟩
  map_zero' := by ext <;> simp
  map_one' := by ext <;> simp [QuadraticAlgebra.re_one,QuadraticAlgebra.im_one]
  map_add' x y := by ext <;> simp
  map_mul' x y := by
    ext <;> simp [DiscriminantAlgebra,CoefficientAlgebra,map_add,map_mul,map_neg]

/-- The coefficient map preserves the literal quadratic norm. -/
theorem discriminantAlgebraMap_norm {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (D : ℤ) (z : DiscriminantAlgebra R D) :
    f z.norm=(discriminantAlgebraMap f D z).norm := by
  simp [QuadraticAlgebra.norm_def,discriminantAlgebraMap,
    DiscriminantAlgebra,CoefficientAlgebra,map_add,map_mul]

/-- Scalar coefficient reduction is onto, including nonunits. -/
theorem normResidueHom_surjective (p : ℕ) [Fact p.Prime] :
    Function.Surjective (normResidueHom p) := by
  intro z
  refine ⟨(z.val : ℤ_[p]),?_⟩
  simpa only [map_natCast] using ZMod.natCast_zmod_val z

/-- A unit after the chosen scalar reduction was already a p-adic unit. -/
theorem isUnit_of_normResidueHom_isUnit (p : ℕ) [Fact p.Prime] (x : ℤ_[p])
    (hx : IsUnit (normResidueHom p x)) : IsUnit x := by
  by_contra hn
  have hd : (p : ℤ_[p]) ∣ x := by
    rw [← Ideal.mem_span_singleton,← PadicInt.maximalIdeal_eq_span_p]
    exact (IsLocalRing.mem_maximalIdeal x).mpr hn
  obtain ⟨y,rfl⟩ := hd
  have hu : IsUnit (p : ZMod (normResidueModulus p)) :=
    isUnit_of_mul_isUnit_left (by simpa only [map_mul,map_natCast] using hx)
  have hc := (ZMod.isUnit_iff_coprime p (normResidueModulus p)).mp hu
  have hpm : p ∣ normResidueModulus p := by
    by_cases hp : p=2 <;> simp [normResidueModulus,hp]
  have h := Nat.dvd_gcd (dvd_refl p) hpm
  rw [hc.gcd_eq_one] at h
  exact (Fact.out : p.Prime).ne_one (Nat.dvd_one.mp h)

/-- Literal coefficient reduction of the original local order. -/
def orderNormResidueHom (p : ℕ) [Fact p.Prime] (D : ℤ) :
    DiscriminantAlgebra ℤ_[p] D →+* DiscriminantAlgebra (ZMod (normResidueModulus p)) D :=
  discriminantAlgebraMap (normResidueHom p) D

theorem orderNormResidueHom_surjective (p : ℕ) [Fact p.Prime] (D : ℤ) :
    Function.Surjective (orderNormResidueHom p D) := by
  intro z
  obtain ⟨x,hx⟩ := normResidueHom_surjective p z.re
  obtain ⟨y,hy⟩ := normResidueHom_surjective p z.im
  refine ⟨⟨x,y⟩,?_⟩
  exact QuadraticAlgebra.ext hx hy

/-- Reduction on actual order units. -/
def orderNormResidueUnits (p : ℕ) [Fact p.Prime] (D : ℤ) :
    (DiscriminantAlgebra ℤ_[p] D)ˣ →*
      (DiscriminantAlgebra (ZMod (normResidueModulus p)) D)ˣ :=
  Units.map (orderNormResidueHom p D).toMonoidHom

/-- Every finite order unit has an actual integral order-unit lift. -/
theorem orderNormResidueUnits_surjective (p : ℕ) [Fact p.Prime] (D : ℤ) :
    Function.Surjective (orderNormResidueUnits p D) := by
  intro u
  obtain ⟨z,hz⟩ := orderNormResidueHom_surjective p D u.val
  have hn : IsUnit (normResidueHom p z.norm) := by
    rw [discriminantAlgebraMap_norm]
    change IsUnit (orderNormResidueHom p D z).norm
    rw [hz]
    exact QuadraticAlgebra.isUnit_iff_norm_isUnit.mp u.isUnit
  have hu : IsUnit z := QuadraticAlgebra.isUnit_iff_norm_isUnit.mpr
    (isUnit_of_normResidueHom_isUnit p z.norm hn)
  refine ⟨hu.unit,?_⟩
  apply Units.ext
  change orderNormResidueHom p D (hu.unit : DiscriminantAlgebra ℤ_[p] D)=u.val
  rw [hu.unit_spec,hz]

/-- Norm and residue reduction commute on their actual unit carriers. -/
theorem normResidueUnits_orderUnitNorm (p : ℕ) [Fact p.Prime] (D : ℤ)
    (z : (DiscriminantAlgebra ℤ_[p] D)ˣ) :
    normResidueUnits p (orderUnitNorm ℤ_[p] D z)=
      orderUnitNorm (ZMod (normResidueModulus p)) D (orderNormResidueUnits p D z) := by
  apply Units.ext
  exact discriminantAlgebraMap_norm (normResidueHom p) D z.val

/-- The finite image is exactly norms of all finite quadratic-algebra units. -/
theorem residueOrderUnitNormSubgroup_eq_finiteNormImage (p : ℕ) [Fact p.Prime] (D : ℤ) :
    residueOrderUnitNormSubgroup p D=
      orderUnitNormSubgroup (ZMod (normResidueModulus p)) D := by
  ext u
  constructor
  · rintro ⟨v,⟨z,rfl⟩,rfl⟩
    exact ⟨orderNormResidueUnits p D z,(normResidueUnits_orderUnitNorm p D z).symm⟩
  · rintro ⟨z,rfl⟩
    obtain ⟨w,rfl⟩ := orderNormResidueUnits_surjective p D z
    exact ⟨orderUnitNorm ℤ_[p] D w,⟨w,rfl⟩,normResidueUnits_orderUnitNorm p D w⟩

/-- Exact finite quadratic-algebra model for the original local norm quotient. -/
def orderUnitNormQuotientEquivFiniteNorm (p : ℕ) [Fact p.Prime] (D : ℤ) :
    OrderUnitNormQuotient ℤ_[p] D ≃*
      OrderUnitNormQuotient (ZMod (normResidueModulus p)) D := by
  have h := orderUnitNormQuotientEquivResidue p D
  rw [residueOrderUnitNormSubgroup_eq_finiteNormImage] at h
  exact h

theorem card_orderUnitNormQuotient_eq_finiteNorm (p : ℕ) [Fact p.Prime] (D : ℤ) :
    Nat.card (OrderUnitNormQuotient ℤ_[p] D)=
      Nat.card (OrderUnitNormQuotient (ZMod (normResidueModulus p)) D) :=
  Nat.card_congr (orderUnitNormQuotientEquivFiniteNorm p D).toEquiv


/-- At an odd prime away from D, every finite scalar unit is an actual
finite discriminant-algebra unit norm. -/
theorem orderUnitNorm_finite_surjective_of_odd_not_dvd (p : ℕ) [Fact p.Prime]
    (D : ℤ) (hD : D%4=0 ∨ D%4=1) (hp : p≠2) (hpD : ¬ (p : ℤ) ∣ D) :
    Function.Surjective (orderUnitNorm (ZMod p) D) := by
  intro u
  have hchar : ringChar (ZMod p)≠2 := by simpa only [ZMod.ringChar_zmod_n] using hp
  have hd : (D : ZMod p)≠0 := by
    intro h
    exact hpD ((ZMod.intCast_zmod_eq_zero_iff_dvd D p).mp h)
  have hn : PositiveDefiniteIntegralLattice.quadraticNormRepresents (D : ZMod p) (u : ZMod p) := by
    by_cases hs : IsSquare (D : ZMod p)
    · exact PositiveDefiniteIntegralLattice.quadraticNormRepresents_of_isSquare _ _ hchar hd hs
    · exact PositiveDefiniteIntegralLattice.quadraticNormRepresents_finiteField_of_not_isSquare _ _ hs
  obtain ⟨x,y,hxy⟩ := (PositiveDefiniteIntegralLattice.quadraticNormRepresents_iff_exists _ _).mp hn
  let r : ZMod p := ((D%2 : ℤ) : ZMod p)
  let c : ZMod p := ((((D%2)^2-D)/4 : ℤ) : ZMod p)
  have hdisc : r*r-4*c=(D : ZMod p) := by
    dsimp only [r,c]
    have h := congrArg (fun z : ℤ => (z : ZMod p)) (discriminantOrder_coefficients D hD)
    push_cast at h
    simpa only [pow_two,mul_one] using h
  let z : DiscriminantAlgebra (ZMod p) D := ⟨x-r*y,2*y⟩
  have hz : z.norm=(u : ZMod p) := by
    calc
      z.norm=x*x-(r*r-4*c)*y*y := by
        simp only [QuadraticAlgebra.norm_def]
        dsimp only [z,DiscriminantAlgebra,CoefficientAlgebra,r,c]
        push_cast
        ring
      _=x*x-(D : ZMod p)*y*y := by rw [hdisc]
      _=(u : ZMod p) := hxy
  have hu : IsUnit z := QuadraticAlgebra.isUnit_iff_norm_isUnit.mpr (hz ▸ u.isUnit)
  refine ⟨hu.unit,?_⟩
  apply Units.ext
  change (hu.unit : DiscriminantAlgebra (ZMod p) D).norm=(u : ZMod p)
  rw [hu.unit_spec,hz]

/-- The finite residue norm subgroup is full at odd primes away from D. -/
theorem orderUnitNormSubgroup_finite_eq_top_of_odd_not_dvd (p : ℕ) [Fact p.Prime]
    (D : ℤ) (hD : D%4=0 ∨ D%4=1) (hp : p≠2) (hpD : ¬ (p : ℤ) ∣ D) :
    orderUnitNormSubgroup (ZMod p) D=⊤ :=
  MonoidHom.range_eq_top.mpr (orderUnitNorm_finite_surjective_of_odd_not_dvd p D hD hp hpD)

/-- The original local norm quotient is trivial at every odd prime away
from D, including primes bad only because of the original content. -/
theorem card_orderUnitNormQuotient_eq_one_of_odd_not_dvd (p : ℕ) [Fact p.Prime]
    (D : ℤ) (hD : D%4=0 ∨ D%4=1) (hp : p≠2) (hpD : ¬ (p : ℤ) ∣ D) :
    Nat.card (OrderUnitNormQuotient ℤ_[p] D)=1 := by
  rw [card_orderUnitNormQuotient_eq_finiteNorm]
  have hm : normResidueModulus p=p := if_neg hp
  rw [hm]
  unfold OrderUnitNormQuotient
  rw [orderUnitNormSubgroup_finite_eq_top_of_odd_not_dvd p D hD hp hpD]
  letI : Subsingleton ((ZMod p)ˣ ⧸ (⊤ : Subgroup (ZMod p)ˣ)) :=
    QuotientGroup.subsingleton_quotient_top
  exact Nat.card_unique


/-- The literal eight-residue norm with odd trace represents every unit.
This is a closed finite proof, not a native_decide trust extension. -/
theorem exists_norm_eight_trace_one (c : ZMod 8) (u : (ZMod 8)ˣ) :
    ∃ x y : ZMod 8, x*x+x*y+c*y*y=(u : ZMod 8) := by
  have h : ∀ (c : ZMod 8) (u : (ZMod 8)ˣ),
      ∃ x y : ZMod 8, x*x+x*y+c*y*y=(u : ZMod 8) := by decide
  exact h c u

/-- At two with odd discriminant, finite order-unit norm reduction is onto. -/
theorem orderUnitNorm_eight_surjective_of_odd (D : ℤ) (hD : D%2=1) :
    Function.Surjective (orderUnitNorm (ZMod 8) D) := by
  intro u
  obtain ⟨x,y,hxy⟩ := exists_norm_eight_trace_one
    (((D%2)^2-D)/4 : ℤ) u
  let z : DiscriminantAlgebra (ZMod 8) D := ⟨x,y⟩
  have hz : z.norm=(u : ZMod 8) := by
    simpa [QuadraticAlgebra.norm_def,z,DiscriminantAlgebra,CoefficientAlgebra,hD] using hxy
  have hu : IsUnit z := QuadraticAlgebra.isUnit_iff_norm_isUnit.mpr (hz ▸ u.isUnit)
  refine ⟨hu.unit,?_⟩
  apply Units.ext
  change (hu.unit : DiscriminantAlgebra (ZMod 8) D).norm=(u : ZMod 8)
  rw [hu.unit_spec,hz]

/-- The dyadic quotient for an odd original discriminant has one class. -/
theorem card_orderUnitNormQuotient_two_eq_one_of_odd (D : ℤ) (hD : D%2=1) :
    Nat.card (OrderUnitNormQuotient ℤ_[2] D)=1 := by
  rw [card_orderUnitNormQuotient_eq_finiteNorm]
  have hn : orderUnitNormSubgroup (ZMod 8) D=⊤ :=
    MonoidHom.range_eq_top.mpr (orderUnitNorm_eight_surjective_of_odd D hD)
  change Nat.card ((ZMod 8)ˣ ⧸ orderUnitNormSubgroup (ZMod 8) D)=1
  rw [hn]
  letI : Subsingleton ((ZMod 8)ˣ ⧸ (⊤ : Subgroup (ZMod 8)ˣ)) :=
    QuotientGroup.subsingleton_quotient_top
  exact Nat.card_unique

/-- Support of the actual norm-index correction is contained in D.
The result includes the dyadic prime and arbitrary original content. -/
theorem card_orderUnitNormQuotient_eq_one_of_not_dvd (p : ℕ) [Fact p.Prime]
    (D : ℤ) (hD : D%4=0 ∨ D%4=1) (hpD : ¬ (p : ℤ) ∣ D) :
    Nat.card (OrderUnitNormQuotient ℤ_[p] D)=1 := by
  by_cases hp : p=2
  · subst p
    have hodd : D%2=1 := by
      have hn : D%2≠0 := fun h => hpD (Int.dvd_of_emod_eq_zero h)
      omega
    exact card_orderUnitNormQuotient_two_eq_one_of_odd D hodd
  · exact card_orderUnitNormQuotient_eq_one_of_odd_not_dvd p D hD hp hpD

end BinaryNormIdeal

#assert_standard_axioms BinaryNormIdeal.discriminantAlgebraMap
#assert_standard_axioms BinaryNormIdeal.discriminantAlgebraMap_norm
#assert_standard_axioms BinaryNormIdeal.normResidueHom_surjective
#assert_standard_axioms BinaryNormIdeal.isUnit_of_normResidueHom_isUnit
#assert_standard_axioms BinaryNormIdeal.orderNormResidueHom
#assert_standard_axioms BinaryNormIdeal.orderNormResidueHom_surjective
#assert_standard_axioms BinaryNormIdeal.orderNormResidueUnits
#assert_standard_axioms BinaryNormIdeal.orderNormResidueUnits_surjective
#assert_standard_axioms BinaryNormIdeal.normResidueUnits_orderUnitNorm
#assert_standard_axioms BinaryNormIdeal.residueOrderUnitNormSubgroup_eq_finiteNormImage
#assert_standard_axioms BinaryNormIdeal.orderUnitNormQuotientEquivFiniteNorm
#assert_standard_axioms BinaryNormIdeal.card_orderUnitNormQuotient_eq_finiteNorm

#assert_standard_axioms BinaryNormIdeal.orderUnitNorm_finite_surjective_of_odd_not_dvd
#assert_standard_axioms BinaryNormIdeal.orderUnitNormSubgroup_finite_eq_top_of_odd_not_dvd
#assert_standard_axioms BinaryNormIdeal.card_orderUnitNormQuotient_eq_one_of_odd_not_dvd

#assert_standard_axioms BinaryNormIdeal.exists_norm_eight_trace_one
#assert_standard_axioms BinaryNormIdeal.orderUnitNorm_eight_surjective_of_odd
#assert_standard_axioms BinaryNormIdeal.card_orderUnitNormQuotient_two_eq_one_of_odd
#assert_standard_axioms BinaryNormIdeal.card_orderUnitNormQuotient_eq_one_of_not_dvd
