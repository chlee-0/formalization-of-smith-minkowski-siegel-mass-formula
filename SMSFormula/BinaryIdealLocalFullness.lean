import SMSFormula.BinaryIdealLocalDetection

/-!
# Local fullness of arbitrary integral quadratic-order ideals

Integral coefficient residues lift modulo p. Full local span therefore
gives P+(p)=O without an inverse of P. A positive integer in P then gives
P=O by prime units in the quotient. This supplies the noncircular inverse
criterion needed by the actual binary ideal patch construction.
-/

namespace BinaryNormIdeal

open scoped QuadraticAlgebra nonZeroDivisors

/-- Both integral local coefficients have one original-order lift modulo p. -/
theorem exists_order_residue_mod_prime (a b c : ℤ) (p : ℕ) [Fact (Nat.Prime p)]
    (z : CoefficientAlgebra (a : ℤ_[p]) (b : ℤ_[p]) (c : ℤ_[p])) :
    ∃ w : CoefficientOrder a b c,
      z-orderScalarMap a b c ℤ_[p] w ∈
        Ideal.span {(p : CoefficientAlgebra (a : ℤ_[p]) (b : ℤ_[p]) (c : ℤ_[p]))} := by
  obtain ⟨r,hr⟩ := Ideal.mem_span_singleton.mp (by simpa using PadicInt.appr_spec 1 z.re)
  obtain ⟨s,hs⟩ := Ideal.mem_span_singleton.mp (by simpa using PadicInt.appr_spec 1 z.im)
  refine ⟨⟨(z.re.appr 1 : ℤ),(z.im.appr 1 : ℤ)⟩,?_⟩
  apply Ideal.mem_span_singleton.mpr
  refine ⟨⟨r,s⟩,?_⟩
  apply QuadraticAlgebra.ext <;> simp [orderScalarMap,coefficientScalarMap] at *
  · exact hr
  · exact hs

/-- Local divisibility of an original order element by p is the actual
integer coefficient divisibility. The prime2 is included. -/
theorem order_mem_prime_of_scalarMap_mem_prime (a b c : ℤ)
    (p : ℕ) [Fact (Nat.Prime p)] (w : CoefficientOrder a b c)
    (h : orderScalarMap a b c ℤ_[p] w ∈
      Ideal.span {(p : CoefficientAlgebra (a : ℤ_[p]) (b : ℤ_[p]) (c : ℤ_[p]))}) :
    w ∈ Ideal.span {(p : CoefficientOrder a b c)} := by
  obtain ⟨z,hz⟩ := Ideal.mem_span_singleton.mp h
  have hr : (p : ℤ_[p]) ∣ (w.re : ℤ_[p]) := by
    refine ⟨z.re,?_⟩
    simpa [orderScalarMap,coefficientScalarMap] using congrArg QuadraticAlgebra.re hz
  have hi : (p : ℤ_[p]) ∣ (w.im : ℤ_[p]) := by
    refine ⟨z.im,?_⟩
    simpa [orderScalarMap,coefficientScalarMap] using congrArg QuadraticAlgebra.im hz
  have hdr : (p : ℤ) ∣ w.re := by simpa using (PadicInt.pow_p_dvd_int_iff 1 w.re).mp (by simpa using hr)
  have hdi : (p : ℤ) ∣ w.im := by simpa using (PadicInt.pow_p_dvd_int_iff 1 w.im).mp (by simpa using hi)
  obtain ⟨r,hr⟩ := hdr
  obtain ⟨s,hs⟩ := hdi
  apply Ideal.mem_span_singleton.mpr
  refine ⟨⟨r,s⟩,?_⟩
  apply QuadraticAlgebra.ext <;> simp [hr,hs]

/-- Every element of the extended integral ideal has a residue lifted from
that same original ideal. No invertibility or finite generation is used. -/
theorem exists_ideal_residue_mod_prime (a b c : ℤ)
    (P : Ideal (CoefficientOrder a b c)) (p : ℕ) [Fact (Nat.Prime p)]
    (z : CoefficientAlgebra (a : ℤ_[p]) (b : ℤ_[p]) (c : ℤ_[p]))
    (hz : z ∈ Ideal.map (orderScalarMap a b c ℤ_[p]) P) :
    ∃ w ∈ P, z-orderScalarMap a b c ℤ_[p] w ∈
      Ideal.span {(p : CoefficientAlgebra (a : ℤ_[p]) (b : ℤ_[p]) (c : ℤ_[p]))} := by
  let f := orderScalarMap a b c ℤ_[p]
  let Q : Ideal (CoefficientAlgebra (a : ℤ_[p]) (b : ℤ_[p]) (c : ℤ_[p])) := Ideal.span {(p : CoefficientAlgebra (a : ℤ_[p]) (b : ℤ_[p]) (c : ℤ_[p]))}
  change z ∈ Ideal.span (f '' (P : Set (CoefficientOrder a b c))) at hz
  change ∃ w ∈ P, z-f w ∈ Q
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w,hw,rfl⟩ := hx
    exact ⟨w,hw,by simp⟩
  | zero => exact ⟨0,P.zero_mem,by simp⟩
  | add x y hx hy ihx ihy =>
    obtain ⟨v,hv,hxv⟩ := ihx
    obtain ⟨w,hw,hyw⟩ := ihy
    refine ⟨v+w,P.add_mem hv hw,?_⟩
    convert Q.add_mem hxv hyw using 1
    simp [map_add]
    ring
  | smul r x hx ih =>
    obtain ⟨w,hw,hxw⟩ := ih
    obtain ⟨s,hs⟩ := exists_order_residue_mod_prime a b c p r
    refine ⟨s*w,P.mul_mem_left _ hw,?_⟩
    have hh := Q.add_mem (Q.mul_mem_right x hs) (Q.mul_mem_left (f s) hxw)
    convert hh using 1
    simp [map_mul]
    ring

/-- Full actual local integral ideal gives P+(p)=O for an arbitrary P.
It does not assume the invertibility it will later help to prove. -/
theorem ideal_sup_prime_eq_top_of_map_eq_top (a b c : ℤ)
    (P : Ideal (CoefficientOrder a b c)) (p : ℕ) [Fact (Nat.Prime p)]
    (hP : Ideal.map (orderScalarMap a b c ℤ_[p]) P=⊤) :
    P ⊔ Ideal.span {(p : CoefficientOrder a b c)}=⊤ := by
  have h1 : (1 : CoefficientAlgebra (a : ℤ_[p]) (b : ℤ_[p]) (c : ℤ_[p])) ∈
      Ideal.map (orderScalarMap a b c ℤ_[p]) P := by rw [hP]; trivial
  obtain ⟨w,hw,hr⟩ := exists_ideal_residue_mod_prime a b c P p 1 h1
  have hr' : 1-w ∈ Ideal.span {(p : CoefficientOrder a b c)} := by
    apply order_mem_prime_of_scalarMap_mem_prime a b c p
    simpa only [map_sub,map_one] using hr
  apply (Ideal.eq_top_iff_one _).mpr
  apply Submodule.mem_sup.mpr
  exact ⟨w,hw,1-w,hr',by ring⟩

end BinaryNormIdeal

namespace Ideal

/-- An arbitrary ideal containing a positive integer is the unit ideal if
it is comaximal with each prime divisor of that integer. Quotient cardinality
and an existing inverse are unnecessary. -/
theorem eq_top_of_pos_nat_mem_and_prime_sup {R : Type*} [CommRing R]
    (P : Ideal R) (d : ℕ) (hd : 0<d) (hdP : (d : R) ∈ P)
    (hprime : ∀ p : ℕ, p.Prime → p ∣ d → P ⊔ Ideal.span {(p : R)}=⊤) : P=⊤ := by
  have hunit (p : ℕ) (hp : p.Prime) (hpd : p ∣ d) : IsUnit (p : R ⧸ P) := by
    have h1 : (1 : R) ∈ P ⊔ Ideal.span {(p : R)} := by rw [hprime p hp hpd]; trivial
    obtain ⟨x,hx,y,hy,hxy⟩ := Submodule.mem_sup.mp h1
    obtain ⟨z,hz⟩ := Ideal.mem_span_singleton.mp hy
    have h := congrArg (Ideal.Quotient.mk P) hxy
    rw [map_add,Ideal.Quotient.eq_zero_iff_mem.mpr hx,zero_add,hz,map_mul,map_natCast,map_one] at h
    exact (Units.mkOfMulEqOne _ _ h).isUnit
  have hl (l : List ℕ) (hu : ∀ p ∈ l, IsUnit (p : R ⧸ P)) : IsUnit ((l.prod : ℕ) : R ⧸ P) := by
    induction l with
    | nil => simp
    | cons p l ih =>
      simpa only [List.prod_cons,Nat.cast_mul] using
        (hu p List.mem_cons_self).mul (ih (fun q hq => hu q (List.mem_cons_of_mem p hq)))
  have hdunit : IsUnit (d : R ⧸ P) := by
    have hh := hl d.primeFactorsList (fun p hp => hunit p
      (Nat.prime_of_mem_primeFactorsList hp) (Nat.dvd_of_mem_primeFactorsList hp))
    simpa only [Nat.prod_primeFactorsList (ne_of_gt hd)] using hh
  have hzero : (d : R ⧸ P)=0 := by
    simpa only [map_natCast] using (Ideal.Quotient.eq_zero_iff_mem.mpr hdP)
  obtain ⟨u,hu⟩ := hdunit
  have h10 : (1 : R ⧸ P)=0 := by
    calc
      1=u.val*u.inv := u.val_inv.symm
      _=0 := by rw [hu,hzero,zero_mul]
  apply (Ideal.eq_top_iff_one _).mpr
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  simpa only [map_one] using h10

end Ideal

namespace Submodule

/-- The span of an integral ideal's image under a scalar algebra map is
its actual image as a submodule. This does not require injectivity. -/
theorem mem_span_image_ideal_iff {R A : Type*} [CommRing R] [CommRing A]
    [Algebra R A] (P : Ideal R) (x : A) :
    x ∈ Submodule.span R ((algebraMap R A) '' (P : Set R)) ↔
      ∃ z ∈ P, algebraMap R A z=x := by
  change x ∈ Submodule.span R ((Algebra.linearMap R A) '' (P : Set R)) ↔ _
  rw [← Submodule.map_span,Submodule.span_eq]
  exact Submodule.mem_map

end Submodule

namespace PositiveDefiniteIntegralLattice

open BinaryNormIdeal
open scoped nonZeroDivisors

/-- Full actual local span of an integral ideal implies its integral
local ideal is top. Injectivity of the local-order embedding suffices. -/
theorem binaryIntegralIdeal_map_eq_top_of_extension_one (K : PositiveDefiniteIntegralLattice 2)
    (P : Ideal (DiscriminantOrder K.binaryPrimitiveDiscriminant))
    (p : ℕ) [Fact (Nat.Prime p)]
    (hP : letI := K.binaryDiscriminantOrder_isDomain
      letI := padicOrderAlgebra p K.binaryPrimitiveDiscriminant
      K.binaryPadicIdealExtension p (P : K.BinaryDiscriminantFractionalIdeals)=1) :
    Ideal.map (orderScalarMap 1 (K.binaryPrimitiveDiscriminant%2)
      (((K.binaryPrimitiveDiscriminant%2)^2-K.binaryPrimitiveDiscriminant)/4) ℤ_[p]) P=⊤ := by
  letI := K.binaryDiscriminantOrder_isDomain
  letI := padicOrderAlgebra p K.binaryPrimitiveDiscriminant
  let Q := Ideal.map (orderScalarMap 1 (K.binaryPrimitiveDiscriminant%2)
    (((K.binaryPrimitiveDiscriminant%2)^2-K.binaryPrimitiveDiscriminant)/4) ℤ_[p]) P
  have h1 : (1 : DiscriminantAlgebra ℚ_[p] K.binaryPrimitiveDiscriminant) ∈
      K.binaryPadicIdealExtension p (P : K.BinaryDiscriminantFractionalIdeals) := by
    rw [hP]
    exact Submodule.mem_one.mpr ⟨1,map_one _⟩
  change (1 : DiscriminantAlgebra ℚ_[p] K.binaryPrimitiveDiscriminant) ∈
    FractionalIdeal.scalarSpanExtension _ _ _ (P : K.BinaryDiscriminantFractionalIdeals) at h1
  rw [FractionalIdeal.scalarSpanExtension_coeIdeal] at h1
  obtain ⟨z,hz,hz1⟩ := (Submodule.mem_span_image_ideal_iff Q
    (1 : DiscriminantAlgebra ℚ_[p] K.binaryPrimitiveDiscriminant)).mp h1
  have he : z=1 := (padicOrderMap_injective p _)
    (by simpa only [map_one] using hz1)
  apply (Ideal.eq_top_iff_one _).mpr
  exact he ▸ hz

/-- A positive integer and local fullness at its prime divisors force an
Arbitrary actual integral ideal to be the unit ideal. -/
theorem binaryIntegralIdeal_eq_top_of_pos_nat_mem_and_local_fullness
    (K : PositiveDefiniteIntegralLattice 2) (P : Ideal (DiscriminantOrder K.binaryPrimitiveDiscriminant))
    (d : ℕ) (hd : 0<d) (hdP : (d : DiscriminantOrder K.binaryPrimitiveDiscriminant) ∈ P)
    (hP : letI := K.binaryDiscriminantOrder_isDomain
      ∀ (p : ℕ) [Fact (Nat.Prime p)], p ∣ d →
        letI := padicOrderAlgebra p K.binaryPrimitiveDiscriminant
        K.binaryPadicIdealExtension p (P : K.BinaryDiscriminantFractionalIdeals)=1) : P=⊤ := by
  letI := K.binaryDiscriminantOrder_isDomain
  apply P.eq_top_of_pos_nat_mem_and_prime_sup d hd hdP
  intro p hp hpd
  letI : Fact (Nat.Prime p) := ⟨hp⟩
  exact ideal_sup_prime_eq_top_of_map_eq_top _ _ _ P p
    (K.binaryIntegralIdeal_map_eq_top_of_extension_one P p (hP p hpd))

/-- An actual fractional ideal bounded below by a positive integer is one
if all its actual local extensions are one. It need not already be a unit. -/
theorem binaryFractionalIdeal_eq_one_of_pos_nat_mem_and_local_fullness
    (K : PositiveDefiniteIntegralLattice 2) (P : K.BinaryDiscriminantFractionalIdeals)
    (d : ℕ) (hd : 0<d)
    (hdP : (d : FractionRing (DiscriminantOrder K.binaryPrimitiveDiscriminant)) ∈ P)
    (hP : letI := K.binaryDiscriminantOrder_isDomain
      ∀ (p : ℕ) [Fact (Nat.Prime p)],
        letI := padicOrderAlgebra p K.binaryPrimitiveDiscriminant
        K.binaryPadicIdealExtension p P=1) : P=1 := by
  letI := K.binaryDiscriminantOrder_isDomain
  have hle : P ≤ (1 : K.BinaryDiscriminantFractionalIdeals) := by
    apply (K.binaryFractionalIdeal_le_unit_iff_padic P 1).mpr
    intro p hp
    letI := padicOrderAlgebra p K.binaryPrimitiveDiscriminant
    rw [hP p,Units.val_one,map_one]
  obtain ⟨I,hI⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.mp hle
  have hdI : (d : DiscriminantOrder K.binaryPrimitiveDiscriminant) ∈ I := by
    rw [← hI] at hdP
    obtain ⟨w,hw,he⟩ := (FractionalIdeal.mem_coeIdeal _).mp hdP
    have hdw : w=(d : DiscriminantOrder K.binaryPrimitiveDiscriminant) := by
      apply (IsFractionRing.injective (DiscriminantOrder K.binaryPrimitiveDiscriminant)
        (FractionRing (DiscriminantOrder K.binaryPrimitiveDiscriminant)))
      simpa only [map_natCast] using he
    exact hdw ▸ hw
  have htop : I=⊤ := K.binaryIntegralIdeal_eq_top_of_pos_nat_mem_and_local_fullness I d hd hdI
    (fun p _ _ => by rw [hI]; exact hP p)
  rw [← hI,htop]
  exact FractionalIdeal.coeIdeal_top _

/-- Two actual fractional ideals with reciprocal local products and a
positive integer in their global product give an actual product identity.
Neither ideal is assumed invertible. -/
theorem binaryFractionalIdeal_mul_eq_one_of_local_product (K : PositiveDefiniteIntegralLattice 2)
    (I J : K.BinaryDiscriminantFractionalIdeals) (d : ℕ) (hd : 0<d)
    (hdIJ : (d : FractionRing (DiscriminantOrder K.binaryPrimitiveDiscriminant)) ∈ I*J)
    (hlocal : letI := K.binaryDiscriminantOrder_isDomain
      ∀ (p : ℕ) [Fact (Nat.Prime p)],
        letI := padicOrderAlgebra p K.binaryPrimitiveDiscriminant
        K.binaryPadicIdealExtension p I*K.binaryPadicIdealExtension p J=1) : I*J=1 := by
  letI := K.binaryDiscriminantOrder_isDomain
  exact K.binaryFractionalIdeal_eq_one_of_pos_nat_mem_and_local_fullness (I*J) d hd hdIJ
    (fun p _ => by rw [map_mul]; exact hlocal p)

/-- Package the actual reciprocal local-product data as a fractional-ideal
unit with the displayed inverse, without a pre-existing inverse premise. -/
theorem exists_binaryFractionalIdeal_unit_of_local_product (K : PositiveDefiniteIntegralLattice 2)
    (I J : K.BinaryDiscriminantFractionalIdeals) (d : ℕ) (hd : 0<d)
    (hdIJ : (d : FractionRing (DiscriminantOrder K.binaryPrimitiveDiscriminant)) ∈ I*J)
    (hlocal : letI := K.binaryDiscriminantOrder_isDomain
      ∀ (p : ℕ) [Fact (Nat.Prime p)],
        letI := padicOrderAlgebra p K.binaryPrimitiveDiscriminant
        K.binaryPadicIdealExtension p I*K.binaryPadicIdealExtension p J=1) :
    ∃ u : K.BinaryDiscriminantFractionalIdealsˣ, u.val=I ∧ (u⁻¹).val=J := by
  have hmul := K.binaryFractionalIdeal_mul_eq_one_of_local_product I J d hd hdIJ hlocal
  exact ⟨⟨I,J,hmul,by rw [mul_comm,hmul]⟩,rfl,rfl⟩

end PositiveDefiniteIntegralLattice

#assert_standard_axioms BinaryNormIdeal.exists_order_residue_mod_prime
#assert_standard_axioms BinaryNormIdeal.order_mem_prime_of_scalarMap_mem_prime
#assert_standard_axioms BinaryNormIdeal.exists_ideal_residue_mod_prime
#assert_standard_axioms BinaryNormIdeal.ideal_sup_prime_eq_top_of_map_eq_top
#assert_standard_axioms Ideal.eq_top_of_pos_nat_mem_and_prime_sup
#assert_standard_axioms Submodule.mem_span_image_ideal_iff
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryIntegralIdeal_map_eq_top_of_extension_one
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryIntegralIdeal_eq_top_of_pos_nat_mem_and_local_fullness
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryFractionalIdeal_eq_one_of_pos_nat_mem_and_local_fullness
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryFractionalIdeal_mul_eq_one_of_local_product
#assert_standard_axioms PositiveDefiniteIntegralLattice.exists_binaryFractionalIdeal_unit_of_local_product
