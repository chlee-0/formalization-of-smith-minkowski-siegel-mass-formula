import SMSFormula.BinaryIdealPrimitivity

/-!
# Exact rational scales for binary ideal products

The actual fraction field carries the rational quadratic norm and order
conjugation. Positive rational scalars have rigid principal ideals. These
interfaces preserve the order at nonmaximal and dyadic discriminants.
-/

namespace BinaryNormIdeal

open scoped nonZeroDivisors QuadraticAlgebra

variable (a b c : ℤ) [IsDomain (CoefficientOrder a b c)]

/-- Embed the actual fraction field in the rational coefficient algebra.
The latter field structure is used locally, with its proved negative D. -/
noncomputable def fractionRationalMap (hD : b^2-4*a*c < 0) :
    FractionRing (CoefficientOrder a b c) →+*
      QuadraticAlgebra ℚ (-(a : ℚ)*(c : ℚ)) (b : ℚ) := by
  letI := rationalField a b c hD
  exact IsFractionRing.lift (K := FractionRing (CoefficientOrder a b c))
    (rationalMap_injective a b c)

lemma fractionRationalMap_algebraMap (hD : b^2-4*a*c < 0) (z : CoefficientOrder a b c) :
    fractionRationalMap a b c hD (algebraMap _ (FractionRing (CoefficientOrder a b c)) z)=
      rationalMap a b c z := by
  letI := rationalField a b c hD
  unfold fractionRationalMap
  exact IsFractionRing.lift_algebraMap _ z

/-- The field norm is rational, on the existing canonical FractionRing. -/
noncomputable def fractionNorm (hD : b^2-4*a*c < 0) :
    FractionRing (CoefficientOrder a b c) →* ℚ :=
  QuadraticAlgebra.norm.comp (fractionRationalMap a b c hD).toMonoidHom

lemma fractionNorm_algebraMap (hD : b^2-4*a*c < 0) (z : CoefficientOrder a b c) :
    fractionNorm a b c hD (algebraMap _ (FractionRing (CoefficientOrder a b c)) z)=(z.norm : ℚ) := by
  change (fractionRationalMap a b c hD (algebraMap _ _ z)).norm=_
  rw [fractionRationalMap_algebraMap]
  simp [rationalMap,QuadraticAlgebra.norm_def]

lemma fractionNorm_pos (hD : b^2-4*a*c < 0)
    (z : FractionRing (CoefficientOrder a b c)) (hz : z ≠ 0) : 0 < fractionNorm a b c hD z := by
  letI := rationalField a b c hD
  let w := fractionRationalMap a b c hD z
  have hw : w ≠ 0 := by simpa only [map_zero] using (fractionRationalMap a b c hD).injective.ne hz
  have hneg : (b : ℚ)^2-4*(a : ℚ)*(c : ℚ)<0 := by exact_mod_cast hD
  have hn : 4*w.norm=(2*w.re+(b : ℚ)*w.im)^2-
      ((b : ℚ)^2-4*(a : ℚ)*(c : ℚ))*w.im^2 := by
    rw [QuadraticAlgebra.norm_def]
    ring
  change 0 < w.norm
  by_cases hi : w.im=0
  · have hr : w.re ≠ 0 := by
      intro hr
      apply hw
      apply QuadraticAlgebra.ext <;> simp [hr,hi]
    rw [hi] at hn
    nlinarith [sq_pos_of_ne_zero hr]
  · nlinarith [sq_nonneg (2*w.re+(b : ℚ)*w.im),
      mul_neg_of_neg_of_pos hneg (sq_pos_of_ne_zero hi)]

/-- Conjugation on the actual canonical fraction field. -/
noncomputable def fractionConjugation :
    FractionRing (CoefficientOrder a b c) ≃+* FractionRing (CoefficientOrder a b c) :=
  IsFractionRing.ringEquivOfRingEquiv (starRingAut : CoefficientOrder a b c ≃+* CoefficientOrder a b c)

omit [IsDomain (CoefficientOrder a b c)] in
lemma fractionConjugation_algebraMap (z : CoefficientOrder a b c) :
    fractionConjugation a b c (algebraMap _ (FractionRing (CoefficientOrder a b c)) z)=
      algebraMap _ _ (star z) :=
  IsFractionRing.ringEquivOfRingEquiv_algebraMap
    (starRingAut : CoefficientOrder a b c ≃+* CoefficientOrder a b c) z

omit [IsDomain (CoefficientOrder a b c)] in
private lemma rationalMap_star (z : CoefficientOrder a b c) :
    rationalMap a b c (star z)=star (rationalMap a b c z) := by
  apply QuadraticAlgebra.ext <;> simp [rationalMap]

lemma fractionRationalMap_conjugation (hD : b^2-4*a*c < 0)
    (z : FractionRing (CoefficientOrder a b c)) :
    fractionRationalMap a b c hD (fractionConjugation a b c z)=
      star (fractionRationalMap a b c hD z) := by
  letI := rationalField a b c hD
  have hh : (fractionRationalMap a b c hD).comp (fractionConjugation a b c).toRingHom =
      (starRingAut : QuadraticAlgebra ℚ (-(a : ℚ)*(c : ℚ)) (b : ℚ) ≃+*
        QuadraticAlgebra ℚ (-(a : ℚ)*(c : ℚ)) (b : ℚ)).toRingHom.comp
        (fractionRationalMap a b c hD) := by
    apply IsFractionRing.ringHom_ext (A := CoefficientOrder a b c)
    intro r
    change fractionRationalMap a b c hD (fractionConjugation a b c (algebraMap _ _ r))=
      star (fractionRationalMap a b c hD (algebraMap _ _ r))
    rw [fractionConjugation_algebraMap,fractionRationalMap_algebraMap,fractionRationalMap_algebraMap]
    exact rationalMap_star a b c r
  exact DFunLike.congr_fun hh z

/-- The actual field product with its conjugate is the rational norm. -/
lemma fraction_mul_conjugation (hD : b^2-4*a*c < 0)
    (z : FractionRing (CoefficientOrder a b c)) :
    z*fractionConjugation a b c z=(fractionNorm a b c hD z : FractionRing (CoefficientOrder a b c)) := by
  letI := rationalField a b c hD
  apply (fractionRationalMap a b c hD).injective
  rw [map_mul,fractionRationalMap_conjugation,map_ratCast]
  exact (QuadraticAlgebra.algebraMap_norm_eq_mul_star (fractionRationalMap a b c hD z)).symm

/-- A rational scalar belongs to the actual order iff it is an integer. -/
theorem rat_mem_fractional_one_iff (hD : b^2-4*a*c < 0) (q : ℚ) :
    (q : FractionRing (CoefficientOrder a b c)) ∈
      (1 : FractionalIdeal (CoefficientOrder a b c)⁰ (FractionRing (CoefficientOrder a b c))) ↔
      ∃ n : ℤ, (n : ℚ)=q := by
  letI := rationalField a b c hD
  rw [FractionalIdeal.mem_one_iff]
  constructor
  · rintro ⟨z,hz⟩
    have h := congrArg (fractionRationalMap a b c hD) hz
    rw [fractionRationalMap_algebraMap,map_ratCast] at h
    refine ⟨z.re,?_⟩
    have hr := congrArg QuadraticAlgebra.re h
    simpa [rationalMap] using hr
  · rintro ⟨n,rfl⟩
    exact ⟨(n : CoefficientOrder a b c),by simp⟩

/-- The actual fraction field has characteristic zero, proved via its
rational coefficient embedding. No global inference rule is added. -/
theorem fractionField_charZero (hD : b^2-4*a*c < 0) :
    CharZero (FractionRing (CoefficientOrder a b c)) := by
  letI := rationalField a b c hD
  exact charZero_of_inj_zero (fun n hn => by
    have hh := congrArg (fractionRationalMap a b c hD) hn
    rw [map_natCast,map_zero] at hh
    have hr := congrArg QuadraticAlgebra.re hh
    have hz : (n : ℚ)=0 := by simpa using hr
    exact_mod_cast hz)

/-- Positive rational scalars cannot change the actual order as a lattice. -/
theorem rat_eq_one_of_spanSingleton_eq_one (hD : b^2-4*a*c < 0) (q : ℚ) (hq : 0<q)
    (h : FractionalIdeal.spanSingleton (CoefficientOrder a b c)⁰
      (q : FractionRing (CoefficientOrder a b c))=1) : q=1 := by
  letI := rationalField a b c hD
  letI := fractionField_charZero a b c hD
  have hqmem : (q : FractionRing (CoefficientOrder a b c)) ∈
      (1 : FractionalIdeal (CoefficientOrder a b c)⁰ (FractionRing (CoefficientOrder a b c))) := by
    rw [← h]
    exact FractionalIdeal.mem_spanSingleton_self _ _
  obtain ⟨m,hm⟩ := (rat_mem_fractional_one_iff a b c hD q).mp hqmem
  have hOne : (1 : FractionRing (CoefficientOrder a b c)) ∈
      FractionalIdeal.spanSingleton (CoefficientOrder a b c)⁰ (q : FractionRing (CoefficientOrder a b c)) := by
    rw [h]
    exact FractionalIdeal.one_mem_one (S := (CoefficientOrder a b c)⁰)
      (P := FractionRing (CoefficientOrder a b c))
  obtain ⟨z,hz⟩ := (FractionalIdeal.mem_spanSingleton _).mp hOne
  have hz' : algebraMap (CoefficientOrder a b c) (FractionRing (CoefficientOrder a b c)) z=
      ((q⁻¹ : ℚ) : FractionRing (CoefficientOrder a b c)) := by
    rw [Algebra.smul_def] at hz
    have hne : (q : FractionRing (CoefficientOrder a b c)) ≠ 0 := by exact_mod_cast (ne_of_gt hq)
    have hh := (mul_eq_one_iff_eq_inv₀ hne).mp hz
    simpa using hh
  obtain ⟨n,hn⟩ := (rat_mem_fractional_one_iff a b c hD (q⁻¹)).mp
    ((FractionalIdeal.mem_one_iff _).mpr ⟨z,hz'⟩)
  have hmn : m*n=1 := by
    have hh : (m : ℚ)*(n : ℚ)=1 := by rw [hm,hn]; exact mul_inv_cancel₀ (ne_of_gt hq)
    exact_mod_cast hh
  have hmpos : 0<m := by exact_mod_cast (hm ▸ hq)
  have hmunit : IsUnit m := isUnit_iff_dvd_one.mpr ⟨n,hmn.symm⟩
  have hm1 : m=1 := (Int.isUnit_iff.mp hmunit).resolve_right (by omega)
  simpa [hm1] using hm.symm

/-- Positive rational principal scales are equal if their actual
fractional ideals are equal. -/
theorem rat_eq_of_spanSingleton_eq (hD : b^2-4*a*c < 0) (r s : ℚ)
    (hr : 0<r) (hs : 0<s)
    (h : FractionalIdeal.spanSingleton (CoefficientOrder a b c)⁰
        (r : FractionRing (CoefficientOrder a b c))=
      FractionalIdeal.spanSingleton (CoefficientOrder a b c)⁰
        (s : FractionRing (CoefficientOrder a b c))) : r=s := by
  letI := fractionField_charZero a b c hD
  have hscale : FractionalIdeal.spanSingleton (CoefficientOrder a b c)⁰
      ((r/s : ℚ) : FractionRing (CoefficientOrder a b c))=1 := by
    rw [Rat.cast_div,div_eq_mul_inv,← FractionalIdeal.spanSingleton_mul_spanSingleton,h,
      FractionalIdeal.spanSingleton_mul_spanSingleton,mul_inv_cancel₀, FractionalIdeal.spanSingleton_one]
    exact_mod_cast (ne_of_gt hs)
  have hh := rat_eq_one_of_spanSingleton_eq_one a b c hD (r/s) (div_pos hr hs) hscale
  exact (div_eq_one_iff_eq (ne_of_gt hs)).mp hh

/-- Conjugation acts on the fractional-ideal carrier, preserving
products and units through the semilinear ring-equivalence API. -/
noncomputable def fractionalConjugation :
    FractionalIdeal (CoefficientOrder a b c)⁰ (FractionRing (CoefficientOrder a b c)) ≃+*
      FractionalIdeal (CoefficientOrder a b c)⁰ (FractionRing (CoefficientOrder a b c)) :=
  FractionalIdeal.ringEquivOfRingEquiv _ _
    (starRingAut : CoefficientOrder a b c ≃+* CoefficientOrder a b c)

lemma fractionalConjugation_spanSingleton (z : FractionRing (CoefficientOrder a b c)) :
    fractionalConjugation a b c (FractionalIdeal.spanSingleton (CoefficientOrder a b c)⁰ z)=
      FractionalIdeal.spanSingleton (CoefficientOrder a b c)⁰ (fractionConjugation a b c z) :=
  FractionalIdeal.ringEquivOfRingEquiv_spanSingleton _ _ _ _

lemma fractionConjugation_involutive (hD : b^2-4*a*c < 0) :
    Function.Involutive (fractionConjugation a b c) := by
  intro z
  letI := rationalField a b c hD
  apply (fractionRationalMap a b c hD).injective
  rw [fractionRationalMap_conjugation,fractionRationalMap_conjugation,star_star]

lemma mem_fractionalConjugation_iff (hD : b^2-4*a*c < 0)
    (I : FractionalIdeal (CoefficientOrder a b c)⁰ (FractionRing (CoefficientOrder a b c)))
    (x : FractionRing (CoefficientOrder a b c)) :
    x ∈ fractionalConjugation a b c I ↔ fractionConjugation a b c x ∈ I := by
  let e : CoefficientOrder a b c ≃+* CoefficientOrder a b c := starRingAut
  letI : RingHomInvPair (e : CoefficientOrder a b c →+* CoefficientOrder a b c)
      (e.symm : CoefficientOrder a b c →+* CoefficientOrder a b c) := RingHomInvPair.of_ringEquiv e
  letI : RingHomInvPair (e.symm : CoefficientOrder a b c →+* CoefficientOrder a b c)
      (e : CoefficientOrder a b c →+* CoefficientOrder a b c) := RingHomInvPair.of_ringEquiv e.symm
  change x ∈ Submodule.map
    (IsFractionRing.semilinearEquivOfRingEquiv (FractionRing (CoefficientOrder a b c))
      (FractionRing (CoefficientOrder a b c)) e).toLinearMap
      (I : Submodule (CoefficientOrder a b c) (FractionRing (CoefficientOrder a b c))) ↔ _
  rw [Submodule.mem_map]
  change (∃ y, y ∈ I ∧ fractionConjugation a b c y=x) ↔ _
  constructor
  · rintro ⟨y,hy,rfl⟩
    simpa only [fractionConjugation_involutive a b c hD y] using hy
  · intro hx
    exact ⟨fractionConjugation a b c x,hx,fractionConjugation_involutive a b c hD x⟩

/-- Conjugation of an integral ideal agrees with the actual order involution. -/
lemma fractionalConjugation_coeIdeal (hD : b^2-4*a*c < 0) (I : Ideal (CoefficientOrder a b c)) :
    fractionalConjugation a b c (I : FractionalIdeal (CoefficientOrder a b c)⁰
      (FractionRing (CoefficientOrder a b c)))=
      (I.comap (starRingAut : CoefficientOrder a b c ≃+* CoefficientOrder a b c).toRingHom :
        FractionalIdeal (CoefficientOrder a b c)⁰ (FractionRing (CoefficientOrder a b c))) := by
  ext x
  rw [mem_fractionalConjugation_iff a b c hD,FractionalIdeal.mem_coeIdeal,FractionalIdeal.mem_coeIdeal]
  constructor
  · rintro ⟨r,hr,heq⟩
    refine ⟨star r,?_,?_⟩
    · change star (star r) ∈ I
      simpa only [star_star] using hr
    · have h := congrArg (fractionConjugation a b c) heq
      rwa [fractionConjugation_algebraMap,fractionConjugation_involutive a b c hD] at h
  · rintro ⟨r,hr,heq⟩
    refine ⟨star r,hr,?_⟩
    rw [← heq,fractionConjugation_algebraMap]

omit [IsDomain (CoefficientOrder a b c)] in
lemma coefficientOrderEquivOfShift_star (d e f k : ℤ)
    (hb : b=e+2*k) (hac : a*c=d*f+e*k+k^2) (z : CoefficientOrder a b c) :
    coefficientOrderEquivOfShift a b c d e f k hb hac (star z)=
      star (coefficientOrderEquivOfShift a b c d e f k hb hac z) := by
  apply QuadraticAlgebra.ext
  · change z.re+b*z.im+k*(-z.im)=z.re+k*z.im+e*z.im
    linear_combination z.im*hb
  · rfl

omit [IsDomain (CoefficientOrder a b c)] in
lemma coefficientOrderEquivOfDiscriminant_star (d e f : ℤ)
    (hD : b^2-4*a*c=e^2-4*d*f) (z : CoefficientOrder a b c) :
    coefficientOrderEquivOfDiscriminant a b c d e f hD (star z)=
      star (coefficientOrderEquivOfDiscriminant a b c d e f hD z) := by
  unfold coefficientOrderEquivOfDiscriminant
  exact coefficientOrderEquivOfShift_star a b c d e f _ _ _ z

/-- Exact product/scaling norm identity, without an ideal-index norm API.
The scale convention is I1*I2=(gamma)*I3. -/
theorem norm_scale_of_fractional_product (hD : b^2-4*a*c < 0)
    (I1 I2 I3 : FractionalIdeal (CoefficientOrder a b c)⁰ (FractionRing (CoefficientOrder a b c)))
    (A1 A2 A3 : ℚ) (hA1 : 0<A1) (hA2 : 0<A2) (hA3 : 0<A3)
    (h1 : I1*fractionalConjugation a b c I1=
      FractionalIdeal.spanSingleton (CoefficientOrder a b c)⁰ (A1 : FractionRing (CoefficientOrder a b c)))
    (h2 : I2*fractionalConjugation a b c I2=
      FractionalIdeal.spanSingleton (CoefficientOrder a b c)⁰ (A2 : FractionRing (CoefficientOrder a b c)))
    (h3 : I3*fractionalConjugation a b c I3=
      FractionalIdeal.spanSingleton (CoefficientOrder a b c)⁰ (A3 : FractionRing (CoefficientOrder a b c)))
    (gamma : FractionRing (CoefficientOrder a b c)) (hgamma : gamma ≠ 0)
    (hprod : I1*I2=FractionalIdeal.spanSingleton (CoefficientOrder a b c)⁰ gamma*I3) :
    fractionNorm a b c hD gamma*A3=A1*A2 := by
  letI := fractionField_charZero a b c hD
  have hp : FractionalIdeal.spanSingleton (CoefficientOrder a b c)⁰
        ((A1*A2 : ℚ) : FractionRing (CoefficientOrder a b c))=
      FractionalIdeal.spanSingleton (CoefficientOrder a b c)⁰
        ((fractionNorm a b c hD gamma*A3 : ℚ) : FractionRing (CoefficientOrder a b c)) := by
    calc
      _ = (I1*fractionalConjugation a b c I1)*(I2*fractionalConjugation a b c I2) := by
        rw [h1,h2,FractionalIdeal.spanSingleton_mul_spanSingleton,Rat.cast_mul]
      _ = (I1*I2)*fractionalConjugation a b c (I1*I2) := by rw [map_mul]; ring
      _ = (FractionalIdeal.spanSingleton (CoefficientOrder a b c)⁰ gamma*I3)*
          fractionalConjugation a b c (FractionalIdeal.spanSingleton (CoefficientOrder a b c)⁰ gamma*I3) := by rw [hprod]
      _ = (FractionalIdeal.spanSingleton (CoefficientOrder a b c)⁰ gamma*
          FractionalIdeal.spanSingleton (CoefficientOrder a b c)⁰ (fractionConjugation a b c gamma))*
          (I3*fractionalConjugation a b c I3) := by
        rw [map_mul,fractionalConjugation_spanSingleton]; ring
      _ = _ := by
        rw [FractionalIdeal.spanSingleton_mul_spanSingleton,fraction_mul_conjugation a b c hD,h3,
          FractionalIdeal.spanSingleton_mul_spanSingleton,Rat.cast_mul]
  exact (rat_eq_of_spanSingleton_eq a b c hD _ _ (mul_pos hA1 hA2)
    (mul_pos (fractionNorm_pos a b c hD gamma hgamma) hA3) hp).symm

end BinaryNormIdeal

namespace PositiveDefiniteIntegralLattice

open BinaryNormIdeal
open scoped nonZeroDivisors

lemma binaryCoefficientOrderEquivDiscriminantOrder_star (K : PositiveDefiniteIntegralLattice 2)
    (z : K.binaryCoefficientOrder) :
    K.binaryCoefficientOrderEquivDiscriminantOrder (star z)=
      star (K.binaryCoefficientOrderEquivDiscriminantOrder z) := by
  unfold binaryCoefficientOrderEquivDiscriminantOrder coefficientOrderEquivDiscriminantOrder
  exact coefficientOrderEquivOfDiscriminant_star _ _ _ _ _ _ _ z

/-- The original transported conjugate ideal is literally conjugation in
its fixed common order, with the same integral generator translation. -/
lemma binaryDiscriminantConjugateNormIdeal_eq_comap_star (K : PositiveDefiniteIntegralLattice 2) :
    K.binaryDiscriminantConjugateNormIdeal=K.binaryDiscriminantNormIdeal.comap
      (starRingAut : DiscriminantOrder K.binaryPrimitiveDiscriminant ≃+*
        DiscriminantOrder K.binaryPrimitiveDiscriminant).toRingHom := by
  ext z
  let E := K.binaryCoefficientOrderEquivDiscriminantOrder
  change star (E.symm z) ∈ K.binaryNormIdeal ↔ E.symm (star z) ∈ K.binaryNormIdeal
  have hh : E.symm (star z)=star (E.symm z) := by
    apply E.injective
    rw [E.apply_symm_apply,K.binaryCoefficientOrderEquivDiscriminantOrder_star,E.apply_symm_apply]
  rw [hh]

/-- The original actual norm ideal satisfies the conjugate scale identity
inside the canonical fractional-ideal carrier and its actual conjugation. -/
theorem binaryFractionalNormIdeal_mul_fractionalConjugation (K : PositiveDefiniteIntegralLattice 2) :
    letI := K.binaryDiscriminantOrder_isDomain
    K.binaryFractionalNormIdeal*fractionalConjugation 1 (K.binaryPrimitiveDiscriminant%2)
      (((K.binaryPrimitiveDiscriminant%2)^2-K.binaryPrimitiveDiscriminant)/4)
      K.binaryFractionalNormIdeal=
      FractionalIdeal.spanSingleton (DiscriminantOrder K.binaryPrimitiveDiscriminant)⁰
        (((K.pairingMatrix 0 0/(K.binaryContent : ℤ) : ℤ) :
          FractionRing (DiscriminantOrder K.binaryPrimitiveDiscriminant))) := by
  letI := K.binaryDiscriminantOrder_isDomain
  have hneg := discriminantOrder_coefficients K.binaryPrimitiveDiscriminant K.binaryPrimitiveDiscriminant_mod_four
  have hn : (K.binaryPrimitiveDiscriminant%2)^2-
      4*1*(((K.binaryPrimitiveDiscriminant%2)^2-K.binaryPrimitiveDiscriminant)/4)<0 := by
    rw [hneg]
    exact K.binaryPrimitiveDiscriminant_neg
  change (K.binaryDiscriminantNormIdeal : K.BinaryDiscriminantFractionalIdeals)*
    fractionalConjugation 1 (K.binaryPrimitiveDiscriminant%2)
      (((K.binaryPrimitiveDiscriminant%2)^2-K.binaryPrimitiveDiscriminant)/4)
      (K.binaryDiscriminantNormIdeal : K.BinaryDiscriminantFractionalIdeals)=_
  rw [fractionalConjugation_coeIdeal _ _ _ hn,← K.binaryDiscriminantConjugateNormIdeal_eq_comap_star,
    ← FractionalIdeal.coeIdeal_mul,K.binaryDiscriminantNormIdeal_mul_conjugate,
    FractionalIdeal.coeIdeal_span_singleton]
  simp only [map_intCast]


lemma binaryDiscriminantOrder_discriminant_neg (K : PositiveDefiniteIntegralLattice 2) :
    (K.binaryPrimitiveDiscriminant%2)^2-
      4*1*(((K.binaryPrimitiveDiscriminant%2)^2-K.binaryPrimitiveDiscriminant)/4)<0 := by
  rw [discriminantOrder_coefficients K.binaryPrimitiveDiscriminant K.binaryPrimitiveDiscriminant_mod_four]
  exact K.binaryPrimitiveDiscriminant_neg

/-- The rational norm on the original binary lattice's canonical field. -/
noncomputable def binaryFractionNorm (K : PositiveDefiniteIntegralLattice 2) :
    letI := K.binaryDiscriminantOrder_isDomain
    FractionRing (DiscriminantOrder K.binaryPrimitiveDiscriminant) →* ℚ := by
  letI := K.binaryDiscriminantOrder_isDomain
  exact fractionNorm 1 (K.binaryPrimitiveDiscriminant%2)
    (((K.binaryPrimitiveDiscriminant%2)^2-K.binaryPrimitiveDiscriminant)/4)
    K.binaryDiscriminantOrder_discriminant_neg

lemma binaryFractionalNormIdealUnitAt_mul_fractionalConjugation
    (L : PositiveDefiniteIntegralLattice 2) (D : ℤ) (hD : L.binaryPrimitiveDiscriminant=D)
    [IsDomain (DiscriminantOrder D)] :
    (binaryFractionalNormIdealUnitAt L D hD : FractionalIdeal (DiscriminantOrder D)⁰ (FractionRing (DiscriminantOrder D)))*
      fractionalConjugation 1 (D%2) (((D%2)^2-D)/4)
        (binaryFractionalNormIdealUnitAt L D hD : FractionalIdeal (DiscriminantOrder D)⁰ (FractionRing (DiscriminantOrder D)))=
      FractionalIdeal.spanSingleton (DiscriminantOrder D)⁰
        (((L.pairingMatrix 0 0/(L.binaryContent : ℤ) : ℤ) : FractionRing (DiscriminantOrder D))) := by
  subst D
  exact L.binaryFractionalNormIdeal_mul_fractionalConjugation

/-- Product scaling of the actual normalized ideals has the exact leading
coefficient norm scale. Contents may differ; the actual discriminant is fixed. -/
theorem binaryFractionNorm_mul_leading_eq_of_ideal_product
    (K L M : PositiveDefiniteIntegralLattice 2)
    (hL : L.binaryPrimitiveDiscriminant=K.binaryPrimitiveDiscriminant)
    (hM : M.binaryPrimitiveDiscriminant=K.binaryPrimitiveDiscriminant)
    (gamma : FractionRing (DiscriminantOrder K.binaryPrimitiveDiscriminant)) (hgamma : gamma ≠ 0)
    (hprod : letI := K.binaryDiscriminantOrder_isDomain
      (binaryFractionalNormIdealUnitAt K K.binaryPrimitiveDiscriminant rfl : K.BinaryDiscriminantFractionalIdeals)*
        (binaryFractionalNormIdealUnitAt L K.binaryPrimitiveDiscriminant hL : K.BinaryDiscriminantFractionalIdeals)=
      FractionalIdeal.spanSingleton (DiscriminantOrder K.binaryPrimitiveDiscriminant)⁰ gamma*
        (binaryFractionalNormIdealUnitAt M K.binaryPrimitiveDiscriminant hM : K.BinaryDiscriminantFractionalIdeals)) :
    letI := K.binaryDiscriminantOrder_isDomain
    K.binaryFractionNorm gamma*(M.pairingMatrix 0 0/(M.binaryContent : ℤ) : ℤ)=
      (K.pairingMatrix 0 0/(K.binaryContent : ℤ) : ℤ)*(L.pairingMatrix 0 0/(L.binaryContent : ℤ) : ℤ) := by
  letI := K.binaryDiscriminantOrder_isDomain
  letI := fractionField_charZero 1 (K.binaryPrimitiveDiscriminant%2)
    (((K.binaryPrimitiveDiscriminant%2)^2-K.binaryPrimitiveDiscriminant)/4)
    K.binaryDiscriminantOrder_discriminant_neg
  have hc (N : PositiveDefiniteIntegralLattice 2) : (0 : ℚ)<(N.pairingMatrix 0 0/(N.binaryContent : ℤ) : ℤ) := by
    exact_mod_cast N.binaryPrimitivePolynomial_leading_pos
  have hconj (N : PositiveDefiniteIntegralLattice 2) (hN : N.binaryPrimitiveDiscriminant=K.binaryPrimitiveDiscriminant) :
      (binaryFractionalNormIdealUnitAt N K.binaryPrimitiveDiscriminant hN : K.BinaryDiscriminantFractionalIdeals)*
        fractionalConjugation 1 (K.binaryPrimitiveDiscriminant%2)
          (((K.binaryPrimitiveDiscriminant%2)^2-K.binaryPrimitiveDiscriminant)/4)
          (binaryFractionalNormIdealUnitAt N K.binaryPrimitiveDiscriminant hN : K.BinaryDiscriminantFractionalIdeals)=
        FractionalIdeal.spanSingleton (DiscriminantOrder K.binaryPrimitiveDiscriminant)⁰
          ((((N.pairingMatrix 0 0/(N.binaryContent : ℤ) : ℤ) : ℚ) : FractionRing (DiscriminantOrder K.binaryPrimitiveDiscriminant))) := by
    simpa only [Rat.cast_intCast] using binaryFractionalNormIdealUnitAt_mul_fractionalConjugation N _ hN
  exact norm_scale_of_fractional_product 1 (K.binaryPrimitiveDiscriminant%2)
    (((K.binaryPrimitiveDiscriminant%2)^2-K.binaryPrimitiveDiscriminant)/4)
    K.binaryDiscriminantOrder_discriminant_neg
    _ _ _ _ _ _ (hc K) (hc L) (hc M) (hconj K rfl) (hconj L hL) (hconj M hM) gamma hgamma hprod

/-- A product equality in the existing canonical class group supplies the
actual nonzero principal factor and its exact rational norm scale. -/
theorem exists_binaryIdealProduct_scaling_of_class_mul
    (K L M : PositiveDefiniteIntegralLattice 2)
    (hL : L.binaryPrimitiveDiscriminant=K.binaryPrimitiveDiscriminant)
    (hM : M.binaryPrimitiveDiscriminant=K.binaryPrimitiveDiscriminant)
    (hclass : letI := K.binaryDiscriminantOrder_isDomain
      binaryIdealClassAt K K.binaryPrimitiveDiscriminant rfl*
        binaryIdealClassAt L K.binaryPrimitiveDiscriminant hL=
      binaryIdealClassAt M K.binaryPrimitiveDiscriminant hM) :
    letI := K.binaryDiscriminantOrder_isDomain
    ∃ gamma : (FractionRing (DiscriminantOrder K.binaryPrimitiveDiscriminant))ˣ,
      (binaryFractionalNormIdealUnitAt K K.binaryPrimitiveDiscriminant rfl : K.BinaryDiscriminantFractionalIdeals)*
        (binaryFractionalNormIdealUnitAt L K.binaryPrimitiveDiscriminant hL : K.BinaryDiscriminantFractionalIdeals)=
      FractionalIdeal.spanSingleton (DiscriminantOrder K.binaryPrimitiveDiscriminant)⁰ gamma.val*
        (binaryFractionalNormIdealUnitAt M K.binaryPrimitiveDiscriminant hM : K.BinaryDiscriminantFractionalIdeals) ∧
      K.binaryFractionNorm gamma.val*(M.pairingMatrix 0 0/(M.binaryContent : ℤ) : ℤ)=
        (K.pairingMatrix 0 0/(K.binaryContent : ℤ) : ℤ)*(L.pairingMatrix 0 0/(L.binaryContent : ℤ) : ℤ) := by
  letI := K.binaryDiscriminantOrder_isDomain
  let O := DiscriminantOrder K.binaryPrimitiveDiscriminant
  let F := FractionRing O
  let I := binaryFractionalNormIdealUnitAt K K.binaryPrimitiveDiscriminant rfl
  let J := binaryFractionalNormIdealUnitAt L K.binaryPrimitiveDiscriminant hL
  let H := binaryFractionalNormIdealUnitAt M K.binaryPrimitiveDiscriminant hM
  have hh : ClassGroup.mk F (I*J)=ClassGroup.mk F H := by
    rw [map_mul]
    exact hclass
  obtain ⟨x,hx⟩ := ClassGroup.mk_eq_mk.mp hh
  let gamma := x⁻¹
  have hp : I*J=toPrincipalIdeal O F gamma*H := by
    change I*J=toPrincipalIdeal O F (x⁻¹)*H
    rw [map_inv]
    exact (eq_mul_inv_of_mul_eq hx).trans (mul_comm _ _)
  have hp' : (I : K.BinaryDiscriminantFractionalIdeals)*(J : K.BinaryDiscriminantFractionalIdeals)=
      FractionalIdeal.spanSingleton O⁰ gamma.val*(H : K.BinaryDiscriminantFractionalIdeals) := by
    have h := congrArg (fun u : (FractionalIdeal O⁰ F)ˣ => (u : FractionalIdeal O⁰ F)) hp
    simpa only [Units.val_mul,coe_toPrincipalIdeal] using h
  exact ⟨gamma,hp',binaryFractionNorm_mul_leading_eq_of_ideal_product K L M hL hM
    gamma.val gamma.ne_zero hp'⟩


/-- Every product of actual same-discriminant ideal classes has an actual
lattice representative at K's original content, with the exact principal
factor and rational norm scale. No genus membership is asserted. -/
theorem exists_binaryIdealProduct_realization (K L : PositiveDefiniteIntegralLattice 2)
    (hL : L.binaryPrimitiveDiscriminant=K.binaryPrimitiveDiscriminant) :
    letI := K.binaryDiscriminantOrder_isDomain
    ∃ (M : PositiveDefiniteIntegralLattice 2), M.binaryContent=K.binaryContent ∧
      ∃ (hM : M.binaryPrimitiveDiscriminant=K.binaryPrimitiveDiscriminant)
        (gamma : (FractionRing (DiscriminantOrder K.binaryPrimitiveDiscriminant))ˣ),
        binaryIdealClassAt M K.binaryPrimitiveDiscriminant hM=
          binaryIdealClassAt K K.binaryPrimitiveDiscriminant rfl*
            binaryIdealClassAt L K.binaryPrimitiveDiscriminant hL ∧
        (binaryFractionalNormIdealUnitAt K K.binaryPrimitiveDiscriminant rfl : K.BinaryDiscriminantFractionalIdeals)*
          (binaryFractionalNormIdealUnitAt L K.binaryPrimitiveDiscriminant hL : K.BinaryDiscriminantFractionalIdeals)=
        FractionalIdeal.spanSingleton (DiscriminantOrder K.binaryPrimitiveDiscriminant)⁰ gamma.val*
          (binaryFractionalNormIdealUnitAt M K.binaryPrimitiveDiscriminant hM : K.BinaryDiscriminantFractionalIdeals) ∧
        K.binaryFractionNorm gamma.val*(M.pairingMatrix 0 0/(M.binaryContent : ℤ) : ℤ)=
          (K.pairingMatrix 0 0/(K.binaryContent : ℤ) : ℤ)*(L.pairingMatrix 0 0/(L.binaryContent : ℤ) : ℤ) := by
  letI := K.binaryDiscriminantOrder_isDomain
  obtain ⟨M,hg,hM,hclass⟩ := K.exists_lattice_of_binaryIdealClass
    (binaryIdealClassAt K K.binaryPrimitiveDiscriminant rfl*
      binaryIdealClassAt L K.binaryPrimitiveDiscriminant hL)
  obtain ⟨gamma,hprod,hscale⟩ := exists_binaryIdealProduct_scaling_of_class_mul K L M hL hM hclass.symm
  exact ⟨M,hg,hM,gamma,hclass,hprod,hscale⟩

end PositiveDefiniteIntegralLattice

#assert_standard_axioms BinaryNormIdeal.fractionRationalMap
#assert_standard_axioms BinaryNormIdeal.fractionRationalMap_algebraMap
#assert_standard_axioms BinaryNormIdeal.fractionNorm
#assert_standard_axioms BinaryNormIdeal.fractionNorm_algebraMap
#assert_standard_axioms BinaryNormIdeal.fractionNorm_pos
#assert_standard_axioms BinaryNormIdeal.fractionConjugation
#assert_standard_axioms BinaryNormIdeal.fractionConjugation_algebraMap
#assert_standard_axioms BinaryNormIdeal.fractionRationalMap_conjugation
#assert_standard_axioms BinaryNormIdeal.fraction_mul_conjugation
#assert_standard_axioms BinaryNormIdeal.rat_mem_fractional_one_iff
#assert_standard_axioms BinaryNormIdeal.fractionField_charZero
#assert_standard_axioms BinaryNormIdeal.rat_eq_one_of_spanSingleton_eq_one
#assert_standard_axioms BinaryNormIdeal.rat_eq_of_spanSingleton_eq
#assert_standard_axioms BinaryNormIdeal.fractionalConjugation
#assert_standard_axioms BinaryNormIdeal.fractionalConjugation_spanSingleton
#assert_standard_axioms BinaryNormIdeal.fractionConjugation_involutive
#assert_standard_axioms BinaryNormIdeal.mem_fractionalConjugation_iff
#assert_standard_axioms BinaryNormIdeal.fractionalConjugation_coeIdeal
#assert_standard_axioms BinaryNormIdeal.coefficientOrderEquivOfShift_star
#assert_standard_axioms BinaryNormIdeal.coefficientOrderEquivOfDiscriminant_star
#assert_standard_axioms BinaryNormIdeal.norm_scale_of_fractional_product
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryCoefficientOrderEquivDiscriminantOrder_star
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryDiscriminantConjugateNormIdeal_eq_comap_star
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryFractionalNormIdeal_mul_fractionalConjugation
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryDiscriminantOrder_discriminant_neg
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryFractionNorm
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryFractionalNormIdealUnitAt_mul_fractionalConjugation
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryFractionNorm_mul_leading_eq_of_ideal_product
#assert_standard_axioms PositiveDefiniteIntegralLattice.exists_binaryIdealProduct_scaling_of_class_mul
#assert_standard_axioms PositiveDefiniteIntegralLattice.exists_binaryIdealProduct_realization
