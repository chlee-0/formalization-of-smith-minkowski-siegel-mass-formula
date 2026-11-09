import SMSFormula.BinaryIdealScale
import SMSFormula.BinaryLocalNorm

/-!
# Actual local binary ideal extension

Coefficient maps land in the genuine quadratic scalar algebra, which can
split. Ideals are extended as submodule spans over the actual local order.
No field structure is assumed on that algebra.
-/

namespace Submodule

open scoped Pointwise

variable {R S K A : Type*} [CommRing R] [CommRing S] [CommRing K] [CommRing A]
  [Algebra R K] [Algebra S A]

/-- Extension of a submodule by taking the span over the target scalar ring. -/
def ringSpanExtension (g : K →+* A) (I : Submodule R K) : Submodule S A :=
  span S (g '' (I : Set K))

/-- Span extension needs scalar compatibility, not a local field. -/
lemma ringSpanExtension_span (f : R →+* S) (g : K →+* A)
    (hg : ∀ r, g (algebraMap R K r)=algebraMap S A (f r)) (s : Set K) :
    ringSpanExtension (S := S) g (span R s)=span S (g '' s) := by
  apply le_antisymm
  · apply span_le.mpr
    rintro _ ⟨x,hx,rfl⟩
    refine span_induction (fun y hy => subset_span ⟨y,hy,rfl⟩) (by simp)
      (fun x y _ _ hx hy => ?_) (fun r y _ hy => ?_) hx
    · rw [map_add]
      exact (span S (g '' s)).add_mem hx hy
    · rw [Algebra.smul_def,map_mul,hg,← Algebra.smul_def]
      exact smul_mem _ (f r) hy
  · apply span_le.mpr
    rintro _ ⟨x,hx,rfl⟩
    exact subset_span ⟨x,subset_span hx,rfl⟩

lemma ringSpanExtension_mul (f : R →+* S) (g : K →+* A)
    (hg : ∀ r, g (algebraMap R K r)=algebraMap S A (f r))
    (I J : Submodule R K) :
    ringSpanExtension (S := S) g (I*J)=ringSpanExtension (S := S) g I*ringSpanExtension (S := S) g J := by
  rw [Submodule.mul_eq_span_mul_set,ringSpanExtension_span f g hg]
  change span S (g '' ((I : Set K)*(J : Set K)))=span S (g '' (I : Set K))*span S (g '' (J : Set K))
  rw [span_mul_span]
  congr 1
  ext x
  constructor
  · rintro ⟨_,h,rfl⟩
    obtain ⟨i,hi,j,hj,rfl⟩ := Set.mem_mul.mp h
    exact Set.mem_mul.mpr ⟨g i,⟨i,hi,rfl⟩,g j,⟨j,hj,rfl⟩,(map_mul g i j).symm⟩
  · intro h
    obtain ⟨_,⟨i,hi,rfl⟩,_,⟨j,hj,rfl⟩,rfl⟩ := Set.mem_mul.mp h
    exact ⟨i*j,Set.mem_mul.mpr ⟨i,hi,j,hj,rfl⟩,map_mul g i j⟩

lemma ringSpanExtension_one (f : R →+* S) (g : K →+* A)
    (hg : ∀ r, g (algebraMap R K r)=algebraMap S A (f r)) :
    ringSpanExtension (S := S) g (1 : Submodule R K)=1 := by
  rw [one_eq_span,ringSpanExtension_span f g hg]
  simp only [Set.image_singleton,map_one]
  exact one_eq_span.symm

/-- Multiplicative scalar extension into submodules of a commutative algebra. -/
def ringSpanExtensionHom (f : R →+* S) (g : K →+* A)
    (hg : ∀ r, g (algebraMap R K r)=algebraMap S A (f r)) :
    Submodule R K →* Submodule S A where
  toFun := ringSpanExtension g
  map_one' := ringSpanExtension_one f g hg
  map_mul' := ringSpanExtension_mul f g hg

/-- Two unit generators of the same principal scalar submodule differ by
an actual scalar-ring unit, even if the ambient algebra has zero divisors. -/
theorem exists_scalar_unit_of_span_eq
    (hinj : Function.Injective (algebraMap S A)) (beta delta : Aˣ)
    (h : span S {(beta : A)}=span S {(delta : A)}) :
    ∃ e : Sˣ, algebraMap S A (e : S)*(delta : A)=(beta : A) := by
  have hb : (beta : A) ∈ span S {(delta : A)} := h ▸ mem_span_singleton_self _
  have hd : (delta : A) ∈ span S {(beta : A)} := h.symm ▸ mem_span_singleton_self _
  obtain ⟨r,hr⟩ := mem_span_singleton.mp hb
  obtain ⟨t,ht⟩ := mem_span_singleton.mp hd
  rw [Algebra.smul_def] at hr ht
  have hm : (algebraMap S A r*algebraMap S A t)*(beta : A)=(beta : A) := by
    rw [mul_assoc,ht,hr]
  have hh := congrArg (fun x : A => x*(↑(beta⁻¹) : A)) hm
  have hrt : r*t=1 := by
    apply hinj
    rw [map_mul,map_one]
    simpa only [mul_assoc,Units.mul_inv,mul_one] using hh
  exact ⟨⟨r,t,hrt,by rw [mul_comm,hrt]⟩,hr⟩

/-- Extending an ideal span uses exactly its displayed generators. -/
lemma span_image_ideal_span (s : Set S) :
    span S ((algebraMap S A) '' (Ideal.span s : Set S))=
      span S ((algebraMap S A) '' s) := by
  exact ringSpanExtension_span (RingHom.id S) (algebraMap S A) (fun _ => rfl) s

end Submodule

namespace FractionalIdeal

open scoped nonZeroDivisors

variable {R S K A : Type*} [CommRing R] [CommRing S] [CommRing K] [CommRing A]
  [Algebra R K] [Algebra S A]

/-- Honest extension of actual fractional ideals as scalar-order submodules.
The local ambient algebra is only a commutative ring. -/
def scalarSpanExtension (f : R →+* S) (g : K →+* A)
    (hg : ∀ r, g (algebraMap R K r)=algebraMap S A (f r)) :
    FractionalIdeal R⁰ K →* Submodule S A :=
  (Submodule.ringSpanExtensionHom f g hg).comp (coeSubmoduleHom R⁰ K).toMonoidHom

lemma scalarSpanExtension_spanSingleton [IsLocalization R⁰ K] (f : R →+* S) (g : K →+* A)
    (hg : ∀ r, g (algebraMap R K r)=algebraMap S A (f r)) (x : K) :
    scalarSpanExtension f g hg (spanSingleton R⁰ x)=Submodule.span S {g x} := by
  change Submodule.ringSpanExtension g ((spanSingleton R⁰ x : FractionalIdeal R⁰ K) : Submodule R K)=_
  rw [coe_spanSingleton,Submodule.ringSpanExtension_span f g hg,Set.image_singleton]

/-- Extending an integral ideal span extends its actual generators. -/
lemma scalarSpanExtension_coeIdeal_span [IsLocalization R⁰ K]
    (f : R →+* S) (g : K →+* A)
    (hg : ∀ r, g (algebraMap R K r)=algebraMap S A (f r)) (s : Set R) :
    scalarSpanExtension f g hg (Ideal.span s : FractionalIdeal R⁰ K)=
      Submodule.span S ((algebraMap S A) '' (f '' s)) := by
  change Submodule.ringSpanExtension g ((Ideal.span s : FractionalIdeal R⁰ K) : Submodule R K)=_
  rw [coe_coeIdeal,IsLocalization.coeSubmodule_span,Submodule.ringSpanExtension_span f g hg]
  rw [← Set.image_comp]
  have hh : (g : K → A) ∘ (algebraMap R K)=(algebraMap S A) ∘ f := funext hg
  rw [hh,Set.image_comp]

/-- The fractional extension agrees with extension of the integral ideal. -/
lemma scalarSpanExtension_coeIdeal [IsLocalization R⁰ K]
    (f : R →+* S) (g : K →+* A)
    (hg : ∀ r, g (algebraMap R K r)=algebraMap S A (f r)) (I : Ideal R) :
    scalarSpanExtension f g hg (I : FractionalIdeal R⁰ K)=
      Submodule.span S ((algebraMap S A) '' (Ideal.map f I : Set S)) := by
  conv_lhs => rw [← Ideal.span_eq I]
  rw [scalarSpanExtension_coeIdeal_span]
  conv_rhs => rw [← Ideal.span_eq I,Ideal.map_span]
  exact (Submodule.span_image_ideal_span _).symm

end FractionalIdeal

namespace BinaryNormIdeal

open scoped QuadraticAlgebra nonZeroDivisors

variable {R S : Type*} [CommRing R] [CommRing S]

/-- Coefficientwise scalar extension of the same integer order presentation. -/
def coefficientScalarMap (a b c : ℤ) (f : R →+* S) :
    CoefficientAlgebra (a : R) (b : R) (c : R) →+*
      CoefficientAlgebra (a : S) (b : S) (c : S) where
  toFun z := ⟨f z.re,f z.im⟩
  map_one' := by apply QuadraticAlgebra.ext <;> simp
  map_mul' z w := by apply QuadraticAlgebra.ext <;> simp
  map_zero' := by apply QuadraticAlgebra.ext <;> simp
  map_add' z w := by apply QuadraticAlgebra.ext <;> simp

lemma norm_coefficientScalarMap (a b c : ℤ) (f : R →+* S)
    (z : CoefficientAlgebra (a : R) (b : R) (c : R)) :
    (coefficientScalarMap a b c f z).norm=f z.norm := by
  simp [coefficientScalarMap,QuadraticAlgebra.norm_def]

lemma coefficientScalarMap_injective (a b c : ℤ) (f : R →+* S) (hf : Function.Injective f) :
    Function.Injective (coefficientScalarMap a b c f) := by
  intro z w h
  apply QuadraticAlgebra.ext
  · exact hf (congrArg QuadraticAlgebra.re h)
  · exact hf (congrArg QuadraticAlgebra.im h)

/-- Integral coefficients mapped into any scalar ring. -/
def orderScalarMap (a b c : ℤ) (R : Type*) [CommRing R] :
    CoefficientOrder a b c →+* CoefficientAlgebra (a : R) (b : R) (c : R) :=
  coefficientScalarMap a b c (Int.castRingHom R)

/-- The actual global fraction field maps to a quadratic scalar algebra.
Only the scalar R is a field; the target quadratic algebra can split. -/
noncomputable def fractionScalarMap (a b c : ℤ) [IsDomain (CoefficientOrder a b c)]
    (hD : b^2-4*a*c<0) (R : Type*) [Field R] [CharZero R] :
    FractionRing (CoefficientOrder a b c) →+* CoefficientAlgebra (a : R) (b : R) (c : R) :=
  (coefficientScalarMap a b c (Rat.castHom R)).comp (fractionRationalMap a b c hD)

lemma fractionScalarMap_injective (a b c : ℤ) [IsDomain (CoefficientOrder a b c)]
    (hD : b^2-4*a*c<0) (R : Type*) [Field R] [CharZero R] :
    Function.Injective (fractionScalarMap a b c hD R) :=
  (fractionScalarMap a b c hD R).injective

lemma fractionScalarMap_algebraMap (a b c : ℤ) [IsDomain (CoefficientOrder a b c)]
    (hD : b^2-4*a*c<0) (R : Type*) [Field R] [CharZero R] (z : CoefficientOrder a b c) :
    fractionScalarMap a b c hD R (algebraMap _ (FractionRing (CoefficientOrder a b c)) z)=
      orderScalarMap a b c R z := by
  change coefficientScalarMap a b c (Rat.castHom R)
    (fractionRationalMap a b c hD (algebraMap _ _ z))=_
  rw [fractionRationalMap_algebraMap]
  apply QuadraticAlgebra.ext <;> simp [coefficientScalarMap,rationalMap,orderScalarMap]

lemma norm_fractionScalarMap (a b c : ℤ) [IsDomain (CoefficientOrder a b c)]
    (hD : b^2-4*a*c<0) (R : Type*) [Field R] [CharZero R]
    (z : FractionRing (CoefficientOrder a b c)) :
    (fractionScalarMap a b c hD R z).norm=(fractionNorm a b c hD z : R) := by
  exact norm_coefficientScalarMap a b c (Rat.castHom R) (fractionRationalMap a b c hD z)

/-- Integral p-adic coefficients embedded in the genuine quadratic Q_p algebra. -/
noncomputable def padicOrderMap (p : ℕ) [Fact (Nat.Prime p)] (D : ℤ) :
    DiscriminantAlgebra ℤ_[p] D →+* DiscriminantAlgebra ℚ_[p] D :=
  coefficientScalarMap 1 (D%2) (((D%2)^2-D)/4) (algebraMap ℤ_[p] ℚ_[p])

lemma padicOrderMap_injective (p : ℕ) [Fact (Nat.Prime p)] (D : ℤ) :
    Function.Injective (padicOrderMap p D) :=
  coefficientScalarMap_injective _ _ _ _ (fun _ _ h => PadicInt.ext h)

/-- The actual local order acts on the quadratic Q_p algebra by its coefficient map. -/
@[reducible] noncomputable def padicOrderAlgebra (p : ℕ) [Fact (Nat.Prime p)] (D : ℤ) :
    Algebra (DiscriminantAlgebra ℤ_[p] D) (DiscriminantAlgebra ℚ_[p] D) :=
  (padicOrderMap p D).toAlgebra

/-- Integral generator translation commutes with extension of scalars. -/
lemma orderScalarMap_equiv (a b c a' b' c' : ℤ)
    (hD : b^2-4*a*c=b'^2-4*a'*c') (R : Type*) [CommRing R]
    (z : CoefficientOrder a b c) :
    orderScalarMap a' b' c' R (coefficientOrderEquivOfDiscriminant a b c a' b' c' hD z)=
      coefficientAlgebraEquivOfDiscriminant a b c a' b' c' hD
        (orderScalarMap a b c R z) := by
  apply QuadraticAlgebra.ext <;>
    simp [orderScalarMap,coefficientScalarMap,coefficientOrderEquivOfDiscriminant,
      coefficientOrderEquivOfShift,coefficientAlgebraEquivOfDiscriminant,
      coefficientAlgebraEquivOfShift]

/-- The scalar extension of the actual norm ideal is generated by any
vector of unit value, after the exact integral generator translation. -/
theorem map_normIdeal_principal (a b c a' b' c' : ℤ)
    (hD : b^2-4*a*c=b'^2-4*a'*c') (R : Type*) [CommRing R]
    (v : Fin 2 → R) (u : Rˣ)
    (hv : polynomialOver (a : R) (b : R) (c : R) v=(u : R)) :
    Ideal.map (orderScalarMap a' b' c' R)
      (Ideal.map (coefficientOrderEquivOfDiscriminant a b c a' b' c' hD).toRingHom
        (normIdeal a b c))=
    Ideal.span {coefficientAlgebraEquivOfDiscriminant a b c a' b' c' hD
      (normVector (a : R) (b : R) (c : R) v)} := by
  have hcomp : (orderScalarMap a' b' c' R).comp
      (coefficientOrderEquivOfDiscriminant a b c a' b' c' hD).toRingHom=
      (coefficientAlgebraEquivOfDiscriminant (R := R) a b c a' b' c' hD).toRingHom.comp
        (orderScalarMap a b c R) := by
    apply RingHom.ext
    intro z
    exact orderScalarMap_equiv _ _ _ _ _ _ hD R z
  rw [Ideal.map_map,hcomp,← Ideal.map_map]
  have hbase : Ideal.map (orderScalarMap a b c R) (normIdeal a b c)=
      Ideal.span {algebraMap R (CoefficientAlgebra (a : R) (b : R) (c : R)) (a : R),
        QuadraticAlgebra.omega} := by
    rw [normIdeal_eq_span,Ideal.map_span]
    congr 1
    simp only [Set.image_insert_eq,Set.image_singleton]
    congr 2 <;> apply QuadraticAlgebra.ext <;> simp [orderScalarMap,coefficientScalarMap]
  rw [hbase,span_eq_principal_of_unit_value _ _ _ v u hv,Ideal.map_span,Set.image_singleton]
  rfl

end BinaryNormIdeal

namespace PositiveDefiniteIntegralLattice

open BinaryNormIdeal
open scoped nonZeroDivisors

/-- The local generator in the same discriminant order, with its original
integer coordinate action. No leading coefficient is inverted. -/
def binaryLocalIdealGeneratorAt (L : PositiveDefiniteIntegralLattice 2) (D : ℤ)
    (hD : L.binaryPrimitiveDiscriminant=D) (R : Type*) [CommRing R]
    (v : Fin 2 → R) : DiscriminantAlgebra R D :=
  coefficientAlgebraEquivOfDiscriminant
    (L.pairingMatrix 0 0/(L.binaryContent : ℤ))
    (2*L.pairingMatrix 0 1/(L.binaryContent : ℤ))
    (L.pairingMatrix 1 1/(L.binaryContent : ℤ))
    1 (D%2) (((D%2)^2-D)/4)
    (hD.trans (discriminantOrder_coefficients D (hD ▸ L.binaryPrimitiveDiscriminant_mod_four)).symm)
    (normVector _ _ _ v)

lemma norm_binaryLocalIdealGeneratorAt (L : PositiveDefiniteIntegralLattice 2) (D : ℤ)
    (hD : L.binaryPrimitiveDiscriminant=D) (R : Type*) [CommRing R]
    (v : Fin 2 → R) :
    (L.binaryLocalIdealGeneratorAt D hD R v).norm=
      ((L.pairingMatrix 0 0/(L.binaryContent : ℤ) : ℤ) : R)*L.binaryPrimitivePolynomialOver R v := by
  unfold binaryLocalIdealGeneratorAt
  rw [norm_coefficientAlgebraEquivOfDiscriminant,norm_normVector]
  simp only [polynomialOver,binaryPrimitivePolynomialOver_apply]

/-- Any actual represented unit makes the integral scalar extension principal. -/
theorem map_binaryDiscriminantNormIdealAt_principal (L : PositiveDefiniteIntegralLattice 2) (D : ℤ)
    (hD : L.binaryPrimitiveDiscriminant=D) (R : Type*) [CommRing R]
    (v : Fin 2 → R) (u : Rˣ) (hv : L.binaryPrimitivePolynomialOver R v=(u : R)) :
    Ideal.map (orderScalarMap 1 (D%2) (((D%2)^2-D)/4) R)
      (L.binaryDiscriminantNormIdealAt D hD)=
      Ideal.span {L.binaryLocalIdealGeneratorAt D hD R v} := by
  rw [binaryDiscriminantNormIdealAt_eq_map]
  exact map_normIdeal_principal _ _ _ _ _ _ _ R v u
    (by simpa only [polynomialOver,binaryPrimitivePolynomialOver_apply] using hv)

/-- The actual fraction field embeds in the genuine quadratic Q_p algebra.
The latter is allowed to split. -/
noncomputable def binaryPadicFractionMap (K : PositiveDefiniteIntegralLattice 2)
    (p : ℕ) [Fact (Nat.Prime p)] :
    letI := K.binaryDiscriminantOrder_isDomain
    FractionRing (DiscriminantOrder K.binaryPrimitiveDiscriminant) →+*
      DiscriminantAlgebra ℚ_[p] K.binaryPrimitiveDiscriminant := by
  letI := K.binaryDiscriminantOrder_isDomain
  exact fractionScalarMap _ _ _ K.binaryDiscriminantOrder_discriminant_neg ℚ_[p]

lemma binaryPadicFractionMap_compatible (K : PositiveDefiniteIntegralLattice 2)
    (p : ℕ) [Fact (Nat.Prime p)] (z : DiscriminantOrder K.binaryPrimitiveDiscriminant) :
    K.binaryPadicFractionMap p (algebraMap _ (FractionRing (DiscriminantOrder K.binaryPrimitiveDiscriminant)) z)=
      padicOrderMap p K.binaryPrimitiveDiscriminant
        (orderScalarMap 1 (K.binaryPrimitiveDiscriminant%2)
          (((K.binaryPrimitiveDiscriminant%2)^2-K.binaryPrimitiveDiscriminant)/4) ℤ_[p] z) := by
  letI := K.binaryDiscriminantOrder_isDomain
  rw [binaryPadicFractionMap,fractionScalarMap_algebraMap]
  apply QuadraticAlgebra.ext <;> simp [orderScalarMap,padicOrderMap,coefficientScalarMap]

/-- Multiplicative extension of the original fractional ideals to actual
local-order submodules. No field structure on the quadratic algebra is used. -/
noncomputable def binaryPadicIdealExtension (K : PositiveDefiniteIntegralLattice 2)
    (p : ℕ) [Fact (Nat.Prime p)] :
    letI := K.binaryDiscriminantOrder_isDomain
    letI := padicOrderAlgebra p K.binaryPrimitiveDiscriminant
    K.BinaryDiscriminantFractionalIdeals →*
      Submodule (DiscriminantAlgebra ℤ_[p] K.binaryPrimitiveDiscriminant)
        (DiscriminantAlgebra ℚ_[p] K.binaryPrimitiveDiscriminant) := by
  letI := K.binaryDiscriminantOrder_isDomain
  letI := padicOrderAlgebra p K.binaryPrimitiveDiscriminant
  exact FractionalIdeal.scalarSpanExtension
    (orderScalarMap 1 (K.binaryPrimitiveDiscriminant%2)
      (((K.binaryPrimitiveDiscriminant%2)^2-K.binaryPrimitiveDiscriminant)/4) ℤ_[p])
    (K.binaryPadicFractionMap p) (K.binaryPadicFractionMap_compatible p)

lemma binaryPadicIdealExtension_spanSingleton (K : PositiveDefiniteIntegralLattice 2)
    (p : ℕ) [Fact (Nat.Prime p)]
    (z : FractionRing (DiscriminantOrder K.binaryPrimitiveDiscriminant)) :
    letI := K.binaryDiscriminantOrder_isDomain
    letI := padicOrderAlgebra p K.binaryPrimitiveDiscriminant
    K.binaryPadicIdealExtension p (FractionalIdeal.spanSingleton _ z)=
      Submodule.span _ {K.binaryPadicFractionMap p z} := by
  letI := K.binaryDiscriminantOrder_isDomain
  letI := padicOrderAlgebra p K.binaryPrimitiveDiscriminant
  exact FractionalIdeal.scalarSpanExtension_spanSingleton _ _ _ z

/-- Every actual normalized ideal has the explicit local generator in the
genuine quadratic Q_p algebra, including split and dyadic cases. -/
theorem binaryPadicIdealExtension_principal (K L : PositiveDefiniteIntegralLattice 2)
    (hD : L.binaryPrimitiveDiscriminant=K.binaryPrimitiveDiscriminant)
    (p : ℕ) [Fact (Nat.Prime p)] (v : Fin 2 → ℤ_[p]) (u : ℤ_[p]ˣ)
    (hv : L.binaryPrimitivePolynomialOver ℤ_[p] v=(u : ℤ_[p])) :
    letI := K.binaryDiscriminantOrder_isDomain
    letI := padicOrderAlgebra p K.binaryPrimitiveDiscriminant
    K.binaryPadicIdealExtension p
      (L.binaryFractionalNormIdealUnitAt K.binaryPrimitiveDiscriminant hD : K.BinaryDiscriminantFractionalIdeals)=
      Submodule.span _ {padicOrderMap p K.binaryPrimitiveDiscriminant
        (L.binaryLocalIdealGeneratorAt K.binaryPrimitiveDiscriminant hD ℤ_[p] v)} := by
  letI := K.binaryDiscriminantOrder_isDomain
  letI := padicOrderAlgebra p K.binaryPrimitiveDiscriminant
  rw [binaryFractionalNormIdealUnitAt_val]
  change FractionalIdeal.scalarSpanExtension _ _ _ _=_
  rw [FractionalIdeal.scalarSpanExtension_coeIdeal,
    L.map_binaryDiscriminantNormIdealAt_principal _ hD ℤ_[p] v u hv,
    Submodule.span_image_ideal_span,Set.image_singleton]
  rfl

/-- The generator becomes a unit in the quadratic Q_p algebra even when
its leading coefficient is not a unit in Z_p. -/
lemma isUnit_binaryPadicIdealGenerator (K L : PositiveDefiniteIntegralLattice 2)
    (hD : L.binaryPrimitiveDiscriminant=K.binaryPrimitiveDiscriminant)
    (p : ℕ) [Fact (Nat.Prime p)] (v : Fin 2 → ℤ_[p]) (u : ℤ_[p]ˣ)
    (hv : L.binaryPrimitivePolynomialOver ℤ_[p] v=(u : ℤ_[p])) :
    IsUnit (padicOrderMap p K.binaryPrimitiveDiscriminant
      (L.binaryLocalIdealGeneratorAt K.binaryPrimitiveDiscriminant hD ℤ_[p] v)) := by
  apply QuadraticAlgebra.isUnit_iff_norm_isUnit.mpr
  rw [padicOrderMap,norm_coefficientScalarMap,norm_binaryLocalIdealGeneratorAt,hv,map_mul]
  apply isUnit_iff_ne_zero.mpr
  apply mul_ne_zero
  · have hn : ((L.pairingMatrix 0 0/(L.binaryContent : ℤ) : ℤ) : ℚ_[p]) ≠ 0 := by
      exact_mod_cast ne_of_gt L.binaryPrimitivePolynomial_leading_pos
    simpa using hn
  · exact fun h => u.ne_zero (PadicInt.ext h)

/-- The explicit local principal generator as an ambient algebra unit. -/
noncomputable def binaryPadicIdealGeneratorUnit (K L : PositiveDefiniteIntegralLattice 2)
    (hD : L.binaryPrimitiveDiscriminant=K.binaryPrimitiveDiscriminant)
    (p : ℕ) [Fact (Nat.Prime p)] (v : Fin 2 → ℤ_[p]) (u : ℤ_[p]ˣ)
    (hv : L.binaryPrimitivePolynomialOver ℤ_[p] v=(u : ℤ_[p])) :
    (DiscriminantAlgebra ℚ_[p] K.binaryPrimitiveDiscriminant)ˣ :=
  (isUnit_binaryPadicIdealGenerator K L hD p v u hv).unit

lemma binaryPadicIdealGeneratorUnit_val (K L : PositiveDefiniteIntegralLattice 2)
    (hD : L.binaryPrimitiveDiscriminant=K.binaryPrimitiveDiscriminant)
    (p : ℕ) [Fact (Nat.Prime p)] (v : Fin 2 → ℤ_[p]) (u : ℤ_[p]ˣ)
    (hv : L.binaryPrimitivePolynomialOver ℤ_[p] v=(u : ℤ_[p])) :
    (binaryPadicIdealGeneratorUnit K L hD p v u hv : DiscriminantAlgebra ℚ_[p] K.binaryPrimitiveDiscriminant)=
      padicOrderMap p K.binaryPrimitiveDiscriminant
        (L.binaryLocalIdealGeneratorAt K.binaryPrimitiveDiscriminant hD ℤ_[p] v) :=
  (isUnit_binaryPadicIdealGenerator K L hD p v u hv).unit_spec

/-- Principal scaling of the original fractional ideals gives an actual
local-order unit relating their explicit generators. -/
theorem exists_binaryLocalIdealProduct_unit (K L M : PositiveDefiniteIntegralLattice 2)
    (hL : L.binaryPrimitiveDiscriminant=K.binaryPrimitiveDiscriminant)
    (hM : M.binaryPrimitiveDiscriminant=K.binaryPrimitiveDiscriminant)
    (gamma : (FractionRing (DiscriminantOrder K.binaryPrimitiveDiscriminant))ˣ)
    (hprod : letI := K.binaryDiscriminantOrder_isDomain
      (binaryFractionalNormIdealUnitAt K K.binaryPrimitiveDiscriminant rfl : K.BinaryDiscriminantFractionalIdeals)*
        (binaryFractionalNormIdealUnitAt L K.binaryPrimitiveDiscriminant hL : K.BinaryDiscriminantFractionalIdeals)=
      FractionalIdeal.spanSingleton (DiscriminantOrder K.binaryPrimitiveDiscriminant)⁰ gamma.val*
        (binaryFractionalNormIdealUnitAt M K.binaryPrimitiveDiscriminant hM : K.BinaryDiscriminantFractionalIdeals))
    (p : ℕ) [Fact (Nat.Prime p)]
    (v1 v2 v3 : Fin 2 → ℤ_[p]) (u1 u2 u3 : ℤ_[p]ˣ)
    (hv1 : K.binaryPrimitivePolynomialOver ℤ_[p] v1=(u1 : ℤ_[p]))
    (hv2 : L.binaryPrimitivePolynomialOver ℤ_[p] v2=(u2 : ℤ_[p]))
    (hv3 : M.binaryPrimitivePolynomialOver ℤ_[p] v3=(u3 : ℤ_[p])) :
    ∃ e : (DiscriminantAlgebra ℤ_[p] K.binaryPrimitiveDiscriminant)ˣ,
      padicOrderMap p K.binaryPrimitiveDiscriminant e.val*
        (K.binaryPadicFractionMap p gamma.val*
          padicOrderMap p K.binaryPrimitiveDiscriminant
            (M.binaryLocalIdealGeneratorAt K.binaryPrimitiveDiscriminant hM ℤ_[p] v3))=
      padicOrderMap p K.binaryPrimitiveDiscriminant
          (K.binaryLocalIdealGeneratorAt K.binaryPrimitiveDiscriminant rfl ℤ_[p] v1)*
        padicOrderMap p K.binaryPrimitiveDiscriminant
          (L.binaryLocalIdealGeneratorAt K.binaryPrimitiveDiscriminant hL ℤ_[p] v2) := by
  letI := K.binaryDiscriminantOrder_isDomain
  letI := padicOrderAlgebra p K.binaryPrimitiveDiscriminant
  have hh := congrArg (K.binaryPadicIdealExtension p) hprod
  rw [map_mul,map_mul,binaryPadicIdealExtension_spanSingleton,
    K.binaryPadicIdealExtension_principal K rfl p v1 u1 hv1,
    K.binaryPadicIdealExtension_principal L hL p v2 u2 hv2,
    K.binaryPadicIdealExtension_principal M hM p v3 u3 hv3] at hh
  have hs (x y : DiscriminantAlgebra ℚ_[p] K.binaryPrimitiveDiscriminant) :
      Submodule.span (DiscriminantAlgebra ℤ_[p] K.binaryPrimitiveDiscriminant) {x}*
        Submodule.span _ {y}=Submodule.span _ {x*y} := by
    rw [Submodule.span_mul_span]
    simp
  rw [hs,hs] at hh
  obtain ⟨e,he⟩ := Submodule.exists_scalar_unit_of_span_eq (S := DiscriminantAlgebra ℤ_[p] K.binaryPrimitiveDiscriminant)
    (padicOrderMap_injective p K.binaryPrimitiveDiscriminant)
    (binaryPadicIdealGeneratorUnit K K rfl p v1 u1 hv1*binaryPadicIdealGeneratorUnit K L hL p v2 u2 hv2)
    (Units.map (K.binaryPadicFractionMap p) gamma*binaryPadicIdealGeneratorUnit K M hM p v3 u3 hv3)
    (by simpa only [Units.val_mul,Units.coe_map,binaryPadicIdealGeneratorUnit_val] using hh)
  exact ⟨e,by simpa only [Units.val_mul,Units.coe_map,binaryPadicIdealGeneratorUnit_val] using he⟩

/-- The canonical class product preserves the actual local unit-norm
invariant, for any chosen represented units. This includes split algebras,
p=2, nonmaximal orders and arbitrary original contents. -/
theorem exists_binaryLocalNormProduct_unit (K L M : PositiveDefiniteIntegralLattice 2)
    (hL : L.binaryPrimitiveDiscriminant=K.binaryPrimitiveDiscriminant)
    (hM : M.binaryPrimitiveDiscriminant=K.binaryPrimitiveDiscriminant)
    (hclass : letI := K.binaryDiscriminantOrder_isDomain
      binaryIdealClassAt K K.binaryPrimitiveDiscriminant rfl*
        binaryIdealClassAt L K.binaryPrimitiveDiscriminant hL=
      binaryIdealClassAt M K.binaryPrimitiveDiscriminant hM)
    (p : ℕ) [Fact (Nat.Prime p)]
    (v1 v2 v3 : Fin 2 → ℤ_[p]) (u1 u2 u3 : ℤ_[p]ˣ)
    (hv1 : K.binaryPrimitivePolynomialOver ℤ_[p] v1=(u1 : ℤ_[p]))
    (hv2 : L.binaryPrimitivePolynomialOver ℤ_[p] v2=(u2 : ℤ_[p]))
    (hv3 : M.binaryPrimitivePolynomialOver ℤ_[p] v3=(u3 : ℤ_[p])) :
    ∃ e : (DiscriminantAlgebra ℤ_[p] K.binaryPrimitiveDiscriminant)ˣ,
      (u1 : ℤ_[p])*(u2 : ℤ_[p])=(u3 : ℤ_[p])*e.val.norm := by
  letI := K.binaryDiscriminantOrder_isDomain
  obtain ⟨gamma,hprod,hscale⟩ := K.exists_binaryIdealProduct_scaling_of_class_mul L M hL hM hclass
  obtain ⟨e,he⟩ := K.exists_binaryLocalIdealProduct_unit L M hL hM gamma hprod p
    v1 v2 v3 u1 u2 u3 hv1 hv2 hv3
  refine ⟨e,?_⟩
  have hn := congrArg QuadraticAlgebra.norm he
  simp only [map_mul,padicOrderMap,norm_coefficientScalarMap,
    norm_binaryLocalIdealGeneratorAt,hv1,hv2,hv3,
    binaryPadicFractionMap,norm_fractionScalarMap] at hn
  have hs : (K.binaryFractionNorm gamma.val : ℚ_[p])*
      ((M.pairingMatrix 0 0/(M.binaryContent : ℤ) : ℤ) : ℚ_[p])=
      ((K.pairingMatrix 0 0/(K.binaryContent : ℤ) : ℤ) : ℚ_[p])*
        ((L.pairingMatrix 0 0/(L.binaryContent : ℤ) : ℤ) : ℚ_[p]) := by
    exact_mod_cast hscale
  dsimp only [binaryFractionNorm] at hs
  have hK : ((K.pairingMatrix 0 0/(K.binaryContent : ℤ) : ℤ) : ℚ_[p]) ≠ 0 := by
    exact_mod_cast ne_of_gt K.binaryPrimitivePolynomial_leading_pos
  have hL' : ((L.pairingMatrix 0 0/(L.binaryContent : ℤ) : ℤ) : ℚ_[p]) ≠ 0 := by
    exact_mod_cast ne_of_gt L.binaryPrimitivePolynomial_leading_pos
  apply PadicInt.ext
  simp only [map_intCast,PadicInt.algebraMap_apply] at hn
  have hh : (((K.pairingMatrix 0 0/(K.binaryContent : ℤ) : ℤ) : ℚ_[p])*
      ((L.pairingMatrix 0 0/(L.binaryContent : ℤ) : ℤ) : ℚ_[p]))*
      (((u1 : ℤ_[p]) : ℚ_[p])*((u2 : ℤ_[p]) : ℚ_[p])-
        ((u3 : ℤ_[p]) : ℚ_[p])*(e.val.norm : ℚ_[p]))=0 := by
    linear_combination -hn + ((u3 : ℤ_[p]) : ℚ_[p])*(e.val.norm : ℚ_[p])*hs
  exact sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left (mul_ne_zero hK hL'))

end PositiveDefiniteIntegralLattice

#assert_standard_axioms Submodule.ringSpanExtension
#assert_standard_axioms Submodule.ringSpanExtension_span
#assert_standard_axioms Submodule.ringSpanExtension_mul
#assert_standard_axioms Submodule.ringSpanExtension_one
#assert_standard_axioms Submodule.ringSpanExtensionHom
#assert_standard_axioms Submodule.exists_scalar_unit_of_span_eq
#assert_standard_axioms Submodule.span_image_ideal_span
#assert_standard_axioms FractionalIdeal.scalarSpanExtension
#assert_standard_axioms FractionalIdeal.scalarSpanExtension_spanSingleton
#assert_standard_axioms FractionalIdeal.scalarSpanExtension_coeIdeal_span
#assert_standard_axioms FractionalIdeal.scalarSpanExtension_coeIdeal
#assert_standard_axioms BinaryNormIdeal.coefficientScalarMap
#assert_standard_axioms BinaryNormIdeal.norm_coefficientScalarMap
#assert_standard_axioms BinaryNormIdeal.coefficientScalarMap_injective
#assert_standard_axioms BinaryNormIdeal.orderScalarMap
#assert_standard_axioms BinaryNormIdeal.fractionScalarMap
#assert_standard_axioms BinaryNormIdeal.fractionScalarMap_injective
#assert_standard_axioms BinaryNormIdeal.fractionScalarMap_algebraMap
#assert_standard_axioms BinaryNormIdeal.norm_fractionScalarMap
#assert_standard_axioms BinaryNormIdeal.padicOrderMap
#assert_standard_axioms BinaryNormIdeal.padicOrderMap_injective
#assert_standard_axioms BinaryNormIdeal.padicOrderAlgebra
#assert_standard_axioms BinaryNormIdeal.orderScalarMap_equiv
#assert_standard_axioms BinaryNormIdeal.map_normIdeal_principal
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryLocalIdealGeneratorAt
#assert_standard_axioms PositiveDefiniteIntegralLattice.norm_binaryLocalIdealGeneratorAt
#assert_standard_axioms PositiveDefiniteIntegralLattice.map_binaryDiscriminantNormIdealAt_principal
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryPadicFractionMap
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryPadicFractionMap_compatible
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryPadicIdealExtension
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryPadicIdealExtension_spanSingleton
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryPadicIdealExtension_principal
#assert_standard_axioms PositiveDefiniteIntegralLattice.isUnit_binaryPadicIdealGenerator
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryPadicIdealGeneratorUnit
#assert_standard_axioms PositiveDefiniteIntegralLattice.binaryPadicIdealGeneratorUnit_val
#assert_standard_axioms PositiveDefiniteIntegralLattice.exists_binaryLocalIdealProduct_unit
#assert_standard_axioms PositiveDefiniteIntegralLattice.exists_binaryLocalNormProduct_unit
