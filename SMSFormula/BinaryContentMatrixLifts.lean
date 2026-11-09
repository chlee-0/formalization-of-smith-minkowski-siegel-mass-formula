import SMSFormula.BinaryNormPolynomialMatrices

/-!
# Original-content lifts of raw binary polynomial matrices

Reduction of all four matrix entries gives the exact content factor.
The carriers have the original polynomial condition, without a GL2 filter.
-/

noncomputable section

namespace BinaryNormIdeal

/-- Reduction from depth k+h to k on the literal scalar residue rings. -/
def contentReduction (p k h : ℕ) : ZMod (p^(k+h)) →+* ZMod (p^k) :=
  ZMod.castHom (pow_dvd_pow p (Nat.le_add_right k h)) _

/-- Multiplication by the original nonzero content removes exactly its
valuation from the scalar congruence depth. Depth zero remains allowed. -/
theorem content_mul_eq_zero_iff (p : ℕ) [Fact p.Prime] (k g : ℕ) (hg : g≠0)
    (z : ZMod (p^(k+padicValNat p g))) :
    (g : ZMod (p^(k+padicValNat p g)))*z=0 ↔
      contentReduction p k (padicValNat p g) z=0 := by
  have hp : p≠0 := (Fact.out : p.Prime).ne_zero
  letI : NeZero (p^(k+padicValNat p g)) := ⟨pow_ne_zero _ hp⟩
  rw [← ZMod.natCast_zmod_val z]
  simp only [contentReduction,map_natCast,← Nat.cast_mul,ZMod.natCast_eq_zero_iff]
  by_cases hz : z.val=0
  · simp [hz]
  · rw [padicValNat_dvd_iff_le (mul_ne_zero hg hz),padicValNat_dvd_iff_le hz,
      padicValNat.mul hg hz]
    omega

/-- The corresponding exact equality criterion for scalar residues. -/
theorem content_mul_eq_iff (p : ℕ) [Fact p.Prime] (k g : ℕ) (hg : g≠0)
    (x y : ZMod (p^(k+padicValNat p g))) :
    (g : ZMod (p^(k+padicValNat p g)))*x=g*y ↔
      contentReduction p k (padicValNat p g) x=
        contentReduction p k (padicValNat p g) y := by
  rw [← sub_eq_zero,← mul_sub,content_mul_eq_zero_iff p k g hg,map_sub,sub_eq_zero]

/-- All entrywise matrix reductions form an additive homomorphism. -/
def contentMatrixReduction (p k h : ℕ) :
    Matrix (Fin 2) (Fin 2) (ZMod (p^(k+h))) →+
      Matrix (Fin 2) (Fin 2) (ZMod (p^k)) :=
  (contentReduction p k h).toAddMonoidHom.mapMatrix

/-- Every matrix has a lift; invertibility is not required. -/
theorem contentMatrixReduction_surjective (p k h : ℕ) :
    Function.Surjective (contentMatrixReduction p k h) := by
  intro U
  choose V hV using fun i j => ZMod.castHom_surjective
    (pow_dvd_pow p (Nat.le_add_right k h)) (U i j)
  exact ⟨V,by ext i j; exact hV i j⟩

/-- A section of an additive reduction splits each inverse image as the
specified target carrier times the actual additive kernel. -/
def additivePreimageEquiv {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (f : A →+ B) (hf : Function.Surjective f) (S : Set B) :
    {x : A // f x∈S} ≃ S × f.ker := by
  choose s hs using hf
  exact {
    toFun := fun x => (⟨f x.val,x.prop⟩,⟨x.val-s (f x.val),by
      change f (x.val-s (f x.val))=0
      rw [map_sub,hs,sub_self]⟩)
    invFun := fun y => ⟨s y.1.val+y.2.val,by
      have hy : f y.2.val=0 := y.2.prop
      simpa only [map_add,hs,hy,add_zero] using y.1.prop⟩
    left_inv := fun x => by apply Subtype.ext; dsimp; abel
    right_inv := fun y => by
      apply Prod.ext
      · apply Subtype.ext
        change f (s y.1.val+y.2.val)=y.1.val
        rw [map_add,hs,y.2.prop,add_zero]
      · apply Subtype.ext
        change s y.1.val+y.2.val-s (f (s y.1.val+y.2.val))=y.2.val
        rw [map_add,hs,y.2.prop,add_zero]
        abel }

/-- The exact four-coordinate reduction kernel has p^(4*h) elements. -/
theorem card_contentMatrixReduction_kernel (p : ℕ) [Fact p.Prime] (k h : ℕ) :
    Nat.card (contentMatrixReduction p k h).ker=p^(4*h) := by
  have hp : p≠0 := (Fact.out : p.Prime).ne_zero
  letI : NeZero (p^(k+h)) := ⟨pow_ne_zero _ hp⟩
  letI : NeZero (p^k) := ⟨pow_ne_zero _ hp⟩
  let f := contentMatrixReduction p k h
  have hc := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup f.ker
  rw [Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective f
    (contentMatrixReduction_surjective p k h)).toEquiv] at hc
  have hbig : Nat.card (Matrix (Fin 2) (Fin 2) (ZMod (p^(k+h))))=p^(4*(k+h)) := by
    simp [Matrix,← pow_mul]
    congr 1
    ring
  have hsmall : Nat.card (Matrix (Fin 2) (Fin 2) (ZMod (p^k)))=p^(4*k) := by
    simp [Matrix,← pow_mul]
    congr 1
    ring
  rw [hbig,hsmall,Nat.mul_add,pow_add] at hc
  exact (mul_left_cancel₀ (pow_ne_zero _ hp) hc).symm

/-- Polynomial evaluation commutes with every scalar ring map. -/
theorem map_binaryPolynomial {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (a b c : R) (x : Fin 2 → R) :
    f (polynomialOver a b c x)=polynomialOver (f a) (f b) (f c) (fun i=>f (x i)) := by
  simp only [polynomialOver,map_add,map_mul,map_pow]

/-- Matrix action commutes with scalar reduction on the same coordinates. -/
theorem map_binaryMulVec {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (U : Matrix (Fin 2) (Fin 2) R) (x : Fin 2 → R) :
    (fun i=>f (U.mulVec x i))=(U.map f).mulVec (fun i=>f (x i)) := by
  ext i
  simp only [Matrix.mulVec,dotProduct,Fin.sum_univ_two,map_add,map_mul,Matrix.map_apply]

/-- The original gQ condition is exactly the primitive condition on the
reduced matrix. The universal polynomial condition retains every matrix. -/
theorem raw_contentPolynomial_iff (p : ℕ) [Fact p.Prime] (k g : ℕ) (hg : g≠0)
    (a b c : ℤ) (U : Matrix (Fin 2) (Fin 2) (ZMod (p^(k+padicValNat p g)))) :
    (∀ x, (g : ZMod (p^(k+padicValNat p g)))*
        polynomialOver (a : ZMod _) (b : ZMod _) (c : ZMod _) (U.mulVec x)=
      g*polynomialOver (a : ZMod _) (b : ZMod _) (c : ZMod _) x) ↔
    ∀ y, polynomialOver (a : ZMod (p^k)) (b : ZMod _) (c : ZMod _)
        ((contentMatrixReduction p k (padicValNat p g) U).mulVec y)=
      polynomialOver (a : ZMod _) (b : ZMod _) (c : ZMod _) y := by
  let f := contentReduction p k (padicValNat p g)
  have he (x : Fin 2 → ZMod (p^(k+padicValNat p g))) :
      (g : ZMod (p^(k+padicValNat p g)))*polynomialOver (a : ZMod _) (b : ZMod _)
        (c : ZMod _) (U.mulVec x)=g*polynomialOver (a : ZMod _) (b : ZMod _) (c : ZMod _) x ↔
      polynomialOver (a : ZMod (p^k)) (b : ZMod _) (c : ZMod _)
        ((contentMatrixReduction p k (padicValNat p g) U).mulVec (fun i=>f (x i)))=
      polynomialOver (a : ZMod _) (b : ZMod _) (c : ZMod _) (fun i=>f (x i)) := by
    rw [content_mul_eq_iff p k g hg,map_binaryPolynomial,map_binaryPolynomial,map_binaryMulVec]
    simp only [map_intCast]
    rfl
  constructor
  · intro hu y
    choose x hx using fun i => ZMod.castHom_surjective
      (pow_dvd_pow p (Nat.le_add_right k (padicValNat p g))) (y i)
    have hh := (he x).mp (hu x)
    simpa only [f,contentReduction,hx] using hh
  · intro hu x
    exact (he x).mpr (hu _)

/-- Exact original-content lift cardinal, including primitive depth zero. -/
theorem card_rawContentPolynomialMatrices (p : ℕ) [Fact p.Prime] (k g : ℕ)
    (hg : g≠0) (a b c : ℤ) :
    Nat.card (RawPolynomialIsometries (fun x : Fin 2 → ZMod (p^(k+padicValNat p g)) =>
      (g : ZMod _)*polynomialOver (a : ZMod _) (b : ZMod _) (c : ZMod _) x))=
      p^(4*padicValNat p g)*Nat.card (RawPolynomialIsometries
        (polynomialOver (a : ZMod (p^k)) (b : ZMod _) (c : ZMod _))) := by
  let S : Set (Matrix (Fin 2) (Fin 2) (ZMod (p^k))) :=
    {V | ∀ y, polynomialOver (a : ZMod (p^k)) (b : ZMod _) (c : ZMod _) (V.mulVec y)=
      polynomialOver (a : ZMod _) (b : ZMod _) (c : ZMod _) y}
  let e : RawPolynomialIsometries (fun x : Fin 2 → ZMod (p^(k+padicValNat p g)) =>
      (g : ZMod _)*polynomialOver (a : ZMod _) (b : ZMod _) (c : ZMod _) x) ≃
      {U // contentMatrixReduction p k (padicValNat p g) U∈S} :=
    Equiv.subtypeEquivRight (fun U => raw_contentPolynomial_iff p k g hg a b c U)
  rw [Nat.card_congr e,Nat.card_congr (additivePreimageEquiv _
    (contentMatrixReduction_surjective p k (padicValNat p g)) S),Nat.card_prod,
    card_contentMatrixReduction_kernel,mul_comm]
  rfl

end BinaryNormIdeal

namespace PositiveDefiniteIntegralLattice

open BinaryNormIdeal

/-- The actual original integral norm has the exact four-entry content
lift factor. This is a polynomial count, before the original F-dual quotient. -/
theorem card_rawBinaryOriginalMatrices_content (K : PositiveDefiniteIntegralLattice 2)
    (p : ℕ) [Fact p.Prime] (k : ℕ) :
    Nat.card (RawPolynomialIsometries
      (fun x : Fin 2 → ZMod (p^(k+padicValNat p K.binaryContent)) =>
        dotProduct x ((K.pairingMatrix.map (Int.cast : ℤ → ZMod _)).mulVec x)))=
      p^(4*padicValNat p K.binaryContent)*Nat.card (RawPolynomialIsometries
        (K.binaryPrimitivePolynomialOver (ZMod (p^k)))) := by
  let R := ZMod (p^(k+padicValNat p K.binaryContent))
  have he :
      (fun x : Fin 2 → R => dotProduct x ((K.pairingMatrix.map (Int.cast : ℤ → R)).mulVec x))=
      (fun x => (K.binaryContent : R)*polynomialOver
        ((K.pairingMatrix 0 0/(K.binaryContent : ℤ) : ℤ) : R)
        (((2*K.pairingMatrix 0 1)/(K.binaryContent : ℤ) : ℤ) : R)
        ((K.pairingMatrix 1 1/(K.binaryContent : ℤ) : ℤ) : R) x) := by
    funext x
    rw [K.binary_norm_eq_content_mul_primitive_over,K.binaryPrimitivePolynomialOver_apply]
    rfl
  rw [he,card_rawContentPolynomialMatrices p k K.binaryContent
    (ne_of_gt K.binaryContent_pos)]
  have hq : polynomialOver
      ((K.pairingMatrix 0 0/(K.binaryContent : ℤ) : ℤ) : ZMod (p^k))
      (((2*K.pairingMatrix 0 1)/(K.binaryContent : ℤ) : ℤ) : ZMod (p^k))
      ((K.pairingMatrix 1 1/(K.binaryContent : ℤ) : ℤ) : ZMod (p^k))=
      (K.binaryPrimitivePolynomialOver (ZMod (p^k)) : (Fin 2 → ZMod (p^k)) → ZMod (p^k)) := by
    funext x
    rw [K.binaryPrimitivePolynomialOver_apply]
    rfl
  rw [hq]

/-- The same exact count at a specified original depth j, with primitive
reduction depth j-h. No additional stable-depth premise enters this lift. -/
theorem card_rawBinaryOriginalMatrices_of_depth (K : PositiveDefiniteIntegralLattice 2)
    (p : ℕ) [Fact p.Prime] (j : ℕ) (hj : padicValNat p K.binaryContent≤j) :
    Nat.card (RawPolynomialIsometries
      (fun x : Fin 2 → ZMod (p^j) =>
        dotProduct x ((K.pairingMatrix.map (Int.cast : ℤ → ZMod _)).mulVec x)))=
      p^(4*padicValNat p K.binaryContent)*Nat.card (RawPolynomialIsometries
        (K.binaryPrimitivePolynomialOver (ZMod (p^(j-padicValNat p K.binaryContent))))) := by
  have hh := K.card_rawBinaryOriginalMatrices_content p (j-padicValNat p K.binaryContent)
  have hj' : j-padicValNat p K.binaryContent+padicValNat p K.binaryContent=j :=
    Nat.sub_add_cancel hj
  rw [hj'] at hh
  exact hh

/-- Evaluated raw original polynomial matrix count. The field, conductor
and local norm index belong to the same original lattice. -/
theorem card_rawBinaryOriginalMatrices_prime_power (K : PositiveDefiniteIntegralLattice 2)
    (p : ℕ) [Fact p.Prime] (k : ℕ)
    (hk : padicValNat p K.binaryPrimitiveDiscriminant.natAbs<k) (hk2 : p=2 → 3≤k) :
    letI := K.binaryDiscriminantOrder_isDomain
    letI := K.binaryFractionNumberField
    (Nat.card (RawPolynomialIsometries
      (fun x : Fin 2 → ZMod (p^(k+padicValNat p K.binaryContent)) =>
        dotProduct x ((K.pairingMatrix.map (Int.cast : ℤ → ZMod _)).mulVec x))) : ℚ)=
      2*(Nat.card (OrderUnitNormQuotient ℤ_[p] K.binaryPrimitiveDiscriminant) : ℚ)*
        (p : ℚ)^(k+4*padicValNat p K.binaryContent+padicValNat p K.binaryPrimitiveDiscriminant.natAbs)*
        (if p ∣ K.binaryOrderIndex then 1 else 1-
          (conductorPrimeSign (NumberField.discr
            (FractionRing (DiscriminantOrder K.binaryPrimitiveDiscriminant))) p : ℚ)/(p : ℚ)) := by
  letI := K.binaryDiscriminantOrder_isDomain
  letI := K.binaryFractionNumberField
  rw [K.card_rawBinaryOriginalMatrices_content,Nat.cast_mul,
    K.card_rawBinaryPrimitiveMatrices_prime_power p k hk hk2,Nat.cast_pow]
  rw [show k+4*padicValNat p K.binaryContent+padicValNat p K.binaryPrimitiveDiscriminant.natAbs=
    4*padicValNat p K.binaryContent+(k+padicValNat p K.binaryPrimitiveDiscriminant.natAbs) by omega,
    pow_add]
  ring

end PositiveDefiniteIntegralLattice

#assert_standard_axioms BinaryNormIdeal.contentReduction
#assert_standard_axioms BinaryNormIdeal.content_mul_eq_zero_iff
#assert_standard_axioms BinaryNormIdeal.content_mul_eq_iff
#assert_standard_axioms BinaryNormIdeal.contentMatrixReduction
#assert_standard_axioms BinaryNormIdeal.contentMatrixReduction_surjective
#assert_standard_axioms BinaryNormIdeal.additivePreimageEquiv
#assert_standard_axioms BinaryNormIdeal.card_contentMatrixReduction_kernel
#assert_standard_axioms BinaryNormIdeal.map_binaryPolynomial
#assert_standard_axioms BinaryNormIdeal.map_binaryMulVec
#assert_standard_axioms BinaryNormIdeal.raw_contentPolynomial_iff
#assert_standard_axioms BinaryNormIdeal.card_rawContentPolynomialMatrices
#assert_standard_axioms PositiveDefiniteIntegralLattice.card_rawBinaryOriginalMatrices_content
#assert_standard_axioms PositiveDefiniteIntegralLattice.card_rawBinaryOriginalMatrices_of_depth
#assert_standard_axioms PositiveDefiniteIntegralLattice.card_rawBinaryOriginalMatrices_prime_power
