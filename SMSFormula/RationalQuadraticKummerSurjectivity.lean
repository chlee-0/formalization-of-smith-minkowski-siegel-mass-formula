import SMSFormula.RationalQuadraticKummer

/-!
# Surjectivity of the continuous quadratic Kummer map

This module proves the reverse direction of the quadratic Kummer
comparison constructed in `RationalQuadraticKummer.lean`. For a continuous
character `chi : G_K -> ZMod 2`, its kernel is a closed normal subgroup of the
absolute Galois group. If `chi` is nontrivial, infinite Galois correspondence
provides an element `x` of the kernel's fixed field and an automorphism `tau`
outside the kernel with `tau x != x`.

The anti-invariant element

```text
y = x - tau x
```

is nonzero, and every absolute Galois automorphism fixes or negates it
according to its `chi`-value. Thus `y^2` is fixed by the whole absolute Galois
group and lies in the base field. The square class of `y^2` recovers `chi`.

No classification of quadratic extensions, primitive-element theorem, or
finite-dimensional reduction is needed. For every characteristic-zero field
this yields the continuous quadratic Kummer equivalence

```text
K^x / K^(x2) ~= Hom_cont(G_K, Z/2).
```

This file does not construct restriction maps between independently chosen
algebraic closures of different fields, so global/local compatibility is not
treated here.
-/

noncomputable section

namespace RationalTamagawa

variable (K : Type) [Field K]

/-- Regard a continuous additive order-two character as a multiplicative
homomorphism on the untagged absolute Galois group. -/
def muTwoContinuousCharacterMulHom (χ : MuTwoContinuousH1 K) :
    Field.absoluteGaloisGroup K →* Multiplicative (ZMod 2) where
  toFun σ := Multiplicative.ofAdd (χ (Additive.ofMul σ))
  map_one' := congrArg Multiplicative.ofAdd χ.map_zero
  map_mul' σ τ := congrArg Multiplicative.ofAdd (χ.map_add
    (Additive.ofMul σ) (Additive.ofMul τ))

theorem muTwoContinuousCharacterMulHom_ker_isClosed (χ : MuTwoContinuousH1 K) :
    IsClosed ((muTwoContinuousCharacterMulHom K χ).ker :
      Set (Field.absoluteGaloisGroup K)) := by
  have hclosed : IsClosed {σ : Additive (Field.absoluteGaloisGroup K) | χ σ = 0} :=
    isClosed_singleton.preimage χ.continuous_toFun
  change IsClosed {σ : Field.absoluteGaloisGroup K |
    χ (Additive.ofMul σ) = 0}
  exact hclosed

/-- The closed kernel used by infinite Galois correspondence. -/
def muTwoContinuousCharacterKernel (χ : MuTwoContinuousH1 K) :
    ClosedSubgroup (Field.absoluteGaloisGroup K) :=
  ⟨(muTwoContinuousCharacterMulHom K χ).ker,
    muTwoContinuousCharacterMulHom_ker_isClosed K χ⟩

instance muTwoContinuousCharacterKernel_normal (χ : MuTwoContinuousH1 K) :
    (muTwoContinuousCharacterKernel K χ).Normal := by
  change (muTwoContinuousCharacterMulHom K χ).ker.Normal
  exact MonoidHom.normal_ker _

@[simp]
theorem mem_muTwoContinuousCharacterKernel_iff
    (χ : MuTwoContinuousH1 K) (σ : Field.absoluteGaloisGroup K) :
    σ ∈ muTwoContinuousCharacterKernel K χ ↔ χ (Additive.ofMul σ) = 0 := by
  rfl

theorem zmod_two_eq_one_of_ne_zero (z : ZMod 2) (hz : z ≠ 0) : z = 1 := by
  have hv := ZMod.val_lt z
  have hv0 : z.val ≠ 0 := fun hval => hz ((ZMod.val_eq_zero _).mp hval)
  have hval : z.val = 1 := by omega
  apply ZMod.val_injective
  simpa using hval

theorem exists_eq_one_of_ne_zero (χ : MuTwoContinuousH1 K) (hχ : χ ≠ 0) :
    ∃ σ : Field.absoluteGaloisGroup K, χ (Additive.ofMul σ) = 1 := by
  have hex : ∃ σ : Additive (Field.absoluteGaloisGroup K), χ σ ≠ 0 := by
    by_contra h
    push_neg at h
    apply hχ
    ext σ
    exact h σ
  obtain ⟨σ, hσ⟩ := hex
  exact ⟨σ.toMul, zmod_two_eq_one_of_ne_zero (χ σ) hσ⟩

section CharZero

variable [CharZero K]

/-- A nontrivial character supplies an automorphism outside its kernel and an
element of the kernel's fixed field moved by that automorphism. -/
theorem exists_fixedField_element_not_fixed
    (χ : MuTwoContinuousH1 K) (hχ : χ ≠ 0) :
    ∃ (τ : Field.absoluteGaloisGroup K) (x : AlgebraicClosure K),
      χ (Additive.ofMul τ) = 1 ∧
      x ∈ IntermediateField.fixedField
        (muTwoContinuousCharacterKernel K χ).toSubgroup ∧
      absoluteGaloisAlgEquiv K τ x ≠ x := by
  obtain ⟨τ, hτ⟩ := exists_eq_one_of_ne_zero K χ hχ
  have hτker : τ ∉ muTwoContinuousCharacterKernel K χ := by
    rw [mem_muTwoContinuousCharacterKernel_iff]
    simp [hτ]
  have hτfix : τ ∉ (IntermediateField.fixedField
      (muTwoContinuousCharacterKernel K χ).toSubgroup).fixingSubgroup := by
    rw [InfiniteGalois.fixingSubgroup_fixedField]
    exact hτker
  change absoluteGaloisAlgEquiv K τ ∉ (IntermediateField.fixedField
    (muTwoContinuousCharacterKernel K χ).toSubgroup).fixingSubgroup at hτfix
  rw [IntermediateField.mem_fixingSubgroup_iff] at hτfix
  push_neg at hτfix
  obtain ⟨x, hx, hτx⟩ := hτfix
  exact ⟨τ, x, hτ, hx, hτx⟩

omit [CharZero K] in
theorem fixedField_apply_eq_of_character_eq_zero
    (χ : MuTwoContinuousH1 K) (x : AlgebraicClosure K)
    (hx : x ∈ IntermediateField.fixedField
      (muTwoContinuousCharacterKernel K χ).toSubgroup)
    (σ : Field.absoluteGaloisGroup K)
    (hσ : χ (Additive.ofMul σ) = 0) :
    absoluteGaloisAlgEquiv K σ x = x := by
  rw [IntermediateField.mem_fixedField_iff] at hx
  exact hx σ ((mem_muTwoContinuousCharacterKernel_iff K χ σ).mpr hσ)

omit [CharZero K] in
/-- Two automorphisms with the same character value act identically on the
fixed field of the character kernel. -/
theorem fixedField_apply_eq_of_character_eq
    (χ : MuTwoContinuousH1 K) (x : AlgebraicClosure K)
    (hx : x ∈ IntermediateField.fixedField
      (muTwoContinuousCharacterKernel K χ).toSubgroup)
    (σ τ : Field.absoluteGaloisGroup K)
    (hστ : χ (Additive.ofMul σ) = χ (Additive.ofMul τ)) :
    absoluteGaloisAlgEquiv K σ x = absoluteGaloisAlgEquiv K τ x := by
  have hker : χ (Additive.ofMul (τ⁻¹ * σ)) = 0 := by
    change χ (-Additive.ofMul τ + Additive.ofMul σ) = 0
    rw [map_add, map_neg, hστ]
    have hz : χ (Additive.ofMul τ) + χ (Additive.ofMul τ) = 0 := by
      change (χ + χ) (Additive.ofMul τ) = 0
      rw [muTwoContinuousH1_add_self]
      rfl
    simpa using hz
  have hfix := fixedField_apply_eq_of_character_eq_zero K χ x hx (τ⁻¹ * σ) hker
  have happly := congrArg (fun z => absoluteGaloisAlgEquiv K τ z) hfix
  change absoluteGaloisAlgEquiv K τ
      (absoluteGaloisAlgEquiv K (τ⁻¹ * σ) x) =
    absoluteGaloisAlgEquiv K τ x at happly
  rw [← absoluteGaloisAlgEquiv_mul_apply] at happly
  have heq : τ * (τ⁻¹ * σ) = σ := by group
  rw [heq] at happly
  exact happly

omit [CharZero K] in
/-- The anti-invariant element is fixed or negated according to the character
value. -/
theorem antiInvariantElement_apply
    (χ : MuTwoContinuousH1 K)
    (τ : Field.absoluteGaloisGroup K) (x : AlgebraicClosure K)
    (hτ : χ (Additive.ofMul τ) = 1)
    (hx : x ∈ IntermediateField.fixedField
      (muTwoContinuousCharacterKernel K χ).toSubgroup)
    (σ : Field.absoluteGaloisGroup K) :
    absoluteGaloisAlgEquiv K σ (x - absoluteGaloisAlgEquiv K τ x) =
      if χ (Additive.ofMul σ) = 0 then
        x - absoluteGaloisAlgEquiv K τ x
      else -(x - absoluteGaloisAlgEquiv K τ x) := by
  by_cases hσ0 : χ (Additive.ofMul σ) = 0
  · rw [if_pos hσ0, map_sub]
    have hσx := fixedField_apply_eq_of_character_eq_zero K χ x hx σ hσ0
    rw [hσx]
    have hστ : χ (Additive.ofMul (σ * τ)) = χ (Additive.ofMul τ) := by
      change χ (Additive.ofMul σ + Additive.ofMul τ) = χ (Additive.ofMul τ)
      rw [map_add, hσ0, zero_add]
    have hστx := fixedField_apply_eq_of_character_eq K χ x hx (σ * τ) τ hστ
    rw [absoluteGaloisAlgEquiv_mul_apply] at hστx
    rw [hστx]
  · rw [if_neg hσ0, map_sub]
    have hσ1 := zmod_two_eq_one_of_ne_zero (χ (Additive.ofMul σ)) hσ0
    have hσx := fixedField_apply_eq_of_character_eq K χ x hx σ τ (hσ1.trans hτ.symm)
    rw [hσx]
    have hστ0 : χ (Additive.ofMul (σ * τ)) = 0 := by
      change χ (Additive.ofMul σ + Additive.ofMul τ) = 0
      rw [map_add, hσ1, hτ]
      decide
    have hστx := fixedField_apply_eq_of_character_eq_zero K χ x hx (σ * τ) hστ0
    rw [absoluteGaloisAlgEquiv_mul_apply] at hστx
    rw [hστx]
    ring

omit [CharZero K] in
theorem antiInvariantElement_sq_fixed
    (χ : MuTwoContinuousH1 K)
    (τ : Field.absoluteGaloisGroup K) (x : AlgebraicClosure K)
    (hτ : χ (Additive.ofMul τ) = 1)
    (hx : x ∈ IntermediateField.fixedField
      (muTwoContinuousCharacterKernel K χ).toSubgroup)
    (σ : Field.absoluteGaloisGroup K) :
    absoluteGaloisAlgEquiv K σ
        ((x - absoluteGaloisAlgEquiv K τ x) ^ 2) =
      (x - absoluteGaloisAlgEquiv K τ x) ^ 2 := by
  rw [map_pow, antiInvariantElement_apply K χ τ x hτ hx σ]
  split <;> ring

theorem quadraticCharacter_eq_of_sq_eq_and_action
    (χ : MuTwoContinuousH1 K) (a : Kˣ) (y : AlgebraicClosure K)
    (hy0 : y ≠ 0)
    (hy_sq : y ^ 2 = algebraMap K (AlgebraicClosure K) (a : K))
    (hy_action : ∀ σ : Field.absoluteGaloisGroup K,
      absoluteGaloisAlgEquiv K σ y =
        if χ (Additive.ofMul σ) = 0 then y else -y) :
    quadraticCharacter K a = χ := by
  have hry : quadraticRoot K a = y ∨ quadraticRoot K a = -y := by
    apply eq_or_eq_neg_of_sq_eq_sq
    rw [quadraticRoot_sq, hy_sq]
  have hyn : -y ≠ y := by
    intro h
    have hsum : y + y = 0 := by
      nth_rewrite 2 [← h]
      simp
    have hmul : (2 : AlgebraicClosure K) * y = 0 := by
      simpa [two_mul] using hsum
    exact (mul_ne_zero (by norm_num) hy0) hmul
  ext σ
  change quadraticCharacterValue K a σ.toMul = χ σ
  by_cases hσ0 : χ σ = 0
  · have hact := hy_action σ.toMul
    change absoluteGaloisAlgEquiv K σ.toMul y =
      (if χ σ = 0 then y else -y) at hact
    rw [if_pos hσ0] at hact
    rw [hσ0]
    rcases hry with hry | hry <;>
      simp [quadraticCharacterValue, hry, hact]
  · have hσ1 := zmod_two_eq_one_of_ne_zero (χ σ) hσ0
    have hact := hy_action σ.toMul
    change absoluteGaloisAlgEquiv K σ.toMul y =
      (if χ σ = 0 then y else -y) at hact
    rw [if_neg hσ0] at hact
    rw [hσ1]
    rcases hry with hry | hry <;>
      simp [quadraticCharacterValue, hry, hact, hyn, Ne.symm hyn]

/-- Every continuous order-two absolute Galois character is the sign
character of a square class. -/
theorem exists_quadraticCharacter_eq (χ : MuTwoContinuousH1 K) :
    ∃ a : Kˣ, quadraticCharacter K a = χ := by
  by_cases hχ : χ = 0
  · refine ⟨1, ?_⟩
    rw [hχ, quadraticCharacter_one]
  · obtain ⟨τ, x, hτ, hx, hτx⟩ := exists_fixedField_element_not_fixed K χ hχ
    let y : AlgebraicClosure K := x - absoluteGaloisAlgEquiv K τ x
    have hy0 : y ≠ 0 := sub_ne_zero.mpr hτx.symm
    have hyfixed : ∀ σ : Field.absoluteGaloisGroup K,
        absoluteGaloisAlgEquiv K σ (y ^ 2) = y ^ 2 := by
      intro σ
      exact antiInvariantElement_sq_fixed K χ τ x hτ hx σ
    have hyrange : y ^ 2 ∈ Set.range (algebraMap K (AlgebraicClosure K)) :=
      (InfiniteGalois.mem_range_algebraMap_iff_fixed (y ^ 2)).mpr hyfixed
    obtain ⟨a, ha⟩ := hyrange
    have ha0 : a ≠ 0 := by
      intro hazero
      have hy2 : y ^ 2 = 0 := by rw [← ha, hazero]; simp
      exact (pow_ne_zero 2 hy0) hy2
    refine ⟨Units.mk0 a ha0, ?_⟩
    apply quadraticCharacter_eq_of_sq_eq_and_action K χ (Units.mk0 a ha0) y hy0
    · simpa using ha.symm
    · intro σ
      exact antiInvariantElement_apply K χ τ x hτ hx σ

theorem quadraticKummerHom_surjective : Function.Surjective (quadraticKummerHom K) := by
  intro χ
  obtain ⟨a, ha⟩ := exists_quadraticCharacter_eq K χ.toAdd
  refine ⟨(a : Rat.SquareClass K), ?_⟩
  rw [quadraticKummerHom_mk, ha]
  rfl

/-- The continuous quadratic Kummer equivalence for every
characteristic-zero field. -/
noncomputable def quadraticKummerEquiv :
    Rat.SquareClass K ≃* Multiplicative (MuTwoContinuousH1 K) :=
  MulEquiv.ofBijective (quadraticKummerHom K)
    ⟨quadraticKummerHom_injective K, quadraticKummerHom_surjective K⟩

end CharZero

end RationalTamagawa
