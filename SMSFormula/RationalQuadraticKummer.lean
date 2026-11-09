import SMSFormula.RationalMuTwoCharacterCohomology
import Mathlib.FieldTheory.Galois.Profinite

/-!
# The quadratic Kummer embedding

For a characteristic-zero field `K`, this module constructs the continuous
quadratic character attached to a unit `a : Kˣ`. Choose a square root `r` of
`a` in `AlgebraicClosure K`; an absolute Galois automorphism sends `r` to
either `r` or `-r`, and the resulting sign is an additive character with
values in `ZMod 2`.

The character is continuous because its kernel is the stabilizer of the
integral element `r`, which is open in the Krull topology. Multiplicativity in
`a` lets the construction descend to square classes. Infinite Galois theory
then shows that the descended map is injective: if every automorphism fixes
`r`, then `r` lies in the base field and `a` is a square.

This proves the injective half of the specialized continuous quadratic Kummer
comparison

```text
Kˣ / Kˣ²  ->  Hom_cont(G_K, Z/2).
```

Surjectivity and compatibility with completion-induced restriction maps are
handled in separate modules. In particular, no nonexistent functorial map
between mathlib's chosen absolute Galois groups is assumed here.
-/

noncomputable section

namespace RationalTamagawa

variable (K : Type) [Field K]

local instance : DecidableEq (AlgebraicClosure K) := Classical.decEq _

/-- Expose an element of mathlib's absolute Galois group as its underlying
algebra automorphism. -/
abbrev absoluteGaloisAlgEquiv (σ : Field.absoluteGaloisGroup K) :
    AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K := σ

@[simp]
theorem absoluteGaloisAlgEquiv_mul_apply
    (σ τ : Field.absoluteGaloisGroup K) (x : AlgebraicClosure K) :
    absoluteGaloisAlgEquiv K (σ * τ) x =
      absoluteGaloisAlgEquiv K σ (absoluteGaloisAlgEquiv K τ x) :=
  rfl

/-- A chosen square root in the algebraic closure. Its eventual character is
independent of the sign ambiguity. -/
noncomputable def quadraticRoot (a : Kˣ) : AlgebraicClosure K :=
  (IsAlgClosed.exists_pow_nat_eq
    (algebraMap K (AlgebraicClosure K) (a : K)) (n := 2) (by norm_num)).choose

theorem quadraticRoot_sq (a : Kˣ) :
    quadraticRoot K a ^ 2 = algebraMap K (AlgebraicClosure K) (a : K) :=
  (IsAlgClosed.exists_pow_nat_eq
    (algebraMap K (AlgebraicClosure K) (a : K)) (n := 2) (by norm_num)).choose_spec

theorem quadraticRoot_ne_zero (a : Kˣ) : quadraticRoot K a ≠ 0 := by
  intro h
  have hz : algebraMap K (AlgebraicClosure K) (a : K) = 0 := by
    rw [← quadraticRoot_sq K a, h]
    norm_num
  apply a.ne_zero
  apply (algebraMap K (AlgebraicClosure K)).injective
  exact hz.trans (map_zero (algebraMap K (AlgebraicClosure K))).symm

/-- Every continuous order-two character has additive exponent two. -/
theorem muTwoContinuousH1_add_self (χ : MuTwoContinuousH1 K) : χ + χ = 0 := by
  ext σ
  change χ σ + χ σ = 0
  calc
    χ σ + χ σ = (2 : ZMod 2) * χ σ := by ring
    _ = 0 := by rw [show (2 : ZMod 2) = 0 by decide, zero_mul]

section CharZero

variable [CharZero K]

theorem neg_quadraticRoot_ne (a : Kˣ) :
    -quadraticRoot K a ≠ quadraticRoot K a := by
  intro h
  have hsum : quadraticRoot K a + quadraticRoot K a = 0 := by
    nth_rewrite 2 [← h]
    simp
  have hmul : (2 : AlgebraicClosure K) * quadraticRoot K a = 0 := by
    simpa [two_mul] using hsum
  exact (mul_ne_zero (by norm_num) (quadraticRoot_ne_zero K a)) hmul

omit [CharZero K] in
theorem absoluteGalois_quadraticRoot_eq_or_eq_neg
    (a : Kˣ) (σ : Field.absoluteGaloisGroup K) :
    absoluteGaloisAlgEquiv K σ (quadraticRoot K a) = quadraticRoot K a ∨
      absoluteGaloisAlgEquiv K σ (quadraticRoot K a) = -quadraticRoot K a := by
  apply eq_or_eq_neg_of_sq_eq_sq
  rw [← map_pow, quadraticRoot_sq K a]
  simp [absoluteGaloisAlgEquiv]

/-- The sign by which an absolute Galois automorphism acts on the chosen
square root. -/
noncomputable def quadraticCharacterValue
    (a : Kˣ) (σ : Field.absoluteGaloisGroup K) : ZMod 2 :=
  if absoluteGaloisAlgEquiv K σ (quadraticRoot K a) = quadraticRoot K a then 0 else 1

theorem quadraticCharacterValue_mul
    (a : Kˣ) (σ τ : Field.absoluteGaloisGroup K) :
    quadraticCharacterValue K a (σ * τ) =
      quadraticCharacterValue K a σ + quadraticCharacterValue K a τ := by
  have hn := neg_quadraticRoot_ne K a
  rcases absoluteGalois_quadraticRoot_eq_or_eq_neg K a σ with hσ | hσ <;>
    rcases absoluteGalois_quadraticRoot_eq_or_eq_neg K a τ with hτ | hτ
  all_goals
    simp [quadraticCharacterValue, absoluteGaloisAlgEquiv_mul_apply,
      hσ, hτ, hn]
  exact (by decide : (0 : ZMod 2) = 1 + 1)

/-- The abstract additive homomorphism underlying the quadratic character. -/
noncomputable def quadraticCharacterHom (a : Kˣ) :
    Additive (Field.absoluteGaloisGroup K) →+ ZMod 2 where
  toFun σ := quadraticCharacterValue K a σ.toMul
  map_zero' := by
    change (if (1 : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
      (quadraticRoot K a) = quadraticRoot K a then (0 : ZMod 2) else 1) = 0
    simp only [AlgEquiv.one_apply, if_pos]
  map_add' σ τ := quadraticCharacterValue_mul K a σ.toMul τ.toMul

/-- The kernel is open because it is the stabilizer of an integral element in
the Krull topology. -/
theorem quadraticCharacterHom_ker_isOpen (a : Kˣ) :
    IsOpen ((quadraticCharacterHom K a).ker :
      Set (Additive (Field.absoluteGaloisGroup K))) := by
  have hopen := stabilizer_isOpen_of_isIntegral (K := K) (quadraticRoot K a)
  rw [show ((quadraticCharacterHom K a).ker :
      Set (Additive (Field.absoluteGaloisGroup K))) =
      {σ | absoluteGaloisAlgEquiv K σ.toMul (quadraticRoot K a) =
        quadraticRoot K a} by
    ext σ
    simp [quadraticCharacterHom, quadraticCharacterValue]]
  change IsOpen {σ : Field.absoluteGaloisGroup K |
    absoluteGaloisAlgEquiv K σ (quadraticRoot K a) = quadraticRoot K a}
  exact hopen

theorem quadraticCharacterHom_continuous (a : Kˣ) :
    Continuous (quadraticCharacterHom K a) := by
  apply continuous_of_continuousAt_zero (quadraticCharacterHom K a)
  rw [continuousAt_def]
  intro s hs
  rw [map_zero] at hs
  apply mem_nhds_iff.mpr
  refine ⟨(quadraticCharacterHom K a).ker, ?_,
    quadraticCharacterHom_ker_isOpen K a, by simp⟩
  intro σ hσ
  have hz : quadraticCharacterHom K a σ = 0 := hσ
  have h0s : (0 : ZMod 2) ∈ s := mem_of_mem_nhds hs
  simpa [hz] using h0s

/-- The continuous quadratic character attached to a unit. -/
noncomputable def quadraticCharacter (a : Kˣ) : MuTwoContinuousH1 K :=
  ContinuousAddMonoidHom.mk (quadraticCharacterHom K a)
    (quadraticCharacterHom_continuous K a)

omit [CharZero K] in
theorem quadraticRoot_mul_eq_or_eq_neg (a b : Kˣ) :
    quadraticRoot K (a * b) = quadraticRoot K a * quadraticRoot K b ∨
      quadraticRoot K (a * b) = -(quadraticRoot K a * quadraticRoot K b) := by
  apply eq_or_eq_neg_of_sq_eq_sq
  rw [quadraticRoot_sq, mul_pow, quadraticRoot_sq, quadraticRoot_sq]
  simp

theorem quadraticCharacterValue_mul_units
    (a b : Kˣ) (σ : Field.absoluteGaloisGroup K) :
    quadraticCharacterValue K (a * b) σ =
      quadraticCharacterValue K a σ + quadraticCharacterValue K b σ := by
  have hp0 : quadraticRoot K a * quadraticRoot K b ≠ 0 :=
    mul_ne_zero (quadraticRoot_ne_zero K a) (quadraticRoot_ne_zero K b)
  have hpn : -(quadraticRoot K a * quadraticRoot K b) ≠
      quadraticRoot K a * quadraticRoot K b := by
    intro h
    have hsum : quadraticRoot K a * quadraticRoot K b +
        quadraticRoot K a * quadraticRoot K b = 0 := by
      nth_rewrite 2 [← h]
      simp
    have hmul : (2 : AlgebraicClosure K) *
        (quadraticRoot K a * quadraticRoot K b) = 0 := by
      simpa [two_mul] using hsum
    exact (mul_ne_zero (by norm_num) hp0) hmul
  have hpnp : quadraticRoot K a * quadraticRoot K b ≠
      -(quadraticRoot K a * quadraticRoot K b) := Ne.symm hpn
  have hna := neg_quadraticRoot_ne K a
  have hnb := neg_quadraticRoot_ne K b
  rcases quadraticRoot_mul_eq_or_eq_neg K a b with hab | hab <;>
    rcases absoluteGalois_quadraticRoot_eq_or_eq_neg K a σ with ha | ha <;>
    rcases absoluteGalois_quadraticRoot_eq_or_eq_neg K b σ with hb | hb
  all_goals
    simp [quadraticCharacterValue, hab, map_mul, map_neg, ha, hb,
      hpn, hpnp, hna, hnb]
  all_goals exact (by decide : (0 : ZMod 2) = 1 + 1)

theorem quadraticCharacter_mul (a b : Kˣ) :
    quadraticCharacter K (a * b) = quadraticCharacter K a + quadraticCharacter K b := by
  ext σ
  exact quadraticCharacterValue_mul_units K a b σ.toMul

theorem quadraticCharacter_one : quadraticCharacter K 1 = 0 := by
  have h := quadraticCharacter_mul K (1 : Kˣ) 1
  simp only [one_mul] at h
  have hsub := congrArg (fun χ => χ - quadraticCharacter K 1) h
  simpa using hsub.symm

/-- The quadratic-character homomorphism before quotienting by squares. -/
noncomputable def quadraticCharacterUnitsHom :
    Kˣ →* Multiplicative (MuTwoContinuousH1 K) where
  toFun a := Multiplicative.ofAdd (quadraticCharacter K a)
  map_one' := congrArg Multiplicative.ofAdd (quadraticCharacter_one K)
  map_mul' a b := congrArg Multiplicative.ofAdd (quadraticCharacter_mul K a b)

theorem square_le_quadraticCharacterUnitsHom_ker :
    Subgroup.square Kˣ ≤ (quadraticCharacterUnitsHom K).ker := by
  intro a ha
  rw [Subgroup.mem_square] at ha
  obtain ⟨b, rfl⟩ := ha
  rw [MonoidHom.mem_ker, map_mul]
  change Multiplicative.ofAdd (quadraticCharacter K b + quadraticCharacter K b) =
    Multiplicative.ofAdd 0
  rw [muTwoContinuousH1_add_self]

/-- The quadratic Kummer map from square classes to continuous
order-two Galois characters. -/
noncomputable def quadraticKummerHom :
    Rat.SquareClass K →* Multiplicative (MuTwoContinuousH1 K) :=
  QuotientGroup.lift (Subgroup.square Kˣ) (quadraticCharacterUnitsHom K)
    (square_le_quadraticCharacterUnitsHom_ker K)

@[simp]
theorem quadraticKummerHom_mk (a : Kˣ) :
    quadraticKummerHom K (a : Rat.SquareClass K) =
      Multiplicative.ofAdd (quadraticCharacter K a) :=
  rfl

theorem quadraticCharacter_eq_zero_of_isSquare
    (a : Kˣ) (ha : IsSquare a) : quadraticCharacter K a = 0 := by
  obtain ⟨b, rfl⟩ := ha
  rw [quadraticCharacter_mul, muTwoContinuousH1_add_self]

/-- If the quadratic character is trivial, its chosen root is fixed by the
entire absolute Galois group. Infinite Galois theory puts that root back in
the base field, so the original unit is a square. -/
theorem isSquare_of_quadraticCharacter_eq_zero
    (a : Kˣ) (ha : quadraticCharacter K a = 0) : IsSquare a := by
  have hfix : ∀ σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K,
      σ (quadraticRoot K a) = quadraticRoot K a := by
    intro σ
    have hv : quadraticCharacterValue K a σ = 0 := by
      change quadraticCharacter K a (Additive.ofMul σ) = 0
      rw [ha]
      rfl
    simpa [quadraticCharacterValue] using hv
  have hrange : quadraticRoot K a ∈ Set.range (algebraMap K (AlgebraicClosure K)) :=
    (InfiniteGalois.mem_range_algebraMap_iff_fixed (quadraticRoot K a)).mpr hfix
  obtain ⟨x, hx⟩ := hrange
  have hx0 : x ≠ 0 := by
    intro hxzero
    apply quadraticRoot_ne_zero K a
    rw [← hx, hxzero]
    simp
  refine ⟨Units.mk0 x hx0, ?_⟩
  apply Units.ext
  apply (algebraMap K (AlgebraicClosure K)).injective
  simp only [Units.val_mul, Units.val_mk0]
  rw [map_mul, hx]
  simpa [pow_two] using (quadraticRoot_sq K a).symm

theorem quadraticCharacter_eq_zero_iff_isSquare (a : Kˣ) :
    quadraticCharacter K a = 0 ↔ IsSquare a :=
  ⟨isSquare_of_quadraticCharacter_eq_zero K a,
    quadraticCharacter_eq_zero_of_isSquare K a⟩

/-- The continuous quadratic Kummer map is injective for every
characteristic-zero field. -/
theorem quadraticKummerHom_injective : Function.Injective (quadraticKummerHom K) := by
  rw [← MonoidHom.ker_eq_bot_iff]
  apply le_antisymm
  · intro c hc
    rw [Subgroup.mem_bot]
    induction c using QuotientGroup.induction_on with
    | _ a =>
        rw [MonoidHom.mem_ker, quadraticKummerHom_mk] at hc
        have hzero : quadraticCharacter K a = 0 := congrArg Multiplicative.toAdd hc
        rw [QuotientGroup.eq_one_iff, Subgroup.mem_square]
        exact (quadraticCharacter_eq_zero_iff_isSquare K a).mp hzero
  · exact bot_le

end CharZero

end RationalTamagawa
