import SMSFormula.RationalIsotropy
import Mathlib.Algebra.Group.Subgroup.Even

/-!
# Rational square-class localization

This module packages the elementary square-class part of the relative
Tamagawa correction for the central kernel `mu_2`. It upgrades the existing
rational square criterion to the actual multiplicative square-class quotient
and proves that the joint real and `p`-adic localization family is injective.

No algebraic-group, Galois-cohomology, Spin-cover, or Tamagawa theorem is used.
-/

noncomputable section

namespace Rat

/-- Multiplicative square classes of a field. -/
abbrev SquareClass (K : Type*) [Field K] := Kˣ ⧸ Subgroup.square Kˣ

private lemma square_subgroup_le_comap_unitsMap
    {K L : Type*} [Field K] [Field L] (f : K →+* L) :
    Subgroup.square Kˣ ≤ (Subgroup.square Lˣ).comap (Units.map f) := by
  intro x hx
  rw [Subgroup.mem_comap, Subgroup.mem_square] at ⊢
  rw [Subgroup.mem_square] at hx
  obtain ⟨y, hy⟩ := hx
  refine ⟨Units.map f y, ?_⟩
  rw [hy, map_mul]

/-- Extension of scalars on multiplicative square classes. -/
def squareClassMap {K L : Type*} [Field K] [Field L] (f : K →+* L) :
    SquareClass K →* SquareClass L :=
  QuotientGroup.map (Subgroup.square Kˣ) (Subgroup.square Lˣ)
    (Units.map f) (square_subgroup_le_comap_unitsMap f)

/-- A square unit has square underlying value. -/
private lemma isSquare_val_of_isSquare_unit
    {K : Type*} [Field K] {x : Kˣ} (hx : IsSquare x) :
    IsSquare (x : K) := by
  obtain ⟨y, hy⟩ := hx
  refine ⟨(y : K), ?_⟩
  exact congrArg Units.val hy

/-- A nonzero square value determines a square unit. -/
private lemma isSquare_unit_of_isSquare_val
    {K : Type*} [Field K] {x : Kˣ} (hx : IsSquare (x : K)) :
    IsSquare x := by
  obtain ⟨y, hy⟩ := hx
  have hy0 : y ≠ 0 := by
    intro hyzero
    have hxzero : (x : K) = 0 := by simp [hyzero] at hy ⊢
    exact x.ne_zero hxzero
  refine ⟨Units.mk0 y hy0, ?_⟩
  apply Units.ext
  exact hy

/-- A representative has trivial image in a scalar-extended square-class
group exactly when its scalar extension is a square. -/
lemma squareClassMap_mk_eq_one_iff
    {K L : Type*} [Field K] [Field L] (f : K →+* L) (x : Kˣ) :
    squareClassMap f (x : SquareClass K) = 1 ↔
      IsSquare (Units.map f.toMonoidHom x) := by
  change ((Units.map f.toMonoidHom x : Lˣ) : SquareClass L) = 1 ↔ _
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_square]

/-- The rational multiplicative square-class group. -/
abbrev RationalSquareClass := SquareClass ℚ

/-- The real localization map on rational square classes. -/
def rationalSquareClassToReal : RationalSquareClass →* SquareClass ℝ :=
  squareClassMap (algebraMap ℚ ℝ)

/-- The `p`-adic localization map on rational square classes. -/
def rationalSquareClassToPadic (p : ℕ) [Fact p.Prime] :
    RationalSquareClass →* SquareClass ℚ_[p] :=
  squareClassMap (algebraMap ℚ ℚ_[p])

/-- Rational square classes that are trivial over the real completion and
every `p`-adic completion. This is the elementary square-class model for the
localization kernel occurring in the `mu_2` relative Tamagawa factor. -/
def rationalSquareClassLocalGlobalKernel : Subgroup RationalSquareClass where
  carrier := {c | rationalSquareClassToReal c = 1 ∧
    ∀ (p : ℕ) [Fact p.Prime], rationalSquareClassToPadic p c = 1}
  one_mem' := by simp
  mul_mem' := by
    rintro x y ⟨hxreal, hxpadic⟩ ⟨hyreal, hypadic⟩
    constructor
    · simp [hxreal, hyreal]
    · intro p hp
      simp [hxpadic p, hypadic p]
  inv_mem' := by
    rintro x ⟨hxreal, hxpadic⟩
    constructor
    · simp [hxreal]
    · intro p hp
      simp [hxpadic p]

/-- A rational square class trivial at every place is already trivial. -/
theorem rationalSquareClass_eq_one_of_local_eq_one
    (c : RationalSquareClass)
    (hreal : rationalSquareClassToReal c = 1)
    (hpadic : ∀ (p : ℕ) [Fact p.Prime],
      rationalSquareClassToPadic p c = 1) :
    c = 1 := by
  induction c using QuotientGroup.induction_on with
  | _ x =>
      have hrealUnit :
          IsSquare (Units.map (algebraMap ℚ ℝ).toMonoidHom x) :=
        (squareClassMap_mk_eq_one_iff (algebraMap ℚ ℝ) x).mp hreal
      have hrealVal : IsSquare ((x : ℚ) : ℝ) := by
        simpa using isSquare_val_of_isSquare_unit hrealUnit
      have hpadicVal : ∀ (p : ℕ) [Fact p.Prime],
          IsSquare ((x : ℚ) : ℚ_[p]) := by
        intro p hp
        have hpUnit :
            IsSquare (Units.map (algebraMap ℚ ℚ_[p]).toMonoidHom x) :=
          (squareClassMap_mk_eq_one_iff (algebraMap ℚ ℚ_[p]) x).mp
            (hpadic p)
        simpa using isSquare_val_of_isSquare_unit hpUnit
      have hxVal : IsSquare (x : ℚ) :=
        (isSquare_iff_isSquare_real_and_padic (x : ℚ)).mpr
          ⟨hrealVal, hpadicVal⟩
      rw [QuotientGroup.eq_one_iff, Subgroup.mem_square]
      exact isSquare_unit_of_isSquare_val hxVal

/-- The joint real and `p`-adic localization family on rational square
classes is injective. -/
theorem rationalSquareClass_localGlobal_injective
    {x y : RationalSquareClass}
    (hreal : rationalSquareClassToReal x = rationalSquareClassToReal y)
    (hpadic : ∀ (p : ℕ) [Fact p.Prime],
      rationalSquareClassToPadic p x = rationalSquareClassToPadic p y) :
    x = y := by
  have hxy : x⁻¹ * y = 1 := rationalSquareClass_eq_one_of_local_eq_one
    (x⁻¹ * y)
    (by simp [hreal])
    (by intro p hp; simp [hpadic p])
  exact inv_mul_eq_one.mp hxy

/-- The local-global kernel for rational square classes is trivial. -/
theorem rationalSquareClassLocalGlobalKernel_eq_bot :
    rationalSquareClassLocalGlobalKernel = ⊥ := by
  apply le_antisymm
  · intro c hc
    rw [Subgroup.mem_bot]
    exact rationalSquareClass_eq_one_of_local_eq_one c hc.1 hc.2
  · exact bot_le

/-- In particular, the square-class localization kernel has order one. -/
theorem natCard_rationalSquareClassLocalGlobalKernel_eq_one :
    Nat.card rationalSquareClassLocalGlobalKernel = 1 := by
  rw [rationalSquareClassLocalGlobalKernel_eq_bot]
  simp

end Rat
