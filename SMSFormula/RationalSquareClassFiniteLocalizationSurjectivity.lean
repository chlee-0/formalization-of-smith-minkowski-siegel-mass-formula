import SMSFormula.RationalSquareClassLocalGlobal
import SMSFormula.RationalWeakApproximation

/-!
# Finite surjectivity of rational square-class localization

Every finite tuple of p-adic square classes is realized by one positive
rational square class.  The proof chooses an open neighborhood inside each
local square orbit and applies the existing simultaneous real/p-adic weak
approximation theorem.

This is the arithmetic approximation input needed for the rational diagonal
to act on finite Spin-image class carriers.  It is deliberately separate from
the stronger question whether a prescribed positive rational square class is
the spinor norm of a rational special-orthogonal point.
-/

noncomputable section

namespace Rat

local instance rationalSquareClassFiniteLocalizationDecidableEq :
    DecidableEq {p : ℕ // p.Prime} := Classical.decEq _

local instance rationalSquareClassFiniteLocalizationPrimeFact
    (p : {p : ℕ // p.Prime}) : Fact p.1.Prime := ⟨p.2⟩

/-- Joint localization of a rational square class at a finite set of p-adic
places. -/
def rationalSquareClassToFinitePadic
    (S : Finset {p : ℕ // p.Prime}) :
    RationalSquareClass →* ((p : ↥S) → SquareClass ℚ_[p.1.1]) where
  toFun c p := rationalSquareClassToPadic p.1.1 c
  map_one' := by funext p; exact map_one _
  map_mul' x y := by funext p; exact map_mul _ x y

/-- Every finite tuple of p-adic square classes has a positive rational
representative. -/
theorem exists_positive_rat_realizing_finite_padic_squareClasses
    (S : Finset {p : ℕ // p.Prime})
    (y : (p : ↥S) → SquareClass ℚ_[p.1.1]) :
    ∃ q : ℚˣ, 0 < (q : ℚ) ∧
      ∀ p : ↥S,
        rationalSquareClassToPadic p.1.1
            (q : RationalSquareClass) =
          y p := by
  let yAll (p : {p : ℕ // p.Prime}) : SquareClass ℚ_[p.1] :=
    if hp : p ∈ S then y ⟨p, hp⟩ else 1
  let a (p : {p : ℕ // p.Prime}) : ℚ_[p.1] :=
    ((Quotient.out (yAll p) : ℚ_[p.1]ˣ) : ℚ_[p.1])
  have ha (p : {p : ℕ // p.Prime}) : a p ≠ 0 :=
    (Quotient.out (yAll p) : ℚ_[p.1]ˣ).ne_zero
  let openData (p : {p : ℕ // p.Prime}) :=
    exists_isOpen_mem_subset_padic_nonzeroSqOrbit (p := p.1) (ha p)
  let U (p : {p : ℕ // p.Prime}) : Set ℚ_[p.1] :=
    Classical.choose (openData p)
  have hUOpen (p : {p : ℕ // p.Prime}) : IsOpen (U p) :=
    (Classical.choose_spec (openData p)).1
  have haU (p : {p : ℕ // p.Prime}) : a p ∈ U p :=
    (Classical.choose_spec (openData p)).2.1
  have hUSub (p : {p : ℕ // p.Prime}) :
      U p ⊆ {z | ∃ s : ℚ_[p.1], s ≠ 0 ∧ z = s ^ 2 * a p} :=
    (Classical.choose_spec (openData p)).2.2
  obtain ⟨q, hqReal, hqPadic⟩ :=
    exists_rat_mem_real_and_finitely_many_padic_opens S
      (Set.Ioi (0 : ℝ)) U isOpen_Ioi ⟨1, by norm_num⟩
      (fun p _ => hUOpen p) (fun p _ => ⟨a p, haU p⟩)
  have hq : 0 < q := by
    change (0 : ℝ) < (q : ℝ) at hqReal
    exact_mod_cast hqReal
  let qUnit : ℚˣ := Units.mk0 q hq.ne'
  refine ⟨qUnit, hq, ?_⟩
  intro p
  obtain ⟨s, hs, hqs⟩ := hUSub p.1 (hqPadic p.1 p.2)
  have hqs' : (q : ℚ_[p.1.1]) = s ^ 2 *
      ((Quotient.out (y p) : ℚ_[p.1.1]ˣ) : ℚ_[p.1.1]) := by
    simpa [a, yAll, p.2] using hqs
  change
    ((Units.map (algebraMap ℚ ℚ_[p.1.1]) qUnit : ℚ_[p.1.1]ˣ) :
        SquareClass ℚ_[p.1.1]) = y p
  rw [← Quotient.out_eq (y p)]
  apply (QuotientGroup.eq (s := Subgroup.square ℚ_[p.1.1]ˣ)).mpr
  rw [Subgroup.mem_square]
  let sUnit : ℚ_[p.1.1]ˣ := Units.mk0 s hs
  refine ⟨sUnit⁻¹, ?_⟩
  apply Units.ext
  simp only [Units.val_mul, Units.val_inv_eq_inv_val]
  change ((q : ℚ_[p.1.1])⁻¹ *
      ((Quotient.out (y p) : ℚ_[p.1.1]ˣ) : ℚ_[p.1.1])) = s⁻¹ * s⁻¹
  rw [hqs']
  have hout : ((Quotient.out (y p) : ℚ_[p.1.1]ˣ) : ℚ_[p.1.1]) ≠ 0 :=
    (Quotient.out (y p) : ℚ_[p.1.1]ˣ).ne_zero
  field_simp [hout, hs]

/-- Finite p-adic localization on rational square classes is surjective. -/
theorem rationalSquareClassToFinitePadic_surjective
    (S : Finset {p : ℕ // p.Prime}) :
    Function.Surjective (rationalSquareClassToFinitePadic S) := by
  intro y
  obtain ⟨q, _hq, hlocal⟩ :=
    exists_positive_rat_realizing_finite_padic_squareClasses S y
  refine ⟨(q : RationalSquareClass), ?_⟩
  funext p
  exact hlocal p

end Rat
