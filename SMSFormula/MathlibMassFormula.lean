import SMSFormula.MathlibQuadraticForm
import SMSFormula.IntegralQuadraticFormPositiveRank
import SMSFormula.IntegralQuadraticFormFinal
import SMSFormula.IntegralQuadraticFormExplicitFinal
import SMSFormula.IntegralQuadraticFormGenusScaling
import SMSFormula.RationalCliffordSpinCandidateRawDifferentialVolumeProductConvergence
import SMSFormula.Applications.Unimodular.GenusClassification
import SMSFormula.Applications.Unimodular.TypeITotalMass
import SMSFormula.Applications.Unimodular.TypeIITotalMass
import SMSFormula.StandardAxiomsGuard

/-!
# The main theorems for Mathlib quadratic forms

The main theorems restated for `Q : QuadraticForm ℤ (Fin n → ℤ)` with `Q.PosDef`, through the
identifications of `SMSFormula.MathlibQuadraticForm`:

* the positive-rank mass formula, unconditionally: One positive increasing-prime limit P
  satisfies `mass = positiveRankMassCorrection n * (archimedeanMassFactor n * P)`;
  the correction is one half in rank one and one in every rank at least two;
* the classical uncorrected theorem for rank at least two, the old rank-at-least-three
  signatures, and the explicit odd/even formulas at their existing verified ranks;
* the agreement of the two conventions: for an integral lattice `L`, the mass of `Q_L` as an
  integral quadratic form is `L.ordinaryGenusMass`;
* the genus classification of unimodular forms and the total Type I and Type II masses, with the
  isometry groups counted as `Q.IsometryEquiv Q`.

The genus, the mass, the local densities and the archimedean factor are the formalization's own
definitions; this file changes only how the input form is given. The mass of Q is its direct genus class sum. Equality with the mass of the
lattice of its polar form is a proved comparison, used within the proof.
-/

noncomputable section

namespace PositiveDefiniteIntegralQuadraticForm

variable {n : ℕ}

/-- The direct ordinary full-O genus class sum of a positive-definite Mathlib
quadratic form Q on the based module `ℤ^n`. -/
def massOfQuadraticForm (Q : QuadraticForm ℤ (Fin n → ℤ)) (hQ : Q.PosDef) : ℚ :=
  (ofQuadraticForm Q hQ).ordinaryGenusMass

/-- Comparison with the transported ordinary genus mass.  `massOfQuadraticForm`
is defined independently as the direct Q-class sum; this theorem proves that
the two agree. -/
theorem massOfQuadraticForm_eq_transportedOrdinaryGenusMass
    (Q : QuadraticForm ℤ (Fin n → ℤ)) (hQ : Q.PosDef) :
    massOfQuadraticForm Q hQ = (ofQuadraticForm Q hQ).transportedOrdinaryGenusMass :=
  (ofQuadraticForm Q hQ).ordinaryGenusMass_eq_transportedOrdinaryGenusMass

/-- **Positive-rank mass formula** for Mathlib Q. The mass is the direct
Q-class sum; the same P is used by the direct local-product bridge. -/
theorem exists_massOfQuadraticForm_eq_positiveRank (hn : 1 ≤ n)
    (Q : QuadraticForm ℤ (Fin n → ℤ)) (hQ : Q.PosDef) :
    ∃ P : ℝ, 0 < P ∧ (ofQuadraticForm Q hQ).massLocalInverseProductTendsTo P ∧
      ((massOfQuadraticForm Q hQ : ℚ) : ℝ) =
        PositiveDefiniteIntegralLattice.positiveRankMassCorrection n *
          (PositiveDefiniteIntegralLattice.archimedeanMassFactor n * P) :=
  (ofQuadraticForm Q hQ).exists_massFormula_positiveRank hn

/-- Classical uncorrected Mathlib-form mass in every rank at least two. -/
theorem exists_massOfQuadraticForm_eq_of_two_le (hn : 2 ≤ n)
    (Q : QuadraticForm ℤ (Fin n → ℤ)) (hQ : Q.PosDef) :
    ∃ P : ℝ, 0 < P ∧ (ofQuadraticForm Q hQ).massLocalInverseProductTendsTo P ∧
      ((massOfQuadraticForm Q hQ : ℚ) : ℝ) = PositiveDefiniteIntegralLattice.archimedeanMassFactor n * P :=
  (ofQuadraticForm Q hQ).exists_massFormula_of_two_le hn

/-- The corrected Mathlib-form formula for any supplied actual ordered limit. -/
theorem massOfQuadraticForm_eq_positiveRank (hn : 1 ≤ n)
    (Q : QuadraticForm ℤ (Fin n → ℤ)) (hQ : Q.PosDef) {P : ℝ}
    (hconv : (ofQuadraticForm Q hQ).massLocalInverseProductTendsTo P) :
    ((massOfQuadraticForm Q hQ : ℚ) : ℝ) =
      PositiveDefiniteIntegralLattice.positiveRankMassCorrection n *
        (PositiveDefiniteIntegralLattice.archimedeanMassFactor n * P) :=
  (ofQuadraticForm Q hQ).ordinaryGenusMass_eq_positiveRankMassFormula hn hconv

/-- The classical Mathlib-form formula for any actual limit in rank at least two. -/
theorem massOfQuadraticForm_eq_of_two_le (hn : 2 ≤ n)
    (Q : QuadraticForm ℤ (Fin n → ℤ)) (hQ : Q.PosDef) {P : ℝ}
    (hconv : (ofQuadraticForm Q hQ).massLocalInverseProductTendsTo P) :
    ((massOfQuadraticForm Q hQ : ℚ) : ℝ) = PositiveDefiniteIntegralLattice.archimedeanMassFactor n * P :=
  (ofQuadraticForm Q hQ).ordinaryGenusMass_eq_massFormula_of_two_le hn hconv

/-- Every positive unary Mathlib form has direct ordinary mass one half. -/
theorem massOfQuadraticForm_eq_one_half_rank_one
    (Q : QuadraticForm ℤ (Fin 1 → ℤ)) (hQ : Q.PosDef) :
    massOfQuadraticForm Q hQ = (1 / 2 : ℚ) := by
  rw [massOfQuadraticForm, ordinaryGenusMass_eq_latticeOfPolarForm]
  exact PositiveDefiniteIntegralLattice.ordinaryGenusMass_eq_one_half_rank_one _

/-- **Mass formula** for a positive-definite integral quadratic form of rank `n ≥ 3`: the inverse
local products converge to some `P > 0`, and the mass is `archimedeanMassFactor n * P`. -/
theorem exists_massOfQuadraticForm_eq (hn : 3 ≤ n) (Q : QuadraticForm ℤ (Fin n → ℤ))
    (hQ : Q.PosDef) :
    ∃ P : ℝ, 0 < P ∧ (ofQuadraticForm Q hQ).massLocalInverseProductTendsTo P ∧
      ((massOfQuadraticForm Q hQ : ℚ) : ℝ) = PositiveDefiniteIntegralLattice.archimedeanMassFactor n * P := by
  set H := ofQuadraticForm Q hQ
  obtain ⟨P, hP, hconv⟩ :=
    PositiveDefiniteIntegralLattice.exists_pos_massLocalInverseProductTendsTo H.latticeOfPolarForm hn
  have hconv' : H.massLocalInverseProductTendsTo P :=
    (H.massLocalInverseProductTendsTo_iff_latticeOfPolarForm P).mpr hconv
  refine ⟨P, hP, hconv', ?_⟩
  change ((H.ordinaryGenusMass : ℚ) : ℝ) = _
  rw [H.ordinaryGenusMass_eq_transportedOrdinaryGenusMass]
  exact H.transportedOrdinaryGenusMass_eq_massFormulaProductSide hn hP hconv'

/-- The mass formula in odd rank `n = 2s - 1`, with the explicit Euler-product limit. -/
theorem massOfQuadraticForm_eq_oddRankProductLimit (hn3 : 3 ≤ n)
    (Q : QuadraticForm ℤ (Fin n → ℤ)) (hQ : Q.PosDef) {N s : ℕ}
    (hB : (ofQuadraticForm Q hQ).massBadPrimeSet ⊆ PositiveDefiniteIntegralLattice.rationalPrimesUpTo N)
    (hs : 0 < s) (hn : n = 2 * s - 1) :
    ((massOfQuadraticForm Q hQ : ℚ) : ℝ) =
      PositiveDefiniteIntegralLattice.archimedeanMassFactor n *
        (ofQuadraticForm Q hQ).oddRankOrdinaryMassProductLimit N s :=
  by
    rw [massOfQuadraticForm_eq_transportedOrdinaryGenusMass]
    exact (ofQuadraticForm Q hQ).transportedOrdinaryGenusMass_eq_massFormulaProductSide_oddRankProductLimit
      hn3 hB hs hn

/-- The mass formula in even rank `n = 2s`, with the explicit Euler-product limit. -/
theorem massOfQuadraticForm_eq_evenRankProductLimit (hn3 : 3 ≤ n)
    (Q : QuadraticForm ℤ (Fin n → ℤ)) (hQ : Q.PosDef) {N s : ℕ}
    (hB : (ofQuadraticForm Q hQ).massBadPrimeSet ⊆ PositiveDefiniteIntegralLattice.rationalPrimesUpTo N)
    (hn : n = 2 * s) :
    ((massOfQuadraticForm Q hQ : ℚ) : ℝ) =
      PositiveDefiniteIntegralLattice.archimedeanMassFactor n *
        (ofQuadraticForm Q hQ).evenRankOrdinaryMassProductLimit N s :=
  by
    rw [massOfQuadraticForm_eq_transportedOrdinaryGenusMass]
    exact (ofQuadraticForm Q hQ).transportedOrdinaryGenusMass_eq_massFormulaProductSide_evenRankProductLimit
      hn3 hB hn

/-- The integral quadratic form of an integral lattice `L` is `L.toIntegralQuadraticForm`. -/
theorem ofQuadraticForm_integralLattice (L : PositiveDefiniteIntegralLattice n) :
    ofQuadraticForm L.quadraticForm L.quadraticForm_posDef = L.toIntegralQuadraticForm := by
  rw [← ofQuadraticForm_quadraticForm L.toIntegralQuadraticForm]
  congr 1
  exact (PositiveDefiniteIntegralLattice.quadraticForm_toIntegralQuadraticForm L).symm

/-- The two conventions agree: the mass of `Q_L` as an integral quadratic form is the ordinary genus
mass of the integral lattice `L`. -/
theorem massOfQuadraticForm_integralLattice (L : PositiveDefiniteIntegralLattice n) :
    massOfQuadraticForm L.quadraticForm L.quadraticForm_posDef = L.ordinaryGenusMass := by
  rw [massOfQuadraticForm, ofQuadraticForm_integralLattice,
    ordinaryGenusMass_eq_transportedOrdinaryGenusMass,
    L.toIntegralQuadraticForm_transportedOrdinaryGenusMass]

end PositiveDefiniteIntegralQuadraticForm

open UnimodularMass

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- An integral quadratic form all of whose values are even is classically integral. -/
theorem isClassicallyIntegral_of_forall_even {Q : QuadraticForm ℤ (Fin n → ℤ)}
    (h : ∀ x, Even (Q x)) : IsClassicallyIntegral Q := by
  intro i j
  have hp : QuadraticMap.polar Q (Pi.single i 1) (Pi.single j 1) =
      Q (Pi.single i 1 + Pi.single j 1) - Q (Pi.single i 1) - Q (Pi.single j 1) := rfl
  rw [hp]
  exact ((h _).sub (h _)).sub (h _)

theorem quadForm_ofQuadraticForm (Q : QuadraticForm ℤ (Fin n → ℤ)) (hQ : Q.PosDef)
    (hev : IsClassicallyIntegral Q) (x : Fin n → ℤ) :
    (ofQuadraticForm Q hQ hev).quadForm x = Q x := by
  rw [quadForm, quadraticForm_ofQuadraticForm]

/-- **Type I unimodular forms** (`det F = 1` and some odd value) are in the genus of the identity
form. -/
theorem isSameGenus_identity_of_quadraticForm (Q : QuadraticForm ℤ (Fin n → ℤ)) (hQ : Q.PosDef)
    (hev : IsClassicallyIntegral Q) (hdet : (halfPolarMatrix Q).det = 1)
    (hodd : ∃ x, Odd (Q x)) :
    (ofQuadraticForm Q hQ hev).IsSameGenus (identityLattice n) :=
  isSameGenus_identity_of_typeIUnimodular _ hdet
    (by obtain ⟨x, hx⟩ := hodd; exact ⟨x, by rw [quadForm_ofQuadraticForm]; exact hx⟩)

/-- **Type II unimodular forms** of rank `8k` (`det F = 1` and all values even) are in the genus of
the seed form `E₈ ⊕ ⋯ ⊕ E₈`. -/
theorem isSameGenus_typeIISeed_of_quadraticForm (k : ℕ) (hk : 0 < k)
    (Q : QuadraticForm ℤ (Fin (8 * k) → ℤ)) (hQ : Q.PosDef) (heven : ∀ x, Even (Q x))
    (hdet : (halfPolarMatrix Q).det = 1) :
    (ofQuadraticForm Q hQ (isClassicallyIntegral_of_forall_even heven)).IsSameGenus
      (typeIISeed k) :=
  isSameGenus_typeIISeed_of_typeIIUnimodular k hk _ hdet
    (fun x => by rw [quadForm_ofQuadraticForm]; exact heven x)

/-- The total Type I class mass with the isometry groups counted as Mathlib self-isometries. -/
theorem totalTypeIClassMass_eq_sum_isometryEquiv (n : ℕ) :
    totalTypeIClassMass n =
      ∑ C : UnimodularTypeIIsometryClass n,
        ((Nat.card ((typeIClassRepresentative C).quadraticForm.IsometryEquiv
          (typeIClassRepresentative C).quadraticForm) : ℚ)⁻¹) := by
  unfold totalTypeIClassMass
  refine Finset.sum_congr rfl fun C _ => ?_
  rw [← natCard_isometryGroup, Nat.card_eq_fintype_card]

/-- The total Type II class mass with the isometry groups counted as Mathlib self-isometries. -/
theorem totalTypeIIClassMass_eq_sum_isometryEquiv (n : ℕ) :
    totalTypeIIClassMass n =
      ∑ C : UnimodularTypeIIIsometryClass n,
        ((Nat.card ((typeIIClassRepresentative C).quadraticForm.IsometryEquiv
          (typeIIClassRepresentative C).quadraticForm) : ℚ)⁻¹) := by
  unfold totalTypeIIClassMass
  refine Finset.sum_congr rfl fun C _ => ?_
  rw [← natCard_isometryGroup, Nat.card_eq_fintype_card]

/-- **Total Type I mass** in every rank, as a sum over Mathlib isometry groups. -/
theorem sum_isometryEquiv_typeI_eq_typeIConstant (n : ℕ) :
    ∑ C : UnimodularTypeIIsometryClass n,
        ((Nat.card ((typeIClassRepresentative C).quadraticForm.IsometryEquiv
          (typeIClassRepresentative C).quadraticForm) : ℚ)⁻¹) = typeIConstant n := by
  rw [← totalTypeIClassMass_eq_sum_isometryEquiv]
  exact totalTypeIClassMass_eq_typeIConstant

/-- **Total Type II mass** in every rank, as a sum over Mathlib isometry groups. -/
theorem sum_isometryEquiv_typeII_eq_typeIIConstant (n : ℕ) :
    ∑ C : UnimodularTypeIIIsometryClass n,
        ((Nat.card ((typeIIClassRepresentative C).quadraticForm.IsometryEquiv
          (typeIIClassRepresentative C).quadraticForm) : ℚ)⁻¹) = typeIIConstant n := by
  rw [← totalTypeIIClassMass_eq_sum_isometryEquiv]
  exact totalTypeIIClassMass_eq_typeIIConstant n

end PositiveDefiniteIntegralLattice

#assert_standard_axioms PositiveDefiniteIntegralQuadraticForm.exists_massOfQuadraticForm_eq
#assert_standard_axioms PositiveDefiniteIntegralQuadraticForm.massOfQuadraticForm_eq_oddRankProductLimit
#assert_standard_axioms PositiveDefiniteIntegralQuadraticForm.massOfQuadraticForm_eq_evenRankProductLimit
#assert_standard_axioms PositiveDefiniteIntegralQuadraticForm.massOfQuadraticForm_integralLattice
#assert_standard_axioms PositiveDefiniteIntegralLattice.isSameGenus_identity_of_quadraticForm
#assert_standard_axioms PositiveDefiniteIntegralLattice.isSameGenus_typeIISeed_of_quadraticForm
#assert_standard_axioms PositiveDefiniteIntegralLattice.sum_isometryEquiv_typeI_eq_typeIConstant
#assert_standard_axioms PositiveDefiniteIntegralLattice.sum_isometryEquiv_typeII_eq_typeIIConstant

#assert_standard_axioms PositiveDefiniteIntegralQuadraticForm.exists_massOfQuadraticForm_eq_positiveRank
#assert_standard_axioms PositiveDefiniteIntegralQuadraticForm.exists_massOfQuadraticForm_eq_of_two_le
#assert_standard_axioms PositiveDefiniteIntegralQuadraticForm.massOfQuadraticForm_eq_positiveRank
#assert_standard_axioms PositiveDefiniteIntegralQuadraticForm.massOfQuadraticForm_eq_of_two_le
#assert_standard_axioms PositiveDefiniteIntegralQuadraticForm.massOfQuadraticForm_eq_one_half_rank_one
