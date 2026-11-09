import SMSFormula.PadicSpecialOrthogonalDifferentialDensityRawGramQuotientBoundary

/-!
# The full-initial-value raw Gram lifting property

The selected associated-bilinear Hensel tower retains the coarsened quotient
family, not an arbitrary complete raw matrix modulo the selected prime power.
This module states the stronger property and proves that it
is equivalent to surjectivity of every concrete ordinary-to-raw quotient
fiber injection.

It also records why the generic matrix-correction surjectivity theorem
does not settle the bad-prime case: positive discriminant valuation makes the
Gram pairing matrix modulo the residue prime noninvertible.
-/

noncomputable section

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- A selected-depth raw Gram solution has a full-initial-value lift when it
is the literal complete reduction of an integral p-adic stabilizer, rather
than merely sharing its associated-bilinear quotient columns. -/
def HasLocalPadicSpecialOrthogonalDifferentialDensityFullInitialRawGramLift
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)]
    (X : L.localPadicSpecialOrthogonalDifferentialDensityRawGramSolution p) :
    Prop :=
  ∃ g : L.localPadicLatticeStabilizerSubgroup p,
    (L.localPadicLatticeStabilizerReduction p
      (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p) g).1 =
      X.1

/-- Full-initial-value lifting is exactly membership in the image of the
ordinary-reduction-to-raw-Gram injection. -/
theorem
    hasLocalPadicSpecialOrthogonalDifferentialDensityFullInitialRawGramLift_iff_exists_ordinaryReduction
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)]
    (X : L.localPadicSpecialOrthogonalDifferentialDensityRawGramSolution p) :
    L.HasLocalPadicSpecialOrthogonalDifferentialDensityFullInitialRawGramLift p X ↔
      ∃ u :
          L.localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionRange p,
        L.localPadicLatticeStabilizerReductionRangeToGramCongruenceSolutions p
            (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p) u =
          X := by
  constructor
  · rintro ⟨g, hg⟩
    let u :
        L.localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionRange p :=
      ⟨L.localPadicLatticeStabilizerReduction p
          (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p) g,
        ⟨g, rfl⟩⟩
    refine ⟨u, ?_⟩
    apply Subtype.ext
    exact hg
  · rintro ⟨u, hu⟩
    rcases u.2 with ⟨g, hg⟩
    refine ⟨g, ?_⟩
    have hval := congrArg Subtype.val hu
    exact (congrArg Units.val hg).trans hval

/-- At an odd prime, lifting every selected raw Gram solution with its full
initial value is equivalent to surjectivity on every fiber of the selected
quotient map. -/
theorem
    all_fullInitialRawGramLift_iff_forall_ordinaryReductionFiberToRawGramFiber_surjective
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] (hp2 : p ≠ 2) :
    (∀ X : L.localPadicSpecialOrthogonalDifferentialDensityRawGramSolution p,
        L.HasLocalPadicSpecialOrthogonalDifferentialDensityFullInitialRawGramLift p X) ↔
      ∀ Y :
          L.localPadicSpecialOrthogonalDifferentialDensityAssociatedBilinearQuotientFamily
            p,
        Function.Surjective
          (L.localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionFiberToRawGramFiber
            p hp2 Y) := by
  constructor
  · intro hall Y X
    obtain ⟨u, hu⟩ :=
      (L.hasLocalPadicSpecialOrthogonalDifferentialDensityFullInitialRawGramLift_iff_exists_ordinaryReduction
        p X.1).mp (hall X.1)
    have huY :
        L.localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionRangeToQuotientFamily
            p u = Y := by
      calc
        L.localPadicSpecialOrthogonalDifferentialDensityOrdinaryReductionRangeToQuotientFamily
            p u =
            L.localPadicSpecialOrthogonalDifferentialDensityRawGramSolutionToQuotientFamily
              p hp2
              (L.localPadicLatticeStabilizerReductionRangeToGramCongruenceSolutions p
                (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p) u) :=
          (L.localPadicSpecialOrthogonalDifferentialDensity_rawGram_ordinaryReduction_commutes
            p hp2 u).symm
        _ = L.localPadicSpecialOrthogonalDifferentialDensityRawGramSolutionToQuotientFamily
              p hp2 X.1 := by rw [hu]
        _ = Y := X.2
    refine ⟨⟨u, huY⟩, ?_⟩
    apply Subtype.ext
    exact hu
  · intro hfiber X
    let Y :=
      L.localPadicSpecialOrthogonalDifferentialDensityRawGramSolutionToQuotientFamily
        p hp2 X
    let Xfiber :
        {Z : L.localPadicSpecialOrthogonalDifferentialDensityRawGramSolution p //
          L.localPadicSpecialOrthogonalDifferentialDensityRawGramSolutionToQuotientFamily
            p hp2 Z = Y} :=
      ⟨X, rfl⟩
    obtain ⟨u, hu⟩ := hfiber Y Xfiber
    apply
      (L.hasLocalPadicSpecialOrthogonalDifferentialDensityFullInitialRawGramLift_iff_exists_ordinaryReduction
        p X).mpr
    refine ⟨u.1, ?_⟩
    exact congrArg Subtype.val hu

/-- Positive discriminant valuation makes the associated Gram matrix singular
over the residue field. -/
theorem polarGramMatrix_mod_prime_not_isUnit_of_padicValInt_polarDeterminant_pos
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)]
    (hval : 0 < padicValInt p L.polarDeterminant) :
    ¬ IsUnit (matrixMod L.polarGramMatrix (primePowModulus p 1)) := by
  letI : Fact (1 < (primePowModulus p 1 : ℕ)) :=
    ⟨by simpa [primePowModulus] using (Fact.out : Nat.Prime p).one_lt⟩
  rw [Matrix.isUnit_iff_isUnit_det]
  have hdet :
      (matrixMod L.polarGramMatrix (primePowModulus p 1)).det =
        (L.polarDeterminant : ZMod (primePowModulus p 1 : ℕ)) := by
    change
      (L.polarGramMatrix.map
        (Int.castRingHom (ZMod (primePowModulus p 1 : ℕ)))).det =
        (L.polarDeterminant : ZMod (primePowModulus p 1 : ℕ))
    exact
      (RingHom.map_det
        (Int.castRingHom (ZMod (primePowModulus p 1 : ℕ)))
        L.polarGramMatrix).symm
  rw [hdet]
  have hp_dvd_disc : (p : ℤ) ∣ L.polarDeterminant := by
    have hpow : (p : ℤ) ^ 1 ∣ L.polarDeterminant := by
      exact (padicValInt_dvd_iff (p := p) 1 L.polarDeterminant).2
        (Or.inr hval)
    simpa using hpow
  have hzero : (L.polarDeterminant : ZMod (primePowModulus p 1 : ℕ)) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    simpa [primePowModulus] using hp_dvd_disc
  rw [hzero]
  exact not_isUnit_zero

/-- Consequently no `Invertible` instance exists for the residue Gram pairing
at a bad prime. The existing theorem
`henselMatrixCorrectionQuadraticMap_surjective` requires precisely such an
instance and therefore cannot be applied to the raw bad-prime correction
problem. -/
theorem not_nonempty_invertible_polarGramMatrix_mod_prime_of_padicValInt_polarDeterminant_pos
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)]
    (hval : 0 < padicValInt p L.polarDeterminant) :
    ¬ Nonempty (Invertible (matrixMod L.polarGramMatrix (primePowModulus p 1))) := by
  rintro ⟨hA⟩
  letI := hA
  exact L.polarGramMatrix_mod_prime_not_isUnit_of_padicValInt_polarDeterminant_pos p hval
    (isUnit_of_invertible _)

end PositiveDefiniteIntegralLattice
