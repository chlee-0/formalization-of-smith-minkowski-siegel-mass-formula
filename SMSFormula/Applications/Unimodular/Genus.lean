import SMSFormula.Applications.Unimodular.Seeds
import SMSFormula.Finiteness
import SMSFormula.LocalDensity

/-!
# Genus-level interfaces for unimodular mass applications

This file records genus and dyadic-local invariance interfaces for the basic
unimodularity and parity predicates used by the Type I/II Bernoulli
mass application.  It reuses existing determinant and p-adic local-isometry
transport theorems; it does not evaluate any local density or mass factor.
-/

noncomputable section

namespace PositiveDefiniteIntegralLattice

open BigOperators

variable {n : ℕ} {L L' : PositiveDefiniteIntegralLattice n}

/-- Classical unimodularity (`pairingDeterminant = 1`) is invariant under replacing a
lattice by another representative in the same genus. -/
theorem isUnimodular_of_isSameGenus
    (h : L.IsSameGenus L') (h' : L'.IsUnimodular) : L.IsUnimodular := by
  rw [IsUnimodular, pairingDeterminant_eq_of_isSameGenus L L' h, h']

/-- The genus of the rank-zero identity seed has only one global isometry
class.  Every rank-zero lattice is globally isometric to the identity seed. -/
theorem identityLattice_zero_genus_subsingleton :
    Subsingleton (identityLattice 0).genus := by
  refine ⟨fun C D => ?_⟩
  apply Subtype.ext
  have hC : C.1 = (identityLattice 0).globalIsometryClass := by
    rcases C.2 with ⟨M, _hM, hMC⟩
    rw [hMC]
    exact globalIsometryClass_eq_of_isGlobalIsometry
      (isGlobalIsometry_identityLattice_zero M)
  have hD : D.1 = (identityLattice 0).globalIsometryClass := by
    rcases D.2 with ⟨M, _hM, hMC⟩
    rw [hMC]
    exact globalIsometryClass_eq_of_isGlobalIsometry
      (isGlobalIsometry_identityLattice_zero M)
  rw [hC, hD]

/-- The rank-zero identity seed has one ordinary genus class. -/
theorem identityLattice_zero_genus_card :
    Fintype.card (identityLattice 0).genus = 1 := by
  haveI := identityLattice_zero_genus_subsingleton
  rw [Fintype.card_eq_one_iff]
  exact ⟨⟨(identityLattice 0).globalIsometryClass, mem_genus_self _⟩,
    fun C => Subsingleton.elim C _⟩

/-- The genus of the rank-one identity seed has only one global isometry
class.  Any same-genus representative is classically unimodular, hence the
rank-one classification in `Seeds.lean` identifies it with the identity seed. -/
theorem identityLattice_one_genus_subsingleton :
    Subsingleton (identityLattice 1).genus := by
  refine ⟨fun C D => ?_⟩
  apply Subtype.ext
  have hC : C.1 = (identityLattice 1).globalIsometryClass := by
    rcases C.2 with ⟨M, hM, hMC⟩
    rw [hMC]
    have hMu : M.IsUnimodular := by
      exact M.isUnimodular_of_isSameGenus
        (isSameGenus_symm hM) (identityLattice_isUnimodular 1)
    exact globalIsometryClass_eq_of_isGlobalIsometry
      (isGlobalIsometry_identityLattice_one_of_isUnimodular M hMu)
  have hD : D.1 = (identityLattice 1).globalIsometryClass := by
    rcases D.2 with ⟨M, hM, hMC⟩
    rw [hMC]
    have hMu : M.IsUnimodular := by
      exact M.isUnimodular_of_isSameGenus
        (isSameGenus_symm hM) (identityLattice_isUnimodular 1)
    exact globalIsometryClass_eq_of_isGlobalIsometry
      (isGlobalIsometry_identityLattice_one_of_isUnimodular M hMu)
  rw [hC, hD]

/-- The rank-one identity seed has one ordinary genus class. -/
theorem identityLattice_one_genus_card :
    Fintype.card (identityLattice 1).genus = 1 := by
  haveI := identityLattice_one_genus_subsingleton
  rw [Fintype.card_eq_one_iff]
  exact ⟨⟨(identityLattice 1).globalIsometryClass, mem_genus_self _⟩,
    fun C => Subsingleton.elim C _⟩

/-- A global classification of classically unimodular rank-two lattices
collapses the rank-two identity genus to one ordinary class. -/
theorem identityLattice_two_genus_subsingleton_of_rank_two_unimodular_classification
    (hclass : ∀ L : PositiveDefiniteIntegralLattice 2, L.IsUnimodular → L.IsGlobalIsometry (identityLattice 2)) :
    Subsingleton (identityLattice 2).genus := by
  refine ⟨fun C D => ?_⟩
  apply Subtype.ext
  have hC : C.1 = (identityLattice 2).globalIsometryClass := by
    rcases C.2 with ⟨M, hM, hMC⟩
    rw [hMC]
    have hMu : M.IsUnimodular := by
      exact M.isUnimodular_of_isSameGenus
        (isSameGenus_symm hM) (identityLattice_isUnimodular 2)
    exact globalIsometryClass_eq_of_isGlobalIsometry (hclass M hMu)
  have hD : D.1 = (identityLattice 2).globalIsometryClass := by
    rcases D.2 with ⟨M, hM, hMC⟩
    rw [hMC]
    have hMu : M.IsUnimodular := by
      exact M.isUnimodular_of_isSameGenus
        (isSameGenus_symm hM) (identityLattice_isUnimodular 2)
    exact globalIsometryClass_eq_of_isGlobalIsometry (hclass M hMu)
  rw [hC, hD]

/-- A global classification of classically unimodular rank-two lattices gives
one ordinary class in the rank-two identity genus. -/
theorem identityLattice_two_genus_card_of_rank_two_unimodular_classification
    (hclass : ∀ L : PositiveDefiniteIntegralLattice 2, L.IsUnimodular → L.IsGlobalIsometry (identityLattice 2)) :
    Fintype.card (identityLattice 2).genus = 1 := by
  haveI := identityLattice_two_genus_subsingleton_of_rank_two_unimodular_classification hclass
  rw [Fintype.card_eq_one_iff]
  exact ⟨⟨(identityLattice 2).globalIsometryClass, mem_genus_self _⟩,
    fun C => Subsingleton.elim C _⟩

/-- A Type II lattice has zero quadratic value modulo two on every `2`-adic
integral vector. -/
theorem padic_quadForm_toZModPow_one_eq_zero_of_hasEvenNorms
    (hL : L.HasEvenNorms) (v : Fin n → ℤ_[2]) :
    PadicInt.toZModPow 1
        (dotProduct v ((L.pairingMatrix_padic 2).mulVec v)) = 0 := by
  rcases exists_integralVectorToPadic_forall_primePow_dvd_sub (n := n) 2 1 v with ⟨x, hx⟩
  rw [padic_quadForm_toZModPow_eq_of_forall_primePow_dvd_sub L 2 1 v x hx]
  have hEven : Even (L.quadForm x) := hL x
  have hdiv : (2 : ℤ) ∣ L.quadForm x := even_iff_two_dvd.mp hEven
  change (L.quadForm x : ZMod 2) = 0
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
  exact hdiv

/-- Type II parity is invariant under dyadic local isometry. -/
theorem hasEvenNorms_of_isLocallyIsometricAt_two
    (h : L.IsLocallyIsometricAt L' 2) (h' : L'.HasEvenNorms) :
    L.HasEvenNorms := by
  rw [L.hasEvenNorms_iff_forall_diag_even]
  intro i
  rcases h with ⟨U, hU_unit, hU⟩
  let e : Fin n → ℤ_[2] := integralVectorToPadic (n := n) 2 (Pi.single i 1)
  have hsource :=
    padic_quadForm_toZModPow_eq_of_forall_primePow_dvd_sub L 2 1 e (Pi.single i 1)
      (by intro j; simp [e])
  rw [L.quadForm_single_one i] at hsource
  have htarget :=
    padic_quadForm_toZModPow_one_eq_zero_of_hasEvenNorms (L := L') h' (U.mulVec e)
  have hquad := congrArg (PadicInt.toZModPow 1)
    (padic_dotProduct_mulVec_eq_of_local_isometry_matrix (L₀ := L) (L₁ := L') 2 hU e e)
  rw [hsource, htarget] at hquad
  exact even_iff_two_dvd.mpr ((ZMod.intCast_zmod_eq_zero_iff_dvd (L.pairingMatrix i i) 2).mp hquad)

/-- Type II parity is invariant under replacing a lattice by a representative in
the same genus. -/
theorem hasEvenNorms_of_isSameGenus
    (h : L.IsSameGenus L') (h' : L'.HasEvenNorms) : L.HasEvenNorms := by
  exact hasEvenNorms_of_isLocallyIsometricAt_two (L := L) (L' := L') (h.1 2) h'

/-- Type I parity is invariant under replacing a lattice by a representative in
the same genus. -/
theorem hasOddNorm_of_isSameGenus
    (h : L.IsSameGenus L') (h' : L'.HasOddNorm) : L.HasOddNorm := by
  rw [← L.not_hasEvenNorms_iff_hasOddNorm]
  intro hLII
  have hsym : L'.IsSameGenus L := isSameGenus_symm h
  have hL'II := hasEvenNorms_of_isSameGenus (L := L') (L' := L) hsym hLII
  exact L'.not_hasEvenNorms_of_hasOddNorm h' hL'II

end PositiveDefiniteIntegralLattice
