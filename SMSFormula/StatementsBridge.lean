import SMSFormula.Mass
import SMSFormula.Statements

/-!
# From the library to the statements in Mathlib terms

The definitions of `SMSFormula.Statements` restate the library's lattices, genus,
isometry groups and masses in Mathlib terms. This file proves that they agree:
`mass_eq_sum` computes the mass of an isometry-invariant family of lattices from
any complete list of class representatives, and `genusMass_pairingMatrix`
identifies `genusMass` with `ordinaryGenusMass`.
-/

open SMSFormula.Statements

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- The lattice with Gram matrix `G`. -/
def ofGram (G : Matrix (Fin n) (Fin n) ℤ) (hG : IsPosDefGram G) :
    PositiveDefiniteIntegralLattice n :=
  ⟨G, hG.1, hG.2⟩

theorem isPosDefGram (L : PositiveDefiniteIntegralLattice n) : IsPosDefGram L.pairingMatrix :=
  ⟨L.form_symm, L.form_posDef⟩

theorem isometric_iff (L L' : PositiveDefiniteIntegralLattice n) :
    Isometric L.pairingMatrix L'.pairingMatrix ↔ L.IsGlobalIsometry L' :=
  Iff.rfl

theorem sameGenus_iff (L L' : PositiveDefiniteIntegralLattice n) :
    SameGenus L.pairingMatrix L'.pairingMatrix ↔ L.IsSameGenus L' :=
  Iff.rfl

theorem natCard_isometryGroup_pairingMatrix (L : PositiveDefiniteIntegralLattice n) :
    Nat.card (SMSFormula.Statements.IsometryGroup L.pairingMatrix) = Fintype.card L.IsometryGroup := by
  change Nat.card L.IsometryGroup = _
  exact Nat.card_eq_fintype_card

/-- An integral matrix congruent to a positive-definite Gram matrix by an
invertible integral matrix is again a positive-definite Gram matrix. -/
theorem isPosDefGram_of_isometric (L : PositiveDefiniteIntegralLattice n)
    {G : Matrix (Fin n) (Fin n) ℤ} (h : Isometric G L.pairingMatrix) : IsPosDefGram G := by
  obtain ⟨U, hU, rfl⟩ := h
  refine ⟨by simp [Matrix.IsSymm, Matrix.transpose_mul, L.form_symm.eq, Matrix.mul_assoc], ?_⟩
  have hcast : (Int.cast : ℤ → ℝ) = ⇑(Int.castRingHom ℝ) := rfl
  have hdet : IsUnit (U.map (Int.castRingHom ℝ)).det := by
    rw [show U.map (Int.castRingHom ℝ) = (Int.castRingHom ℝ).mapMatrix U from rfl,
      ← RingHom.map_det]
    exact ((Matrix.isUnit_iff_isUnit_det U).mp hU).map _
  have hinj : Function.Injective (U.map (Int.castRingHom ℝ)).mulVec :=
    Matrix.mulVec_injective_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det _).mpr hdet)
  have := L.form_posDef.conjTranspose_mul_mul_same hinj
  rw [hcast, Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map]
  rw [Matrix.conjTranspose_eq_transpose_of_trivial] at this
  exact this

/-- The mass of an isometry-invariant family `P` of lattices, computed from a
complete list `rep` of pairwise non-isometric representatives. -/
theorem mass_eq_sum {ι : Type*} [Fintype ι] (P : Matrix (Fin n) (Fin n) ℤ → Prop)
    (rep : ι → PositiveDefiniteIntegralLattice n)
    (hP : ∀ i, P (rep i).pairingMatrix)
    (hinj : ∀ i j, (rep i).IsGlobalIsometry (rep j) → i = j)
    (hsurj : ∀ L : PositiveDefiniteIntegralLattice n, P L.pairingMatrix →
      ∃ i, (rep i).IsGlobalIsometry L) :
    Finite (IsometryClasses P) ∧
      mass P = ∑ i, ((Fintype.card (rep i).IsometryGroup : ℚ))⁻¹ := by
  classical
  let toClass : ι → IsometryClasses P := fun i =>
    Quotient.mk _ ⟨(rep i).pairingMatrix, (rep i).isPosDefGram, hP i⟩
  have hbij : Function.Bijective toClass := by
    refine ⟨fun i j h => hinj i j (Quotient.exact h), fun C => ?_⟩
    induction C using Quotient.inductionOn with
    | h G =>
      obtain ⟨i, hi⟩ := hsurj (ofGram G.1 G.2.1) G.2.2
      exact ⟨i, Quotient.sound hi⟩
  let e := Equiv.ofBijective toClass hbij
  refine ⟨Finite.of_equiv ι e, ?_⟩
  rw [mass, ← finsum_comp_equiv e, finsum_eq_sum_of_fintype]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hout : Isometric (Quotient.out (toClass i)).1 (rep i).pairingMatrix :=
    Quotient.mk_out (s := Setoid.comap
      (fun G : { G // IsPosDefGram G ∧ P G } => G.1) ⟨Isometric, isometric_equivalence⟩)
      ⟨(rep i).pairingMatrix, (rep i).isPosDefGram, hP i⟩
  let M := ofGram (Quotient.out (toClass i)).1 (Quotient.out (toClass i)).2.1
  have hcard : Nat.card (SMSFormula.Statements.IsometryGroup (Quotient.out (toClass i)).1) =
      Fintype.card (rep i).IsometryGroup := by
    rw [show (Quotient.out (toClass i)).1 = M.pairingMatrix from rfl,
      natCard_isometryGroup_pairingMatrix]
    exact isometryGroup_card_eq_of_isGlobalIsometry (L₀ := M) hout
  show ((Nat.card (SMSFormula.Statements.IsometryGroup (Quotient.out (toClass i)).1) : ℚ))⁻¹ = _
  rw [hcard]

/-- `genusMass` of the Gram matrix of `L` is the library's ordinary genus mass,
and the genus has finitely many classes. -/
theorem genusMass_pairingMatrix (L : PositiveDefiniteIntegralLattice n) :
    Finite (IsometryClasses (SameGenus L.pairingMatrix)) ∧
      genusMass L.pairingMatrix = L.ordinaryGenusMass := by
  classical
  have h := mass_eq_sum (ι := L.genus) (SameGenus L.pairingMatrix)
    (genusClassRepresentative L)
    (fun C => genusClassRepresentative_isSameGenus L C)
    (fun C D hCD => Subtype.ext (by
      rw [genusClassRepresentative_globalIsometryClass L C,
        genusClassRepresentative_globalIsometryClass L D]
      exact globalIsometryClass_eq_of_isGlobalIsometry hCD))
    (fun L' hL' => by
      let C : L.genus := ⟨L'.globalIsometryClass, L', hL', rfl⟩
      refine ⟨C, isGlobalIsometry_of_globalIsometryClass_eq ?_⟩
      exact (genusClassRepresentative_globalIsometryClass L C).symm)
  exact ⟨h.1, h.2⟩

/-- Globally isometric Gram matrices have the same `genusMass`. -/
theorem genusMass_eq_of_isGlobalIsometry {L L' : PositiveDefiniteIntegralLattice n}
    (h : L.IsGlobalIsometry L') : genusMass L.pairingMatrix = genusMass L'.pairingMatrix := by
  rw [(genusMass_pairingMatrix L).2, (genusMass_pairingMatrix L').2,
    ordinaryGenusMass_eq_of_isGlobalIsometry h]

/-- If `G` is integrally isometric to the Gram matrix of `L`, then the genus of `G`
has finitely many classes and its mass is the ordinary genus mass of `L`. -/
theorem genusMass_of_isometric (L : PositiveDefiniteIntegralLattice n)
    {G : Matrix (Fin n) (Fin n) ℤ} (h : Isometric G L.pairingMatrix) :
    Finite (IsometryClasses (SameGenus G)) ∧ genusMass G = L.ordinaryGenusMass := by
  let M := ofGram G (isPosDefGram_of_isometric L h)
  have hM := genusMass_pairingMatrix M
  exact ⟨hM.1, hM.2.trans (ordinaryGenusMass_eq_of_isGlobalIsometry (L₀ := M) h)⟩

end PositiveDefiniteIntegralLattice
