import SMSFormula.Lattice
import Mathlib.NumberTheory.Padics.PadicIntegers

/-!
# Local isometry, same-genus relation, and genus

This file builds on `SMSFormula.Lattice` to define:

1. **Local scalar extensions** of a Gram matrix to `ℤ_p` (for each prime `p`)
   and to `ℝ` (the archimedean place).
2. **Local isometry** of two integral lattices at a finite prime and at
   infinity.
3. The **same-genus relation**: two lattices are in the same genus when they
   are locally isometric at every place.
4. The **genus** of a lattice `L`, defined as a set of global integral
   isometry classes, not as a raw set of based Gram matrices.

## Design notes

* The genus is defined *before* any mass or finiteness construction.
* Local isometry at a prime `p` is expressed via Gram-matrix congruence over
  `ℤ_p`: two lattices `L, L'` of the same rank are locally isometric at `p`
  when there exists an invertible matrix `U ∈ GLₙ(ℤ_p)` satisfying
  `Uᵀ F'_p U = F_p`, where `F_p` is the image of the quadratic matrix under the canonical
  ring map `ℤ → ℤ_p`.
* Local isometry at the archimedean place is the analogous condition over `ℝ`.
  For positive-definite lattices this is automatic (Sylvester), but we state
  it uniformly so that the genus definition matches the general template.

## References

* R. Schulze-Pillot, *Lecture Notes on Quadratic Forms and their Arithmetic*.
-/

open Matrix

noncomputable section

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-! ## Local scalar extensions -/

/-- The quadratic-form matrix of `L` viewed over the `p`-adic integers `ℤ_p`. -/
def pairingMatrix_padic (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    Matrix (Fin n) (Fin n) ℤ_[p] :=
  L.pairingMatrix.map (Int.cast : ℤ → ℤ_[p])

/-- The quadratic-form matrix of `L` viewed over the reals `ℝ`. -/
def pairingMatrix_real (L : PositiveDefiniteIntegralLattice n) :
    Matrix (Fin n) (Fin n) ℝ :=
  L.pairingMatrix.map (Int.cast : ℤ → ℝ)

/-! ## Local isometry at a finite prime -/

/-- Two integral lattices of the same rank are *locally isometric at `p`* when
there exists an invertible matrix `U ∈ GLₙ(ℤ_p)` satisfying
`Uᵀ F'_p U = F_p`. -/
def IsLocallyIsometricAt (L L' : PositiveDefiniteIntegralLattice n)
    (p : ℕ) [Fact (Nat.Prime p)] : Prop :=
  ∃ U : Matrix (Fin n) (Fin n) ℤ_[p],
    IsUnit U ∧ Uᵀ * L'.pairingMatrix_padic p * U = L.pairingMatrix_padic p

/-! ## Local isometry at the archimedean place -/

/-- Two integral lattices of the same rank are *locally isometric at infinity*
when there exists an invertible real matrix `U ∈ GLₙ(ℝ)` satisfying
`Uᵀ F'_ℝ U = F_ℝ`. -/
def IsLocallyIsometricAtInfinity (L L' : PositiveDefiniteIntegralLattice n) : Prop :=
  ∃ U : Matrix (Fin n) (Fin n) ℝ,
    IsUnit U ∧ Uᵀ * L'.pairingMatrix_real * U = L.pairingMatrix_real

/-! ## The same-genus relation -/

/-- Two positive-definite integral lattices of the same rank are in the
*same genus* when they are locally isometric at every finite prime `p`
and at the archimedean place. -/
def IsSameGenus (L L' : PositiveDefiniteIntegralLattice n) : Prop :=
  (∀ (p : ℕ) [Fact (Nat.Prime p)], L.IsLocallyIsometricAt L' p) ∧
    L.IsLocallyIsometricAtInfinity L'

/-! ## Basic properties of the same-genus relation -/

/-- `IsSameGenus` is reflexive. -/
theorem isSameGenus_refl (L : PositiveDefiniteIntegralLattice n) : L.IsSameGenus L := by
  constructor
  · intro p _
    exact ⟨1, isUnit_one, by simp⟩
  · exact ⟨1, isUnit_one, by simp⟩

/-- `IsSameGenus` is symmetric. -/
theorem isSameGenus_symm {L L' : PositiveDefiniteIntegralLattice n}
    (h : L.IsSameGenus L') : L'.IsSameGenus L := by
  refine' ⟨ _, _ ⟩;
  · intro p hp
    obtain ⟨U, hU_unit, hU⟩ := h.left p
    use U⁻¹;
    simp_all +decide [ Matrix.isUnit_iff_isUnit_det ];
    simp +decide [ ← hU, Matrix.mul_assoc, Matrix.transpose_nonsing_inv, hU_unit ];
  · obtain ⟨ U, hU₁, hU₂ ⟩ := h.2;
    refine' ⟨ U⁻¹, _, _ ⟩ <;> simp_all +decide [ Matrix.isUnit_iff_isUnit_det ];
    simp +decide [ ← hU₂, Matrix.mul_assoc, Matrix.transpose_nonsing_inv, hU₁ ]

/-- `IsSameGenus` is transitive. -/
theorem isSameGenus_trans {L L' L'' : PositiveDefiniteIntegralLattice n}
    (h1 : L.IsSameGenus L') (h2 : L'.IsSameGenus L'') : L.IsSameGenus L'' := by
  constructor;
  · intro p hp
    obtain ⟨U, hU⟩ := h1.1 p
    obtain ⟨V, hV⟩ := h2.1 p
    use V * U;
    simp_all +decide [ Matrix.mul_assoc, Matrix.transpose_mul ];
    simp_all +decide [ ← Matrix.mul_assoc ];
  · obtain ⟨U₁, hU₁⟩ := h1.right
    obtain ⟨U₂, hU₂⟩ := h2.right
    use U₂ * U₁;
    simp_all +decide [ Matrix.isUnit_iff_isUnit_det, Matrix.mul_assoc ];
    simp_all +decide [ ← Matrix.mul_assoc ]

/-! ## Global isometry classes and the genus -/

/-- The global integral isometry class represented by `L`, viewed as a set of
based lattices.  This avoids treating a change of integral basis as a new genus
class. -/
def globalIsometryClass (L : PositiveDefiniteIntegralLattice n) : Set (PositiveDefiniteIntegralLattice n) :=
  { L' | L.IsGlobalIsometry L' }

/-- Global integral isometry is reflexive. -/
theorem isGlobalIsometry_refl (L : PositiveDefiniteIntegralLattice n) : L.IsGlobalIsometry L := by
  exact ⟨1, isUnit_one, by simp⟩

/-- Global integral isometry is symmetric. -/
theorem isGlobalIsometry_symm {L L' : PositiveDefiniteIntegralLattice n}
    (h : L.IsGlobalIsometry L') : L'.IsGlobalIsometry L := by
  obtain ⟨U, hU_unit, hU⟩ := h
  use U⁻¹
  simp_all +decide [Matrix.isUnit_iff_isUnit_det]
  simp +decide [← hU, Matrix.mul_assoc, Matrix.transpose_nonsing_inv, hU_unit]

/-- Global integral isometry is transitive. -/
theorem isGlobalIsometry_trans {L L' L'' : PositiveDefiniteIntegralLattice n}
    (h1 : L.IsGlobalIsometry L') (h2 : L'.IsGlobalIsometry L'') :
    L.IsGlobalIsometry L'' := by
  obtain ⟨U, hU⟩ := h1
  obtain ⟨V, hV⟩ := h2
  use V * U
  simp_all +decide [Matrix.isUnit_iff_isUnit_det, Matrix.mul_assoc, Matrix.transpose_mul]
  simp_all +decide [← Matrix.mul_assoc]

/-- A global integral isometry gives a local isometry at every finite prime. -/
lemma isLocallyIsometricAt_of_isGlobalIsometry {L₀ L₁ : PositiveDefiniteIntegralLattice n}
    (h : L₀.IsGlobalIsometry L₁) (p : ℕ) [Fact (Nat.Prime p)] :
    L₀.IsLocallyIsometricAt L₁ p := by
  rcases h with ⟨U, hU_unit, hU⟩
  refine ⟨U.map (Int.castRingHom ℤ_[p]), ?_, ?_⟩
  · exact hU_unit.map (Int.castRingHom ℤ_[p]).mapMatrix
  · change (U.map (Int.castRingHom ℤ_[p])).transpose *
        (L₁.pairingMatrix.map (Int.castRingHom ℤ_[p])) *
        (U.map (Int.castRingHom ℤ_[p])) =
        L₀.pairingMatrix.map (Int.castRingHom ℤ_[p])
    have hmap := congrArg (fun M => M.map (Int.castRingHom ℤ_[p])) hU
    change ((U.transpose * L₁.pairingMatrix * U).map (Int.castRingHom ℤ_[p])) =
        L₀.pairingMatrix.map (Int.castRingHom ℤ_[p]) at hmap
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map] at hmap
    simpa [Matrix.mul_assoc] using hmap

/-- A global integral isometry gives an archimedean local isometry. -/
lemma isLocallyIsometricAtInfinity_of_isGlobalIsometry {L₀ L₁ : PositiveDefiniteIntegralLattice n}
    (h : L₀.IsGlobalIsometry L₁) :
    L₀.IsLocallyIsometricAtInfinity L₁ := by
  rcases h with ⟨U, hU_unit, hU⟩
  refine ⟨U.map (Int.castRingHom ℝ), ?_, ?_⟩
  · exact hU_unit.map (Int.castRingHom ℝ).mapMatrix
  · change (U.map (Int.castRingHom ℝ)).transpose *
        (L₁.pairingMatrix.map (Int.castRingHom ℝ)) *
        (U.map (Int.castRingHom ℝ)) =
        L₀.pairingMatrix.map (Int.castRingHom ℝ)
    have hmap := congrArg (fun M => M.map (Int.castRingHom ℝ)) hU
    change ((U.transpose * L₁.pairingMatrix * U).map (Int.castRingHom ℝ)) =
        L₀.pairingMatrix.map (Int.castRingHom ℝ) at hmap
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map] at hmap
    simpa [Matrix.mul_assoc] using hmap

/-- Globally isometric lattices are in the same genus. -/
lemma isSameGenus_of_isGlobalIsometry {L₀ L₁ : PositiveDefiniteIntegralLattice n}
    (h : L₀.IsGlobalIsometry L₁) : L₀.IsSameGenus L₁ := by
  constructor
  · intro p hp
    exact isLocallyIsometricAt_of_isGlobalIsometry h p
  · exact isLocallyIsometricAtInfinity_of_isGlobalIsometry h

/-- Globally isometric representatives define the same global isometry class. -/
lemma globalIsometryClass_eq_of_isGlobalIsometry {L L' : PositiveDefiniteIntegralLattice n}
    (h : L.IsGlobalIsometry L') : L.globalIsometryClass = L'.globalIsometryClass := by
  ext M
  constructor
  · intro hM
    exact isGlobalIsometry_trans (isGlobalIsometry_symm h) hM
  · intro hM
    exact isGlobalIsometry_trans h hM

/-- Equality of global integral isometry classes gives a global isometry
between their representatives. -/
lemma isGlobalIsometry_of_globalIsometryClass_eq {L L' : PositiveDefiniteIntegralLattice n}
    (h : L.globalIsometryClass = L'.globalIsometryClass) : L.IsGlobalIsometry L' := by
  have hmem : L' ∈ L.globalIsometryClass := by
    rw [h]
    exact L'.isGlobalIsometry_refl
  exact hmem

/-- The representative belongs to its own global integral isometry class. -/
lemma mem_globalIsometryClass_self (L : PositiveDefiniteIntegralLattice n) :
    L ∈ L.globalIsometryClass := by
  exact L.isGlobalIsometry_refl

/-- Every lattice in a global integral isometry class has the same
Schulze--Pillot determinant `det_B = det(F)` as the representative. -/
lemma pairingDeterminant_eq_of_mem_globalIsometryClass {L L' : PositiveDefiniteIntegralLattice n}
    (h : L' ∈ L.globalIsometryClass) : L.pairingDeterminant = L'.pairingDeterminant := by
  exact pairingDeterminant_eq_of_isGlobalIsometry h

/-- The raw set of based lattices locally isometric to `L`.  This is useful as
an auxiliary object, but it is not the genus class set used in the mass
formula. -/
def genusLattices (L : PositiveDefiniteIntegralLattice n) : Set (PositiveDefiniteIntegralLattice n) :=
  { L' | L.IsSameGenus L' }

/-- The **genus** of an integral lattice `L` is the set of global integral
isometry classes represented by lattices locally isometric to `L`.

The genus is defined as a plain `Set`
*before* any finiteness or mass construction. -/
def genus (L : PositiveDefiniteIntegralLattice n) : Set (Set (PositiveDefiniteIntegralLattice n)) :=
  { C | ∃ L' : PositiveDefiniteIntegralLattice n, L.IsSameGenus L' ∧ C = L'.globalIsometryClass }

/-- The global isometry class of `L` belongs to the genus of `L`. -/
theorem mem_genus_self (L : PositiveDefiniteIntegralLattice n) : L.globalIsometryClass ∈ L.genus :=
  ⟨L, L.isSameGenus_refl, rfl⟩

end PositiveDefiniteIntegralLattice

end
