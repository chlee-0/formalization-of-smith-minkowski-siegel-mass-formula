import SMSFormula.IntegralQuadraticFormBridge
import SMSFormula.Mass
import Mathlib.NumberTheory.Padics.RingHoms

/-!
# Direct genus classes and ordinary mass of based integral quadratic forms

The genus index uses direct global isometry classes in the direct genus of Q.
The ordinary mass sums reciprocal full-O orders over those classes. The proofs
of finiteness and comparison reuse the lattice of the polar form. Reconstruction
requires even diagonal, not entrywise evenness. This theory is generic in Q.
-/

open Matrix

noncomputable section

namespace PositiveDefiniteIntegralQuadraticForm

variable {n : ℕ}

theorem even_pairingMatrix_diag_of_latticeOfPolarForm_local_two
    (H : PositiveDefiniteIntegralQuadraticForm n) (M : PositiveDefiniteIntegralLattice n)
    (h : H.latticeOfPolarForm.IsLocallyIsometricAt M 2) :
    ∀ i, Even (M.pairingMatrix i i) := by
  rcases h with ⟨U, hUunit, hU⟩
  have hUdet : IsUnit U.det := by
    rwa [Matrix.isUnit_iff_isUnit_det] at hUunit
  have hinv : U * U⁻¹ = 1 := Matrix.mul_nonsing_inv U hUdet
  have hleft : (U⁻¹).transpose * U.transpose = 1 := by
    rw [← Matrix.transpose_mul, hinv, Matrix.transpose_one]
  let C := H.quadraticCoefficientMatrix.map (Int.cast : ℤ → ℤ_[2])
  have hpolar : C + C.transpose = H.latticeOfPolarForm.pairingMatrix_padic 2 := by
    ext i j
    have hij := congr_fun₂ H.quadraticCoefficientMatrix_add_transpose i j
    have hc := congrArg (Int.cast : ℤ → ℤ_[2]) hij
    simpa [C, PositiveDefiniteIntegralLattice.pairingMatrix_padic, latticeOfPolarForm] using hc
  let D := (U⁻¹).transpose * C * U⁻¹
  have hsolve : M.pairingMatrix_padic 2 = D + D.transpose := by
    calc
      M.pairingMatrix_padic 2 =
          (U⁻¹).transpose * (U.transpose * M.pairingMatrix_padic 2 * U) * U⁻¹ := by
        simp [Matrix.mul_assoc, ← Matrix.mul_assoc (U⁻¹).transpose U.transpose,
          hleft, hinv]
      _ = (U⁻¹).transpose * (C + C.transpose) * U⁻¹ := by rw [hU, hpolar]
      _ = D + D.transpose := by
        simp [D, Matrix.mul_add, Matrix.add_mul, Matrix.transpose_mul, Matrix.mul_assoc]
  intro i
  have hi := congr_fun₂ hsolve i i
  have hz : (M.pairingMatrix i i : ZMod 2) = 0 := by
    have he := congrArg PadicInt.toZMod hi
    have he' : (M.pairingMatrix i i : ZMod 2) = 2 * PadicInt.toZMod (D i i) := by
      simpa [PositiveDefiniteIntegralLattice.pairingMatrix_padic, two_mul] using he
    simpa only [show (2 : ZMod 2) = 0 by decide, zero_mul] using he'
  exact even_iff_two_dvd.mpr ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hz)

end PositiveDefiniteIntegralQuadraticForm

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

def integralQuadraticFormOfEvenDiagonal (M : PositiveDefiniteIntegralLattice n)
    (heven : ∀ i, Even (M.pairingMatrix i i)) : PositiveDefiniteIntegralQuadraticForm n where
  polarGramMatrix := M.pairingMatrix
  polarGram_symm := M.form_symm
  polarGram_even_diag := heven
  polarGram_posDef := M.form_posDef

theorem latticeOfPolarForm_integralQuadraticFormOfEvenDiagonal
    (M : PositiveDefiniteIntegralLattice n) (heven : ∀ i, Even (M.pairingMatrix i i)) :
    (M.integralQuadraticFormOfEvenDiagonal heven).latticeOfPolarForm = M := by
  rfl

end PositiveDefiniteIntegralLattice

namespace PositiveDefiniteIntegralQuadraticForm

variable {n : ℕ}

theorem exists_sameGenus_latticeOfPolarForm_eq
    (H : PositiveDefiniteIntegralQuadraticForm n) (M : PositiveDefiniteIntegralLattice n)
    (h : H.latticeOfPolarForm.IsSameGenus M) :
    ∃ H' : PositiveDefiniteIntegralQuadraticForm n, H.IsSameGenus H' ∧ H'.latticeOfPolarForm = M := by
  let H' := M.integralQuadraticFormOfEvenDiagonal
    (even_pairingMatrix_diag_of_latticeOfPolarForm_local_two H M (h.1 2))
  have heq : H'.latticeOfPolarForm = M := rfl
  exact ⟨H', (H.isSameGenus_iff_latticeOfPolarForm H').mpr (heq ▸ h), heq⟩

def globalIsometryClass (H : PositiveDefiniteIntegralQuadraticForm n) :
    Set (PositiveDefiniteIntegralQuadraticForm n) := {H' | H.IsGlobalIsometry H'}

theorem globalIsometryClass_eq_iff (H H' : PositiveDefiniteIntegralQuadraticForm n) :
    H.globalIsometryClass = H'.globalIsometryClass ↔
      H.IsGlobalIsometry H' := by
  constructor
  · intro heq
    have hmem : H' ∈ H.globalIsometryClass := by
      rw [heq]
      exact H'.latticeOfPolarForm.isGlobalIsometry_refl
    exact hmem
  · intro h
    have hs := PositiveDefiniteIntegralLattice.globalIsometryClass_eq_of_isGlobalIsometry
      ((H.isGlobalIsometry_iff_latticeOfPolarForm H').mp h)
    ext J
    exact Iff.of_eq (congrArg (fun S => J.latticeOfPolarForm ∈ S) hs)

/-- This index uses the direct Q relations, independently of the integral model genus. -/
def genus (H : PositiveDefiniteIntegralQuadraticForm n) :
    Set (Set (PositiveDefiniteIntegralQuadraticForm n)) :=
  {C | ∃ H', H.IsSameGenus H' ∧ C = H'.globalIsometryClass}

def genusClassRepresentative (H : PositiveDefiniteIntegralQuadraticForm n) (C : H.genus) :
    PositiveDefiniteIntegralQuadraticForm n := Classical.choose C.property

theorem genusClassRepresentative_spec (H : PositiveDefiniteIntegralQuadraticForm n)
    (C : H.genus) :
    H.IsSameGenus (H.genusClassRepresentative C) ∧
      C.1 = (H.genusClassRepresentative C).globalIsometryClass :=
  Classical.choose_spec C.property

def genusToPolarFormLattice (H : PositiveDefiniteIntegralQuadraticForm n) (C : H.genus) :
    H.latticeOfPolarForm.genus :=
  ⟨(H.genusClassRepresentative C).latticeOfPolarForm.globalIsometryClass,
    (H.genusClassRepresentative C).latticeOfPolarForm,
    (H.genusClassRepresentative_spec C).1, rfl⟩

theorem genusToPolarFormLattice_injective (H : PositiveDefiniteIntegralQuadraticForm n) :
    Function.Injective H.genusToPolarFormLattice := by
  intro C D h
  have hs := congrArg Subtype.val h
  have hiso := PositiveDefiniteIntegralLattice.isGlobalIsometry_of_globalIsometryClass_eq hs
  apply Subtype.ext
  calc
    C.1 = (H.genusClassRepresentative C).globalIsometryClass :=
      (H.genusClassRepresentative_spec C).2
    _ = (H.genusClassRepresentative D).globalIsometryClass :=
      (globalIsometryClass_eq_iff _ _).mpr hiso
    _ = D.1 := (H.genusClassRepresentative_spec D).2.symm

theorem genusToPolarFormLattice_surjective (H : PositiveDefiniteIntegralQuadraticForm n) :
    Function.Surjective H.genusToPolarFormLattice := by
  intro D
  let M := PositiveDefiniteIntegralLattice.genusClassRepresentative H.latticeOfPolarForm D
  obtain ⟨J, hJ, heq⟩ := H.exists_sameGenus_latticeOfPolarForm_eq M
    (PositiveDefiniteIntegralLattice.genusClassRepresentative_isSameGenus _ D)
  let C : H.genus := ⟨J.globalIsometryClass, J, hJ, rfl⟩
  refine ⟨C, Subtype.ext ?_⟩
  have hclass : J.globalIsometryClass =
      (H.genusClassRepresentative C).globalIsometryClass :=
    (H.genusClassRepresentative_spec C).2
  have hiso := (globalIsometryClass_eq_iff _ _).mp hclass
  have hs := PositiveDefiniteIntegralLattice.globalIsometryClass_eq_of_isGlobalIsometry
    ((J.isGlobalIsometry_iff_latticeOfPolarForm _).mp hiso)
  change (H.genusClassRepresentative C).latticeOfPolarForm.globalIsometryClass = D.1
  rw [← hs, heq]
  exact (PositiveDefiniteIntegralLattice.genusClassRepresentative_globalIsometryClass _ D).symm

def genusEquivPolarFormLattice (H : PositiveDefiniteIntegralQuadraticForm n) :
    H.genus ≃ H.latticeOfPolarForm.genus :=
  Equiv.ofBijective H.genusToPolarFormLattice
    ⟨H.genusToPolarFormLattice_injective, H.genusToPolarFormLattice_surjective⟩

instance genusFintype (H : PositiveDefiniteIntegralQuadraticForm n) : Fintype H.genus :=
  Fintype.ofEquiv H.latticeOfPolarForm.genus H.genusEquivPolarFormLattice.symm

instance isometryGroup_fintype (H : PositiveDefiniteIntegralQuadraticForm n) :
    Fintype H.IsometryGroup :=
  Fintype.ofEquiv H.latticeOfPolarForm.IsometryGroup
    H.isometryGroupEquivLatticeOfPolarForm.symm

/-- The direct Q genus class sum with full orthogonal-group weights. -/
def ordinaryGenusMass (H : PositiveDefiniteIntegralQuadraticForm n) : ℚ :=
  ∑ C : H.genus,
    (Fintype.card (H.genusClassRepresentative C).IsometryGroup : ℚ)⁻¹

theorem ordinaryGenusMass_eq_latticeOfPolarForm (H : PositiveDefiniteIntegralQuadraticForm n) :
    H.ordinaryGenusMass = H.latticeOfPolarForm.ordinaryGenusMass := by
  classical
  unfold ordinaryGenusMass PositiveDefiniteIntegralLattice.ordinaryGenusMass
  refine Fintype.sum_equiv H.genusEquivPolarFormLattice _ _ ?_
  intro C
  let R := H.genusClassRepresentative C
  let S := PositiveDefiniteIntegralLattice.genusClassRepresentative H.latticeOfPolarForm
    (H.genusEquivPolarFormLattice C)
  have hclass : R.latticeOfPolarForm.globalIsometryClass = S.globalIsometryClass :=
    PositiveDefiniteIntegralLattice.genusClassRepresentative_globalIsometryClass _
      (H.genusEquivPolarFormLattice C)
  have hiso := PositiveDefiniteIntegralLattice.isGlobalIsometry_of_globalIsometryClass_eq hclass
  change (Fintype.card R.IsometryGroup : ℚ)⁻¹ = (Fintype.card S.IsometryGroup : ℚ)⁻¹
  rw [Fintype.card_congr R.isometryGroupEquivLatticeOfPolarForm,
    PositiveDefiniteIntegralLattice.isometryGroup_card_eq_of_isGlobalIsometry hiso]

end PositiveDefiniteIntegralQuadraticForm
