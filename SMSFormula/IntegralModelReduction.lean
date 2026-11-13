import SMSFormula.MatrixReductionPhase
import Mathlib.Algebra.Ring.IsFormallyReal

/-!
# The integral model, recognized on the lattice's own Gram matrix

`FiniteQuadraticSumModulusBound` bounds the squared modulus of a quadratic character sum by
`q^n |det H|^n`, where `H` is an integer matrix with `B + B = H.map Int.cast`.  That hypothesis is
the bound's integral model, and this file discharges it -- by recognition, not construction.

The mechanism is that reduction is a ring map on entries, so an adelic matrix that is the diagonal
image of an integer matrix reduces to that integer matrix read in `ZMod m`, and the double of the
reduction is the reduction of the double.  Nothing adelic survives the statement.

The recognition: the repository's `finiteAdelicFormMatrix` is the diagonal image of the lattice's
`pairingMatrix`, and the integer matrix modelling `B + B` is then the lattice's own `polarGramMatrix`
`F + Fᵀ = 2F`, whose determinant is the lattice's own `polarDeterminant`, already proved positive.  So the
bound's constant is `|polarDeterminant L|^n` with no new arithmetic invariant introduced.

Negative scope.  This supplies one of the modulus bound's two remaining hypotheses.  Injectivity of
the residue character is not supplied and does not follow: by the zero-frequency negative recorded
for the phase step, the trivial character satisfies every condition here and gives no decay at all.
No Gauss sum is evaluated, and the bound remains an inequality.
-/

namespace PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase

open SMSFormula.QuadraticPhaseDescent SMSFormula.FiniteQuadraticSum Matrix

variable {n : ℕ}

/-! ## An integer entry reduces to its own residue -/

/-- The two integer embeddings agree: the finite-adelic diagonal of an integer is the image of the
integer under the ring's own structure map. -/
theorem algebraMap_int_eq_coe_integerToIntegralFiniteAdele (z : ℤ) :
    algebraMap ℤ RationalFiniteAdele z =
      ((integerToIntegralFiniteAdele z : IntegralFiniteAdele) : RationalFiniteAdele) := by
  rw [integerToIntegralFiniteAdele_coe]
  simp

/-- Hence an integer diagonal is integral. -/
theorem algebraMap_int_mem_integralFiniteAdeleSubring (z : ℤ) :
    algebraMap ℤ RationalFiniteAdele z ∈ integralFiniteAdeleSubring := by
  rw [algebraMap_int_eq_coe_integerToIntegralFiniteAdele z]
  exact (integerToIntegralFiniteAdele z).property

/-- And its residue is the integer's own residue class. -/
theorem ringResidueOf_algebraMap_int (m : ℕ) (hm : m ≠ 0) (z : ℤ)
    (hz : algebraMap ℤ RationalFiniteAdele z ∈ integralFiniteAdeleSubring) :
    ringResidueOf m hm ⟨algebraMap ℤ RationalFiniteAdele z, hz⟩ = (z : ZMod m) := by
  have hlift : toIntegral (⟨algebraMap ℤ RationalFiniteAdele z, hz⟩ :
      integralFiniteAdeleSubring) = integerToIntegralFiniteAdele z :=
    Subtype.ext (algebraMap_int_eq_coe_integerToIntegralFiniteAdele z)
  show residueOf m hm (toIntegral ⟨algebraMap ℤ RationalFiniteAdele z, hz⟩) = _
  rw [hlift]
  exact residueOf_integerToIntegralFiniteAdele hm z

/-! ## The integral model -/

/-- The diagonal image of an integer matrix in the finite adeles. -/
noncomputable def integralModelMatrix (H : Matrix (Fin n) (Fin n) ℤ) :
    Matrix (Fin n) (Fin n) RationalFiniteAdele :=
  H.map (algebraMap ℤ RationalFiniteAdele)

/-- Its entries are integral. -/
theorem integralModelMatrix_mem (H : Matrix (Fin n) (Fin n) ℤ) (i j : Fin n) :
    integralModelMatrix H i j ∈ integralFiniteAdeleSubring :=
  algebraMap_int_mem_integralFiniteAdeleSubring (H i j)

/-- And it reduces to the integer matrix read in `ZMod m`. -/
theorem reducedMatrix_integralModelMatrix (m : ℕ) (hm : m ≠ 0)
    (H : Matrix (Fin n) (Fin n) ℤ) :
    reducedMatrix m hm (integralModelMatrix H) (integralModelMatrix_mem H) =
      H.map (Int.cast : ℤ → ZMod m) := by
  ext i j
  show ringResidueOf m hm ⟨integralModelMatrix H i j, integralModelMatrix_mem H i j⟩ = _
  exact ringResidueOf_algebraMap_int m hm (H i j) _

/-- The double of the reduction is the reduction of the double -- the bound's hypothesis shape. -/
theorem reducedMatrix_add_self_integralModelMatrix (m : ℕ) (hm : m ≠ 0)
    (H : Matrix (Fin n) (Fin n) ℤ) :
    reducedMatrix m hm (integralModelMatrix H) (integralModelMatrix_mem H) +
        reducedMatrix m hm (integralModelMatrix H) (integralModelMatrix_mem H) =
      (H + H).map (Int.cast : ℤ → ZMod m) := by
  rw [reducedMatrix_integralModelMatrix]
  ext i j
  simp [Matrix.map_apply]

/-- The double's determinant is `2^n` times the original's. -/
theorem det_add_self (H : Matrix (Fin n) (Fin n) ℤ) :
    (H + H).det = 2 ^ n * H.det := by
  have hsmul : H + H = (2 : ℤ) • H := by
    ext i j; simp [two_mul]
  rw [hsmul, Matrix.det_smul]
  simp

/-- SO nonsingularity transports. -/
theorem det_add_self_ne_zero {H : Matrix (Fin n) (Fin n) ℤ} (hdet : H.det ≠ 0) :
    (H + H).det ≠ 0 := by
  rw [det_add_self]
  exact mul_ne_zero (pow_ne_zero _ (by norm_num)) hdet

/-! ## The bound, with the integral model discharged -/

/-- The modulus bound at an integral model: for the reduction of the diagonal image of a symmetric
nonsingular integer matrix, the squared modulus of the character sum is at most
`m^n |det (H + H)|^n`, with no hypothesis on the adelic side left. -/
theorem norm_sq_sum_char_reducedMatrix_le (m : ℕ) (hm : m ≠ 0) [NeZero m]
    {psi : AddChar (ZMod m) ℂ} (hpsi : Function.Injective psi)
    {H : Matrix (Fin n) (Fin n) ℤ} (hsymm : H.IsSymm) (hdet : H.det ≠ 0)
    (l : Fin n → ZMod m) (c : ZMod m) :
    ‖∑ w : Fin n → ZMod m,
        psi (affineQuadratic
          (reducedMatrix m hm (integralModelMatrix H) (integralModelMatrix_mem H)) l c w)‖ ^ 2 ≤
      (m : ℝ) ^ n * (((H + H).det.natAbs : ℝ)) ^ n := by
  have hBsymm : (reducedMatrix m hm (integralModelMatrix H)
      (integralModelMatrix_mem H)).IsSymm := by
    refine reducedMatrix_isSymm m hm (integralModelMatrix_mem H) ?_
    intro i j
    show algebraMap ℤ RationalFiniteAdele (H i j) = algebraMap ℤ RationalFiniteAdele (H j i)
    rw [hsymm.apply j i]
  have hkey := norm_sq_sum_char_affineQuadratic_le_det_pow (q := m) (m := Fin n) hpsi hBsymm l c
    (H := H + H) (det_add_self_ne_zero hdet) (reducedMatrix_add_self_integralModelMatrix m hm H)
  simpa using hkey

/-! ## The recognition on the repository's own lattice -/

/-- The finite-adelic form matrix is the diagonal image of the lattice's form matrix -- the
recognition, definitional. -/
theorem finiteAdelicFormMatrix_eq_integralModelMatrix (L : PositiveDefiniteIntegralLattice n) :
    L.finiteAdelicFormMatrix = integralModelMatrix L.pairingMatrix :=
  rfl

/-- And the integer matrix modelling `B + B` is the lattice's own Gram matrix. -/
theorem polarGramMatrix_eq_pairingMatrix_add_self (L : PositiveDefiniteIntegralLattice n) :
    L.polarGramMatrix = L.pairingMatrix + L.pairingMatrix := by
  rw [L.polarGramMatrix_eq_two_smul_pairingMatrix]
  ext i j
  simp [two_mul]

/-- The lattice's discriminant is nonzero. -/
theorem polarDeterminant_ne_zero (L : PositiveDefiniteIntegralLattice n) : L.polarDeterminant ≠ 0 :=
  ne_of_gt L.polarDeterminant_pos

/-- The payoff: for the lattice's own form matrix the modulus bound holds with constant the
lattice's own discriminant, `‖sum‖^2 ≤ m^n |polarDeterminant L|^n`. -/
theorem norm_sq_sum_char_lattice_le (L : PositiveDefiniteIntegralLattice n) (m : ℕ) (hm : m ≠ 0) [NeZero m]
    {psi : AddChar (ZMod m) ℂ} (hpsi : Function.Injective psi)
    (l : Fin n → ZMod m) (c : ZMod m) :
    ‖∑ w : Fin n → ZMod m,
        psi (affineQuadratic
          (reducedMatrix m hm (integralModelMatrix L.pairingMatrix)
            (integralModelMatrix_mem L.pairingMatrix)) l c w)‖ ^ 2 ≤
      (m : ℝ) ^ n * ((L.polarDeterminant.natAbs : ℝ)) ^ n := by
  have hdet : L.pairingMatrix.det ≠ 0 := by
    have := L.pairingDeterminant_pos
    simpa [PositiveDefiniteIntegralLattice.pairingDeterminant] using ne_of_gt this
  have hkey := norm_sq_sum_char_reducedMatrix_le (n := n) m hm hpsi L.form_symm hdet l c
  rwa [show L.pairingMatrix + L.pairingMatrix = L.polarGramMatrix from
    (polarGramMatrix_eq_pairingMatrix_add_self L).symm,
    show L.polarGramMatrix.det = L.polarDeterminant from rfl] at hkey

end PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase
