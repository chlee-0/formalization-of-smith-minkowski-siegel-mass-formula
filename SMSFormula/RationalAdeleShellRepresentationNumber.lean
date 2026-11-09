import SMSFormula.RationalAdeleFiniteLocalIntegralVanishing

/-!
# The rational shell is the lattice representation number

At a positive integer frequency the theta side of the frequency decomposition is the
rational shell sum.  This file identifies that sum with the arithmetic representation
number of the lattice, times the existing Gaussian shell weight.

Everything is existing: the test kills non-integral rational vectors, the polar
Gaussian is constant on a shell, and the form matrix of an `PositiveDefiniteIntegralLattice` is an integer
matrix, so the integral rational solutions of `Q(x) = m` correspond bijectively to the
integer solutions counted by the representation number.

Negative scope: this is an identification of the theta side only.  No local density is
evaluated, no Euler product is asserted, and no comparison with the cusp side is made.
-/

noncomputable section

open MeasureTheory Matrix

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- The rational quadratic value at an integer vector is the cast of the existing
integral quadratic form. -/
theorem nativeRationalQuadraticForm_intVector (L : PositiveDefiniteIntegralLattice n) (z : Fin n → ℤ) :
    L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm (fun i => (z i : ℚ)) =
      ((L.quadForm z : ℤ) : ℚ) := by
  have hrat : L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm
      (fun i => (z i : ℚ)) =
      dotProduct (fun i => (z i : ℚ))
        (L.rationalQuadraticSpaceMatrix.pairingMatrix.mulVec (fun i => (z i : ℚ))) := by
    simpa [RationalQuadraticSpaceMatrix.nativeRationalQuadraticForm,
      RationalQuadraticSpaceMatrix.quadraticForm, Matrix.toQuadraticMap']
      using Matrix.toLinearMap₂'_apply' L.rationalQuadraticSpaceMatrix.pairingMatrix
        (fun i => (z i : ℚ)) (fun i => (z i : ℚ))
  rw [hrat, L.quadForm_eq_dotProduct]
  simp only [dotProduct, Matrix.mulVec, rationalQuadraticSpaceMatrix, rationalFormMatrix,
    Matrix.map_apply, eq_intCast]
  push_cast
  ring

/-- The integral rational solutions of `Q(x) = m` are exactly the integer solutions of the
existing integral quadratic form. -/
def shellIntegralEquiv (L : PositiveDefiniteIntegralLattice n) (m : ℤ) :
    {z : Fin n → ℤ // L.quadForm z = m} ≃
      {x : {x : Fin n → ℚ //
          L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x = ((m : ℤ) : ℚ)} //
        x.1 ∈ rationalIntegralVectors n} := by
  refine Equiv.ofBijective
    (fun z => ⟨⟨fun i => ((z.1 i : ℤ) : ℚ), ?_⟩, fun i => ⟨z.1 i, by simp⟩⟩) ⟨?_, ?_⟩
  · rw [L.nativeRationalQuadraticForm_intVector z.1, z.2]
  · intro u v huv
    have h1 := congrArg (fun w => (w.1.1 : Fin n → ℚ)) huv
    refine Subtype.ext (funext fun i => ?_)
    have h2 := congrFun h1 i
    dsimp only at h2
    exact_mod_cast h2
  · intro y
    have hint2 : ∀ i, (y.1.1 : Fin n → ℚ) i ∈ Set.range (algebraMap ℤ ℚ) := y.2
    choose z hz using hint2
    have hzx : (fun i => ((z i : ℤ) : ℚ)) = (y.1.1 : Fin n → ℚ) := by
      funext i
      have hi := hz i
      simpa using hi
    refine ⟨⟨z, ?_⟩, ?_⟩
    · have hval := L.nativeRationalQuadraticForm_intVector z
      rw [hzx, y.1.2] at hval
      exact_mod_cast hval.symm
    · exact Subtype.ext (Subtype.ext hzx)

end PositiveDefiniteIntegralLattice
