import SMSFormula.RationalAdeleRankOneBruhatSummability

/-!
# The convergent specialized rational rank-one Eisenstein--Siegel functional

This file forms the first lawful rational cusp sum from the already proved
absolute summability of the concrete Bruhat family.  The affine-cusp model
of `P¹(ℚ)` is the literal disjoint union `Unit ⊕ ℚ`: the left point is
infinity and the right points are the finite Bruhat parameters.

The general definition is convergence-certified: it takes a proof that its
finite Bruhat family is summable.  Thus no value is assigned through Lean's
convention for a nonsummable `tsum`.  The polar Gaussian--lattice
specialization obtains that certificate from the rank-at-least-five theorem.

We also prove the rational unipotent generator identity by translating the
finite affine coordinate.  No Weyl invariance, comparison with the normalized
Spin theta functional, generic Weil representation, or Siegel--Weil theorem
is asserted here.
-/

noncomputable section

open PositiveDefiniteIntegralLattice

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

/-- The affine-cusp model `{∞} ∪ ℚ` of the rational projective line.  The
left `Unit` point is infinity and the right summand is the finite chart. -/
abbrev RationalRankOneProjectiveCusp := Unit ⊕ ℚ

/-- The specialized Eisenstein--Siegel summand on the literal rational cusp
index.  Its infinity value is exactly `Phi 0`; its finite value at `t` is the
already defined `w n(t)` Bruhat coefficient. -/
def rationalAdeleRankOneEisensteinSiegelSummand
    (V : RationalQuadraticSpaceMatrix n)
    (Phi : (Fin n → RationalAdele) → ℂ) :
    RationalRankOneProjectiveCusp → ℂ :=
  Sum.elim (fun _ => Phi 0) (V.rationalAdeleRankOneBruhatCoefficient Phi)

@[simp]
theorem rationalAdeleRankOneEisensteinSiegelSummand_infinity
    (V : RationalQuadraticSpaceMatrix n)
    (Phi : (Fin n → RationalAdele) → ℂ) :
    V.rationalAdeleRankOneEisensteinSiegelSummand Phi (Sum.inl ()) =
      Phi 0 :=
  rfl

@[simp]
theorem rationalAdeleRankOneEisensteinSiegelSummand_finite
    (V : RationalQuadraticSpaceMatrix n)
    (Phi : (Fin n → RationalAdele) → ℂ) (t : ℚ) :
    V.rationalAdeleRankOneEisensteinSiegelSummand Phi (Sum.inr t) =
      V.rationalAdeleRankOneBruhatCoefficient Phi t :=
  rfl

/-- A summable finite Bruhat family gives a genuinely summable family on the
whole rational cusp index. -/
theorem summable_rationalAdeleRankOneEisensteinSiegelSummand
    (V : RationalQuadraticSpaceMatrix n)
    (Phi : (Fin n → RationalAdele) → ℂ)
    (hPhi : Summable (V.rationalAdeleRankOneBruhatCoefficient Phi)) :
    Summable (V.rationalAdeleRankOneEisensteinSiegelSummand Phi) := by
  apply Summable.sum
  · change Summable (fun _ : Unit => Phi 0)
    exact (hasSum_fintype (fun _ : Unit => Phi 0)).summable
  · exact hPhi

/-- The convergence-certified specialized rational rank-one
Eisenstein--Siegel functional.  Requiring `hPhi` prevents this definition from
using the nonsummable-`tsum` convention. -/
noncomputable def rationalAdeleRankOneEisensteinSiegelFunctional
    (V : RationalQuadraticSpaceMatrix n)
    (Phi : (Fin n → RationalAdele) → ℂ)
    (_hPhi : Summable (V.rationalAdeleRankOneBruhatCoefficient Phi)) : ℂ :=
  ∑' c : RationalRankOneProjectiveCusp,
    V.rationalAdeleRankOneEisensteinSiegelSummand Phi c

/-- The cusp sum is the literal infinity term plus the convergent finite
Bruhat sum. -/
theorem rationalAdeleRankOneEisensteinSiegelFunctional_eq_infinity_add_tsum
    (V : RationalQuadraticSpaceMatrix n)
    (Phi : (Fin n → RationalAdele) → ℂ)
    (hPhi : Summable (V.rationalAdeleRankOneBruhatCoefficient Phi)) :
    V.rationalAdeleRankOneEisensteinSiegelFunctional Phi hPhi =
      Phi 0 + ∑' t : ℚ, V.rationalAdeleRankOneBruhatCoefficient Phi t := by
  apply HasSum.tsum_eq
  apply HasSum.sum
  · change HasSum (fun _ : Unit => Phi 0) (Phi 0)
    convert hasSum_fintype (fun _ : Unit => Phi 0) using 1
    simp
  · exact hPhi.hasSum

/-- A rational unipotent applied to the test function translates the finite
Bruhat parameter. -/
theorem rationalAdeleRankOneBruhatCoefficient_unipotent_rational
    (V : RationalQuadraticSpaceMatrix n)
    (Phi : (Fin n → RationalAdele) → ℂ) (s t : ℚ) :
    V.rationalAdeleRankOneBruhatCoefficient
        (V.rationalAdeleRankOneUnipotentOperator
          (algebraMap ℚ RationalAdele s) Phi) t =
      V.rationalAdeleRankOneBruhatCoefficient Phi (t + s) := by
  rw [rationalAdeleRankOneBruhatCoefficient,
    rationalAdeleRankOneBruhatCoefficient]
  rw [← V.rationalAdeleRankOneUnipotentOperator_add]
  simp only [map_add]

/-- A rational unipotent fixes the infinity summand literally. -/
theorem rationalAdeleRankOneUnipotentOperator_zero_rational
    (V : RationalQuadraticSpaceMatrix n)
    (Phi : (Fin n → RationalAdele) → ℂ) (s : ℚ) :
    V.rationalAdeleRankOneUnipotentOperator
        (algebraMap ℚ RationalAdele s) Phi 0 = Phi 0 := by
  exact V.rationalAdeleRankOneUnipotentOperator_rationalDiagonal s Phi
    (0 : Fin n → ℚ)

/-- Translation of the rational affine cusp preserves convergence of the
Bruhat family. -/
theorem summable_rationalAdeleRankOneBruhatCoefficient_unipotent_rational
    (V : RationalQuadraticSpaceMatrix n)
    (Phi : (Fin n → RationalAdele) → ℂ)
    (hPhi : Summable (V.rationalAdeleRankOneBruhatCoefficient Phi))
    (s : ℚ) :
    Summable
      (V.rationalAdeleRankOneBruhatCoefficient
        (V.rationalAdeleRankOneUnipotentOperator
          (algebraMap ℚ RationalAdele s) Phi)) := by
  have hshift : Summable
      ((V.rationalAdeleRankOneBruhatCoefficient Phi) ∘
        (Equiv.addRight s)) :=
    ((Equiv.addRight s).summable_iff).2 hPhi
  exact hshift.congr fun t =>
    (V.rationalAdeleRankOneBruhatCoefficient_unipotent_rational Phi s t).symm

/-- The convergence-certified functional is invariant under every rational
unipotent generator.  The proof is only the literal infinity identity and the
bijective translation `t ↦ t+s` of the finite cusp chart. -/
theorem rationalAdeleRankOneEisensteinSiegelFunctional_unipotent_rational
    (V : RationalQuadraticSpaceMatrix n)
    (Phi : (Fin n → RationalAdele) → ℂ)
    (hPhi : Summable (V.rationalAdeleRankOneBruhatCoefficient Phi))
    (s : ℚ) :
    V.rationalAdeleRankOneEisensteinSiegelFunctional
        (V.rationalAdeleRankOneUnipotentOperator
          (algebraMap ℚ RationalAdele s) Phi)
        (V.summable_rationalAdeleRankOneBruhatCoefficient_unipotent_rational
          Phi hPhi s) =
      V.rationalAdeleRankOneEisensteinSiegelFunctional Phi hPhi := by
  rw [V.rationalAdeleRankOneEisensteinSiegelFunctional_eq_infinity_add_tsum,
    V.rationalAdeleRankOneEisensteinSiegelFunctional_eq_infinity_add_tsum,
    V.rationalAdeleRankOneUnipotentOperator_zero_rational]
  congr 1
  calc
    (∑' t : ℚ,
        V.rationalAdeleRankOneBruhatCoefficient
          (V.rationalAdeleRankOneUnipotentOperator
            (algebraMap ℚ RationalAdele s) Phi) t) =
        ∑' t : ℚ,
          V.rationalAdeleRankOneBruhatCoefficient Phi (t + s) := by
            apply tsum_congr
            intro t
            exact
              V.rationalAdeleRankOneBruhatCoefficient_unipotent_rational
                Phi s t
    _ = ∑' t : ℚ,
        V.rationalAdeleRankOneBruhatCoefficient Phi t :=
      (Equiv.addRight s).tsum_eq
        (V.rationalAdeleRankOneBruhatCoefficient Phi)

end RationalQuadraticSpaceMatrix

namespace PositiveDefiniteIntegralLattice

open RationalQuadraticSpaceMatrix

variable {n : ℕ}

/-- The exact polar Gaussian--lattice cusp family is summable on all of
`{∞} ∪ ℚ` in ambient rank at least five. -/
theorem summable_rationalAdeleRankOneEisensteinSiegelSummand_polarGaussianLattice_of_rankAtLeastFive
    (L : PositiveDefiniteIntegralLattice n) {a : ℝ} (ha : 0 < a) (hn : 5 ≤ n) :
    Summable
      (L.rationalQuadraticSpaceMatrix
        |>.rationalAdeleRankOneEisensteinSiegelSummand
          (rationalAdeleVectorPolarGaussianLatticeTest L (a : ℂ))) := by
  exact L.rationalQuadraticSpaceMatrix
    |>.summable_rationalAdeleRankOneEisensteinSiegelSummand
      (rationalAdeleVectorPolarGaussianLatticeTest L (a : ℂ))
      (L.summable_rationalAdeleRankOneBruhatCoefficient_polarGaussianLattice_of_rankAtLeastFive
        ha hn)

/-- The specialized convergent rational rank-one `E_V` for the concrete polar
Gaussian--lattice test.  Its proof arguments certify the positive scale and
the rank-at-least-five convergence range. -/
noncomputable def rationalAdeleRankOneEisensteinSiegelFunctional_polarGaussianLattice
    (L : PositiveDefiniteIntegralLattice n) {a : ℝ} (ha : 0 < a) (hn : 5 ≤ n) : ℂ :=
  L.rationalQuadraticSpaceMatrix
    |>.rationalAdeleRankOneEisensteinSiegelFunctional
      (rationalAdeleVectorPolarGaussianLatticeTest L (a : ℂ))
      (L.summable_rationalAdeleRankOneBruhatCoefficient_polarGaussianLattice_of_rankAtLeastFive
        ha hn)

/-- The concrete rank-at-least-five functional keeps its infinity term
explicit and has the exact convergent Bruhat expansion. -/
theorem rationalAdeleRankOneEisensteinSiegelFunctional_polarGaussianLattice_eq_infinity_add_tsum
    (L : PositiveDefiniteIntegralLattice n) {a : ℝ} (ha : 0 < a) (hn : 5 ≤ n) :
    L.rationalAdeleRankOneEisensteinSiegelFunctional_polarGaussianLattice
        ha hn =
      rationalAdeleVectorPolarGaussianLatticeTest L (a : ℂ) 0 +
        ∑' t : ℚ,
          L.rationalQuadraticSpaceMatrix.rationalAdeleRankOneBruhatCoefficient
            (rationalAdeleVectorPolarGaussianLatticeTest L (a : ℂ)) t := by
  exact L.rationalQuadraticSpaceMatrix
    |>.rationalAdeleRankOneEisensteinSiegelFunctional_eq_infinity_add_tsum
      (rationalAdeleVectorPolarGaussianLatticeTest L (a : ℂ))
      (L.summable_rationalAdeleRankOneBruhatCoefficient_polarGaussianLattice_of_rankAtLeastFive
        ha hn)

end PositiveDefiniteIntegralLattice

end
