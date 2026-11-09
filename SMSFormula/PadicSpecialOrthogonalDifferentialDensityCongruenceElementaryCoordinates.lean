import SMSFormula.SkewAdjointPadicElementaryCoordinateBall
import SMSFormula.PadicSpecialOrthogonalDifferentialDensityCongruenceCoordinateMass
import Mathlib.Analysis.Normed.Module.Ball.Pointwise
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Elementary coordinates on the density-adapted p-adic congruence kernel

The density-adapted direct principal kernel is represented explicitly in the
identity-centered Cayley target.  Its inverse Cayley coordinate is exposed as
`(g + 1)⁻¹ * (g - 1)`, together with the literal entrywise finite-reduction
condition on `g`.

Independently of any coordinate-mass calculation, the form-adapted uniform
balls are proved cofinal among zero-neighborhoods.  A chosen form-adapted ball
therefore lies inside the density-adapted inverse-Cayley source.

This module does not identify the source with that ball, evaluate its measure,
or compare the resulting mass with `normalizedLocalDensity`.
-/

noncomputable section

open MeasureTheory
open Matrix
open TopologicalSpace
open scoped Matrix Matrix.Norms.Operator Topology Pointwise

namespace Matrix

variable {n : ℕ}

/-! ## Integral inverse-Cayley divisibility -/

/-- At an odd prime, an integral matrix congruent to the identity modulo `p`
has integral inverse denominator `G + 1`. -/
theorem padicIntMatrix_add_one_isUnit_of_toZMod_eq_one
    {p : ℕ} [Fact (Nat.Prime p)] (hp2 : p ≠ 2)
    (G : Matrix (Fin n) (Fin n) ℤ_[p])
    (hG : ∀ i j, PadicInt.toZMod (G i j) =
      (1 : Matrix (Fin n) (Fin n) (ZMod p)) i j) :
    IsUnit (G + 1) := by
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  have h2 : IsUnit (2 : ZMod p) := by
    apply isUnit_iff_ne_zero.mpr
    intro h
    have hd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h
    exact hp2
      ((Nat.dvd_prime (by norm_num : Nat.Prime 2)).mp hd |>.resolve_left
        (Fact.out : Nat.Prime p).ne_one)
  have hmap :
      (G + 1).map PadicInt.toZMod =
        Matrix.scalar (Fin n) (2 : ZMod p) := by
    ext i j
    change
      PadicInt.toZMod
          (G i j + (1 : Matrix (Fin n) (Fin n) ℤ_[p]) i j) =
        _
    rw [map_add, hG]
    by_cases hij : i = j
    · subst j
      simp only [Matrix.one_apply, Matrix.scalar_apply, ↓reduceIte]
      norm_num
    · simp [Matrix.scalar_apply, hij]
  have hmoddet :
      IsUnit (PadicInt.toZMod (G + 1).det) := by
    rw [RingHom.map_det]
    change IsUnit ((G + 1).map PadicInt.toZMod).det
    rw [hmap]
    exact (Matrix.isUnit_iff_isUnit_det _).mp
      (h2.map (Matrix.scalar (Fin n)))
  apply (IsLocalRing.residue_ne_zero_iff_isUnit _).mp
  intro hzero
  have htozero : PadicInt.toZMod (G + 1).det = 0 := by
    rw [PadicInt.toZMod_eq_residueField_comp_residue]
    simp [hzero]
  exact (isUnit_iff_ne_zero.mp hmoddet) htozero

/-- At an odd prime, if an integral invertible matrix is congruent to the
identity modulo `p ^ k`, then every entry of the inverse Cayley coordinate,
after left multiplication by an arbitrary integral matrix, has norm at most
`‖p ^ k‖`. -/
theorem norm_integralMatrix_mul_padicIntegralCayleyInverse_le_pow
    {p k : ℕ} [Fact (Nat.Prime p)]
    (hp2 : p ≠ 2) (hk : 1 ≤ k)
    (F : Matrix (Fin n) (Fin n) ℤ_[p])
    (G : GL (Fin n) ℤ_[p])
    (hG : ∀ i j, PadicInt.toZModPow k (G.1 i j) =
      (1 : Matrix (Fin n) (Fin n) (ZMod (p ^ k))) i j) :
    ∀ i j,
      ‖(F.map PadicInt.Coe.ringHom *
          ((G.1.map PadicInt.Coe.ringHom + 1)⁻¹ *
            (G.1.map PadicInt.Coe.ringHom - 1))) i j‖ ≤
        ‖(p : ℚ_[p]) ^ k‖ := by
  let D : Matrix (Fin n) (Fin n) ℤ_[p] := G.1 - 1
  have hD : ∀ i j,
      D i j ∈ (Ideal.span {(p : ℤ_[p]) ^ k} : Ideal ℤ_[p]) := by
    intro i j
    rw [← PadicInt.ker_toZModPow k, RingHom.mem_ker]
    dsimp [D]
    rw [map_sub, hG]
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  have hspan :
      (Ideal.span {(p : ℤ_[p]) ^ k} : Ideal ℤ_[p]) ≤
        Ideal.span {(p : ℤ_[p])} := by
    apply Ideal.span_le.2
    intro x hx
    simp only [Set.mem_singleton_iff] at hx
    subst x
    exact (Ideal.mem_span_singleton).2
      (dvd_pow_self _ (Nat.ne_of_gt hk))
  have hGmod : ∀ i j, PadicInt.toZMod (G.1 i j) =
      (1 : Matrix (Fin n) (Fin n) (ZMod p)) i j := by
    intro i j
    have hd : D i j ∈ IsLocalRing.maximalIdeal ℤ_[p] := by
      rw [PadicInt.maximalIdeal_eq_span_p]
      exact hspan (hD i j)
    rw [← PadicInt.ker_toZMod, RingHom.mem_ker] at hd
    dsimp [D] at hd
    rw [map_sub] at hd
    have hone :
        PadicInt.toZMod
            ((1 : Matrix (Fin n) (Fin n) ℤ_[p]) i j) =
          (1 : Matrix (Fin n) (Fin n) (ZMod p)) i j := by
      by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
    rw [hone] at hd
    exact sub_eq_zero.mp hd
  let A : Matrix (Fin n) (Fin n) ℤ_[p] := G.1 + 1
  have hA : IsUnit A := by
    dsimp [A]
    exact padicIntMatrix_add_one_isUnit_of_toZMod_eq_one hp2 G.1 hGmod
  let U : GL (Fin n) ℤ_[p] := hA.unit
  let B : Matrix (Fin n) (Fin n) ℤ_[p] := (U⁻¹).1
  have hU : U.1 = A := hA.unit_spec
  have hBmap :
      B.map PadicInt.Coe.ringHom =
        (G.1.map PadicInt.Coe.ringHom + 1)⁻¹ := by
    change
      (Matrix.GeneralLinearGroup.map PadicInt.Coe.ringHom U⁻¹).1 =
        (G.1.map PadicInt.Coe.ringHom + 1)⁻¹
    rw [map_inv, Matrix.coe_units_inv]
    change
      (U.1.map PadicInt.Coe.ringHom)⁻¹ =
        (G.1.map PadicInt.Coe.ringHom + 1)⁻¹
    rw [hU]
    congr 1
    ext i j
    by_cases hij : i = j <;> simp [A, hij]
  let C : Matrix (Fin n) (Fin n) ℤ_[p] := F * B * D
  have hC : ∀ i j,
      C i j ∈ (Ideal.span {(p : ℤ_[p]) ^ k} : Ideal ℤ_[p]) := by
    intro i j
    dsimp [C]
    rw [Matrix.mul_apply]
    apply Ideal.sum_mem
    intro a _
    apply Ideal.mul_mem_left
    exact hD a j
  intro i j
  have hnormInt :=
    (PadicInt.norm_le_pow_iff_mem_span_pow (C i j) k).2 (hC i j)
  have hCmap :
      C.map PadicInt.Coe.ringHom =
        F.map PadicInt.Coe.ringHom *
          ((G.1.map PadicInt.Coe.ringHom + 1)⁻¹ *
            (G.1.map PadicInt.Coe.ringHom - 1)) := by
    have hDmap :
        D.map PadicInt.Coe.ringHom =
          G.1.map PadicInt.Coe.ringHom - 1 := by
      ext a b
      by_cases hab : a = b <;> simp [D, hab]
    dsimp [C]
    rw [Matrix.map_mul, Matrix.map_mul, hBmap, hDmap,
      Matrix.mul_assoc]
  rw [← hCmap]
  change ‖((C i j : ℤ_[p]) : ℚ_[p])‖ ≤ _
  have hnormcoe : ‖((C i j : ℤ_[p]) : ℚ_[p])‖ = ‖C i j‖ := rfl
  rw [hnormcoe]
  calc
    ‖C i j‖ ≤ (p : ℝ) ^ (-(k : ℤ)) := hnormInt
    _ = ‖(p : ℚ_[p]) ^ k‖ := by
      rw [norm_pow, Padic.norm_p]
      simp [inv_pow]

end Matrix

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

local instance
    localPadicSpecialOrthogonalDifferentialDensityCongruenceElementarySourceMeasurableSpace
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    MeasurableSpace
      (skewAdjointMatricesLieSubalgebra
        (L.rationalFormMatrix.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  borel _

local instance
    localPadicSpecialOrthogonalDifferentialDensityCongruenceElementarySourceBorelSpace
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    BorelSpace
      (skewAdjointMatricesLieSubalgebra
        (L.rationalFormMatrix.map (algebraMap ℚ ℚ_[p]))).toSubmodule :=
  ⟨rfl⟩

/-! ## Literal density-depth Cayley coordinates -/

/-- A density-adapted direct-kernel element represented in the exact
identity-centered translated Cayley target. -/
def localPadicSpecialOrthogonalDifferentialDensityCongruenceTargetPoint
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)]
    (g : L.localPadicSpecialOrthogonalDifferentialStabilizerSubgroup p)
    (hg : g ∈
      L.localPadicSpecialOrthogonalDifferentialPrincipalCongruenceSubgroup
        p
        (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p)) :
    padicCayleySpecialOrthogonalTranslatedTarget
      L.rationalFormMatrix p 1 :=
  ⟨g,
    L.localPadicSpecialOrthogonalDifferentialDensityCongruenceAmbientSet_subset_target
      p ⟨g, hg, rfl⟩⟩

/-- The inverse Cayley coordinate of a density-adapted direct-kernel
element. -/
def localPadicSpecialOrthogonalDifferentialDensityCongruenceInverseCayley
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)]
    (g : L.localPadicSpecialOrthogonalDifferentialStabilizerSubgroup p)
    (hg : g ∈
      L.localPadicSpecialOrthogonalDifferentialPrincipalCongruenceSubgroup
        p
        (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p)) :
    Matrix.skewAdjointPadicCayleySource L.rationalFormMatrix p :=
  (skewAdjointPadicCayleyTranslatedHomeomorph
    L.rationalFormMatrix p L.rationalFormMatrix_det_ne_zero 1).symm
      (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceTargetPoint
        p g hg)

/-- At the selected density depth, the identity-centered inverse Cayley
coordinate is literally `(g + 1)⁻¹ * (g - 1)`. -/
theorem
    coe_localPadicSpecialOrthogonalDifferentialDensityCongruenceInverseCayley
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)]
    (g : L.localPadicSpecialOrthogonalDifferentialStabilizerSubgroup p)
    (hg : g ∈
      L.localPadicSpecialOrthogonalDifferentialPrincipalCongruenceSubgroup
        p
        (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p)) :
    ((L.localPadicSpecialOrthogonalDifferentialDensityCongruenceInverseCayley
        p g hg).1 : Matrix (Fin n) (Fin n) ℚ_[p]) =
      ((((g :
          specialFormPreservingMatrixSubgroup
            (L.rationalFormMatrix.map (algebraMap ℚ ℚ_[p]))).1.1.1 :
              Matrix (Fin n) (Fin n) ℚ_[p]) + 1)⁻¹ *
        (((g :
          specialFormPreservingMatrixSubgroup
            (L.rationalFormMatrix.map (algebraMap ℚ ℚ_[p]))).1.1.1 :
              Matrix (Fin n) (Fin n) ℚ_[p]) - 1)) := by
  rw [
    localPadicSpecialOrthogonalDifferentialDensityCongruenceInverseCayley,
    coe_skewAdjointPadicCayleyTranslatedHomeomorph_symm_apply]
  simp [
    localPadicSpecialOrthogonalDifferentialDensityCongruenceTargetPoint]

/-- The inverse coordinate of a density-adapted direct-kernel element belongs
to the literal exact-source density kernel. -/
theorem
    localPadicSpecialOrthogonalDifferentialDensityCongruenceInverseCayley_mem_sourceSet
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)]
    (g : L.localPadicSpecialOrthogonalDifferentialStabilizerSubgroup p)
    (hg : g ∈
      L.localPadicSpecialOrthogonalDifferentialPrincipalCongruenceSubgroup
        p
        (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p)) :
    L.localPadicSpecialOrthogonalDifferentialDensityCongruenceInverseCayley
        p g hg ∈
      L.localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceSet p := by
  change
    (skewAdjointPadicCayleyTranslatedHomeomorph
      L.rationalFormMatrix p L.rationalFormMatrix_det_ne_zero 1)
        ((skewAdjointPadicCayleyTranslatedHomeomorph
          L.rationalFormMatrix p L.rationalFormMatrix_det_ne_zero 1).symm
            (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceTargetPoint
              p g hg)) ∈
      L.localPadicSpecialOrthogonalDifferentialDensityCongruenceTargetSet p
  rw [
    (skewAdjointPadicCayleyTranslatedHomeomorph
      L.rationalFormMatrix p L.rationalFormMatrix_det_ne_zero 1).apply_symm_apply]
  exact ⟨g, hg, rfl⟩

/-- Every exact-source point of the density-adapted kernel is the inverse
Cayley coordinate of a literal direct-kernel element. -/
theorem
    exists_densityCongruenceKernel_eq_inverseCayley_of_mem_sourceSet
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)]
    (X : Matrix.skewAdjointPadicCayleySource L.rationalFormMatrix p)
    (hX :
      X ∈
        L.localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceSet
          p) :
    ∃
      (g : L.localPadicSpecialOrthogonalDifferentialStabilizerSubgroup p)
      (hg : g ∈
        L.localPadicSpecialOrthogonalDifferentialPrincipalCongruenceSubgroup
          p
          (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p)),
      X =
        L.localPadicSpecialOrthogonalDifferentialDensityCongruenceInverseCayley
          p g hg := by
  let e :=
    skewAdjointPadicCayleyTranslatedHomeomorph
      L.rationalFormMatrix p L.rationalFormMatrix_det_ne_zero 1
  change
    (e X).1 ∈
      L.localPadicSpecialOrthogonalDifferentialDensityCongruenceAmbientSet p
    at hX
  rcases hX with ⟨g, hg, hgeq⟩
  refine ⟨g, hg, ?_⟩
  apply e.injective
  change
    e X =
      e (e.symm
        (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceTargetPoint
          p g hg))
  rw [e.apply_symm_apply]
  apply Subtype.ext
  exact hgeq.symm

/-- Every ambient density-kernel coordinate is represented by a literal
direct-kernel element. -/
theorem
    exists_densityCongruenceKernel_eq_inverseCayley_of_mem_sourceAmbientSet
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)]
    (X :
      (skewAdjointMatricesLieSubalgebra
        (L.rationalFormMatrix.map (algebraMap ℚ ℚ_[p]))).toSubmodule)
    (hX :
      X ∈
        L.localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceAmbientSet
          p) :
    ∃
      (g : L.localPadicSpecialOrthogonalDifferentialStabilizerSubgroup p)
      (hg : g ∈
        L.localPadicSpecialOrthogonalDifferentialPrincipalCongruenceSubgroup
          p
          (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p)),
      X =
        (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceInverseCayley
          p g hg).1 := by
  rcases hX with ⟨x, hx, rfl⟩
  rcases
      L.exists_densityCongruenceKernel_eq_inverseCayley_of_mem_sourceSet
        p x hx with
    ⟨g, hg, hxg⟩
  exact ⟨g, hg, congrArg Subtype.val hxg⟩

/-- A density-depth direct-kernel element is entrywise congruent to the
identity after passage to the original integral matrix. -/
theorem
    localPadicSpecialOrthogonalDifferentialDensityCongruence_reduction_apply
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)]
    (g : L.localPadicSpecialOrthogonalDifferentialStabilizerSubgroup p)
    (hg : g ∈
      L.localPadicSpecialOrthogonalDifferentialPrincipalCongruenceSubgroup
        p
        (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p))
    (i j : Fin n) :
    PadicInt.toZModPow
        (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p)
        (L.localPadicLatticeStabilizerIntegralGL p
          (L.localPadicSpecialOrthogonalDifferentialStabilizerToHistorical
            p g).1 i j) =
      (1 :
        Matrix (Fin n) (Fin n)
          (ZMod
            (p ^
              L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth
                p))) i j := by
  have hhistorical :=
    (L.mem_localPadicSpecialOrthogonalDifferentialPrincipalCongruenceSubgroup_iff_historical
      p
      (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p)
      g).mp hg
  exact
    (L.mem_localPadicSpecialOrthogonalLatticePrincipalCongruenceSubgroup_iff
      p
      (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p)
      (L.localPadicSpecialOrthogonalDifferentialStabilizerToHistorical
        p g)).mp hhistorical i j

/-- Ambient density-kernel membership supplies simultaneously the literal
inverse Cayley formula and the entrywise finite-reduction condition. -/
theorem
    exists_densityCongruenceKernel_inverse_formula_and_reduction_of_mem_sourceAmbientSet
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)]
    (X :
      (skewAdjointMatricesLieSubalgebra
        (L.rationalFormMatrix.map (algebraMap ℚ ℚ_[p]))).toSubmodule)
    (hX :
      X ∈
        L.localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceAmbientSet
          p) :
    ∃ g : L.localPadicSpecialOrthogonalDifferentialStabilizerSubgroup p,
      g ∈
        L.localPadicSpecialOrthogonalDifferentialPrincipalCongruenceSubgroup
          p
          (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p) ∧
        (X : Matrix (Fin n) (Fin n) ℚ_[p]) =
          ((((g :
              specialFormPreservingMatrixSubgroup
                (L.rationalFormMatrix.map
                  (algebraMap ℚ ℚ_[p]))).1.1.1 :
                    Matrix (Fin n) (Fin n) ℚ_[p]) + 1)⁻¹ *
            (((g :
              specialFormPreservingMatrixSubgroup
                (L.rationalFormMatrix.map
                  (algebraMap ℚ ℚ_[p]))).1.1.1 :
                    Matrix (Fin n) (Fin n) ℚ_[p]) - 1)) ∧
        ∀ i j,
          PadicInt.toZModPow
              (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth
                p)
              (L.localPadicLatticeStabilizerIntegralGL p
                (L.localPadicSpecialOrthogonalDifferentialStabilizerToHistorical
                  p g).1 i j) =
            (1 :
              Matrix (Fin n) (Fin n)
                (ZMod
                  (p ^
                    L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth
                      p))) i j := by
  rcases
      L.exists_densityCongruenceKernel_eq_inverseCayley_of_mem_sourceAmbientSet
        p X hX with
    ⟨g, hg, hXg⟩
  refine ⟨g, hg, ?_, ?_⟩
  · rw [hXg]
    exact
      L.coe_localPadicSpecialOrthogonalDifferentialDensityCongruenceInverseCayley
        p g hg
  · exact fun i j ↦
      L.localPadicSpecialOrthogonalDifferentialDensityCongruence_reduction_apply
        p g hg i j

/-! ## Form-adapted outer ball at odd primes -/

/-- At an odd prime, every density-adapted inverse-Cayley coordinate belongs
to the form-adapted uniform ball at the selected principal-congruence depth. -/
theorem
    localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceAmbientSet_subset_formElementaryUniformCoordinateBall
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)]
    (hp2 : p ≠ 2) :
    L.localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceAmbientSet
        p ⊆
      skewAdjointFormElementaryPadicUniformCoordinateBall
        p
        (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p)
        L.rationalFormMatrix (L.form_symm.map _)
          L.rationalFormMatrix_det_ne_zero := by
  intro X hX
  apply
    (mem_skewAdjointFormElementaryPadicUniformCoordinateBall_iff_upper
      p
      (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p)
      L.rationalFormMatrix (L.form_symm.map _)
      L.rationalFormMatrix_det_ne_zero X).2
  intro q
  rcases
      L.exists_densityCongruenceKernel_inverse_formula_and_reduction_of_mem_sourceAmbientSet
        p X hX with
    ⟨g, hg, hformula, hreduction⟩
  let h :=
    L.localPadicSpecialOrthogonalDifferentialStabilizerToHistorical p g
  let G : GL (Fin n) ℤ_[p] :=
    L.localPadicLatticeStabilizerIntegralGL p h.1
  have hbound :=
    norm_integralMatrix_mul_padicIntegralCayleyInverse_le_pow
      hp2
      (le_trans (by norm_num)
        (L.two_le_localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth
          p))
      (L.pairingMatrix_padic p) G hreduction q.1.1 q.1.2
  have hGmap :
      G.1.map PadicInt.Coe.ringHom =
        ((g :
          specialFormPreservingMatrixSubgroup
            (L.rationalFormMatrix.map (algebraMap ℚ ℚ_[p]))).1.1.1 :
              Matrix (Fin n) (Fin n) ℚ_[p]) := by
    ext i j
    exact L.localPadicLatticeStabilizerIntegralGL_apply p h.1 i j
  rw [hGmap] at hbound
  rw [hformula]
  simpa only [
    L.rationalFormMatrix_map_padic_eq_pairingMatrix_padicField p] using hbound

/-! ## Form-adapted inner ball -/

/-- Every zero-neighborhood contains a form-adapted uniform `p ^ k`
coordinate ball. -/
theorem
    exists_skewAdjointFormElementaryPadicUniformCoordinateBall_subset_of_mem_nhds_zero
    (p : ℕ) [Fact (Nat.Prime p)]
    (F : Matrix (Fin n) (Fin n) ℚ) (hF : F.IsSymm)
    (hdet : F.det ≠ 0)
    {s : Set
      (skewAdjointMatricesLieSubalgebra
        (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule}
    (hs : s ∈ 𝓝 0) :
    ∃ k,
      skewAdjointFormElementaryPadicUniformCoordinateBall
        p k F hF hdet ⊆ s := by
  have hsmall :
      ∀ᶠ r in 𝓝 (0 : ℚ_[p]),
        ({0} : Set
            (skewAdjointMatricesLieSubalgebra
              (F.map (algebraMap ℚ ℚ_[p]))).toSubmodule) +
            r •
              (skewAdjointFormElementaryPadicCoordinateLattice
                p F hF hdet : Set _) ⊆
          s :=
    eventually_singleton_add_smul_subset
      (skewAdjointFormElementaryPadicCoordinateLattice
        p F hF hdet).isCompact.isBounded hs
  have hp :
      Filter.Tendsto (fun k : ℕ => (p : ℚ_[p]) ^ k)
        Filter.atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_norm_lt_one Padic.norm_p_lt_one
  obtain ⟨k, hk⟩ := (hp.eventually hsmall).exists
  refine ⟨k, ?_⟩
  rintro y ⟨z, hz, rfl⟩
  apply hk
  simp only [Set.mem_add, Set.mem_singleton_iff, Set.mem_smul_set]
  exact ⟨0, rfl, (p : ℚ_[p]) ^ k • z, ⟨z, hz, rfl⟩, by simp⟩

/-- Some form-adapted uniform coordinate ball lies inside the
density-adapted inverse-Cayley kernel. -/
theorem
    exists_skewAdjointFormElementaryPadicUniformCoordinateBall_subset_densityCongruenceSourceAmbientSet
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    ∃ r,
      skewAdjointFormElementaryPadicUniformCoordinateBall
          p r L.rationalFormMatrix (L.form_symm.map _)
            L.rationalFormMatrix_det_ne_zero ⊆
        L.localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceAmbientSet
          p := by
  exact
    exists_skewAdjointFormElementaryPadicUniformCoordinateBall_subset_of_mem_nhds_zero
      p L.rationalFormMatrix (L.form_symm.map _)
        L.rationalFormMatrix_det_ne_zero
      ((L.isOpen_localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceAmbientSet
          p).mem_nhds
        (L.zero_mem_localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceAmbientSet
          p))

/-- A chosen inner form-adapted coordinate-ball level for the
density-adapted inverse-Cayley kernel. -/
def localPadicSpecialOrthogonalDifferentialDensityCongruenceElementaryInnerLevel
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] : ℕ :=
  Classical.choose
    (L.exists_skewAdjointFormElementaryPadicUniformCoordinateBall_subset_densityCongruenceSourceAmbientSet
      p)

/-- The chosen inner form-adapted ball lies inside the density-adapted
inverse-Cayley kernel. -/
theorem
    localPadicSpecialOrthogonalDifferentialDensityCongruenceElementaryInnerLevel_spec
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] :
    skewAdjointFormElementaryPadicUniformCoordinateBall
        p
        (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceElementaryInnerLevel
          p)
        L.rationalFormMatrix (L.form_symm.map _)
          L.rationalFormMatrix_det_ne_zero ⊆
      L.localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceAmbientSet
        p :=
  Classical.choose_spec
    (L.exists_skewAdjointFormElementaryPadicUniformCoordinateBall_subset_densityCongruenceSourceAmbientSet
      p)

/-- At an odd prime, the density-adapted inverse-Cayley kernel is sandwiched
between a chosen sufficiently deep form-adapted ball and the form-adapted
ball at the selected principal-congruence depth.  No equality or mass formula
is inferred from this sandwich. -/
theorem
    localPadicSpecialOrthogonalDifferentialDensityCongruence_formElementaryUniformCoordinateBall_sandwich
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)]
    (hp2 : p ≠ 2) :
    skewAdjointFormElementaryPadicUniformCoordinateBall
        p
        (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceElementaryInnerLevel
          p)
        L.rationalFormMatrix (L.form_symm.map _)
          L.rationalFormMatrix_det_ne_zero ⊆
      L.localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceAmbientSet
        p ∧
    L.localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceAmbientSet
        p ⊆
      skewAdjointFormElementaryPadicUniformCoordinateBall
        p
        (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p)
        L.rationalFormMatrix (L.form_symm.map _)
          L.rationalFormMatrix_det_ne_zero :=
  ⟨L.localPadicSpecialOrthogonalDifferentialDensityCongruenceElementaryInnerLevel_spec
      p,
    L.localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceAmbientSet_subset_formElementaryUniformCoordinateBall
      p hp2⟩

end PositiveDefiniteIntegralLattice
