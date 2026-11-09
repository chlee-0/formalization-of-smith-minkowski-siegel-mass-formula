import SMSFormula.PadicSpecialOrthogonalDifferentialDensityCongruenceSelectedDepthCarrier

/-!
# Explicit odd-prime translation stability of the density kernel

At an odd prime, every point of the selected inverse-Cayley density source has
an integral skew-adjoint representative divisible by the selected prime power.
Indeed, its representing stabilizer matrix is congruent to one, so `g + 1` is
a matrix unit over `Z_p` and the inverse Cayley formula is integral.

Combining this lift with the explicit determinant-loss lift for a perturbation
shows that the density source is stable under addition by the form-elementary
ball at level

`densityCongruenceDepth + padicValInt p L.pairingDeterminant`.

This proves the requested translation theorem without a noncommutative Cayley
difference expansion.  It is odd-prime only: at `p = 2`, `g + 1` need not be a
matrix unit over `Z_2`.
-/

noncomputable section

open Matrix
open scoped Matrix Matrix.Norms.Operator

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- At an odd prime, a point of the exact inverse-Cayley density source has an
integral skew-adjoint lift divisible by the selected principal-congruence
power. -/
theorem
    exists_integral_skewAdjoint_lift_mem_span_pow_of_mem_densityCongruenceSourceAmbientSet
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] (hp2 : p ≠ 2)
    (X :
      (skewAdjointMatricesLieSubalgebra
        (L.rationalFormMatrix.map (algebraMap ℚ ℚ_[p]))).toSubmodule)
    (hX : X ∈
      L.localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceAmbientSet
        p) :
    ∃ Xz :
        (skewAdjointMatricesLieSubalgebra
          (L.pairingMatrix_padic p)).toSubmodule,
      (Xz : Matrix (Fin n) (Fin n) ℤ_[p]).map
          PadicInt.Coe.ringHom =
        (X : Matrix (Fin n) (Fin n) ℚ_[p]) ∧
      ∀ i j,
        (Xz : Matrix (Fin n) (Fin n) ℤ_[p]) i j ∈
          (Ideal.span
            {(p : ℤ_[p]) ^
              L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth
                p} : Ideal ℤ_[p]) := by
  let k :=
    L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p
  have hk : 1 ≤ k := le_trans (by norm_num)
    (L.two_le_localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p)
  rcases
      L.exists_densityCongruenceKernel_inverse_formula_and_reduction_of_mem_sourceAmbientSet
        p X hX with
    ⟨g, hg, hformula, hreduction⟩
  let h :=
    L.localPadicSpecialOrthogonalDifferentialStabilizerToHistorical p g
  let G : GL (Fin n) ℤ_[p] :=
    L.localPadicLatticeStabilizerIntegralGL p h.1
  let D : Matrix (Fin n) (Fin n) ℤ_[p] := G.1 - 1
  have hD : ∀ i j,
      D i j ∈ (Ideal.span {(p : ℤ_[p]) ^ k} : Ideal ℤ_[p]) := by
    intro i j
    rw [← PadicInt.ker_toZModPow k, RingHom.mem_ker]
    dsimp [D]
    rw [map_sub, hreduction]
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
  have hGmod : ∀ i j,
      PadicInt.toZMod (G.1 i j) =
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
  let C : Matrix (Fin n) (Fin n) ℤ_[p] := B * D
  have hCmem : ∀ i j,
      C i j ∈ (Ideal.span {(p : ℤ_[p]) ^ k} : Ideal ℤ_[p]) := by
    intro i j
    dsimp [C]
    rw [Matrix.mul_apply]
    apply Ideal.sum_mem
    intro a _
    exact Ideal.mul_mem_left _ _ (hD a j)
  have hDmap :
      D.map PadicInt.Coe.ringHom =
        G.1.map PadicInt.Coe.ringHom - 1 := by
    ext i j
    by_cases hij : i = j <;> simp [D, hij]
  have hGmap :
      G.1.map PadicInt.Coe.ringHom =
        ((g :
          specialFormPreservingMatrixSubgroup
            (L.rationalFormMatrix.map (algebraMap ℚ ℚ_[p]))).1.1.1 :
              Matrix (Fin n) (Fin n) ℚ_[p]) := by
    ext i j
    exact L.localPadicLatticeStabilizerIntegralGL_apply p h.1 i j
  have hCmap :
      C.map PadicInt.Coe.ringHom =
        (X : Matrix (Fin n) (Fin n) ℚ_[p]) := by
    calc
      C.map PadicInt.Coe.ringHom =
          (G.1.map PadicInt.Coe.ringHom + 1)⁻¹ *
            (G.1.map PadicInt.Coe.ringHom - 1) := by
        dsimp [C]
        rw [Matrix.map_mul, hBmap, hDmap]
      _ = ((((g :
            specialFormPreservingMatrixSubgroup
              (L.rationalFormMatrix.map (algebraMap ℚ ℚ_[p]))).1.1.1 :
                Matrix (Fin n) (Fin n) ℚ_[p]) + 1)⁻¹ *
          (((g :
            specialFormPreservingMatrixSubgroup
              (L.rationalFormMatrix.map (algebraMap ℚ ℚ_[p]))).1.1.1 :
                Matrix (Fin n) (Fin n) ℚ_[p]) - 1)) := by
        rw [hGmap]
      _ = (X : Matrix (Fin n) (Fin n) ℚ_[p]) := hformula.symm
  have hCskew :
      C ∈ skewAdjointMatricesLieSubalgebra (L.pairingMatrix_padic p) := by
    apply (mem_ker_skewAdjointOperator_iff _ _).mp
    apply LinearMap.mem_ker.mpr
    apply Matrix.ext
    intro i j
    apply PadicInt.ext
    have hXop :
        skewAdjointOperator
            (L.rationalFormMatrix.map (algebraMap ℚ ℚ_[p]))
            (X : Matrix (Fin n) (Fin n) ℚ_[p]) = 0 :=
      LinearMap.mem_ker.mp
        ((mem_ker_skewAdjointOperator_iff
          (L.rationalFormMatrix.map (algebraMap ℚ ℚ_[p]))
          (X : Matrix (Fin n) (Fin n) ℚ_[p])).mpr X.property)
    have hmap :
        (skewAdjointOperator (L.pairingMatrix_padic p) C).map
            PadicInt.Coe.ringHom =
          skewAdjointOperator
            (L.rationalFormMatrix.map (algebraMap ℚ ℚ_[p]))
            (X : Matrix (Fin n) (Fin n) ℚ_[p]) := by
      have hFmap :
          (L.pairingMatrix_padic p).map PadicInt.Coe.ringHom =
            L.rationalFormMatrix.map (algebraMap ℚ ℚ_[p]) :=
        (L.rationalFormMatrix_map_padic_eq_pairingMatrix_padicField p).symm
      simp only [skewAdjointOperator_apply]
      rw [Matrix.map_add _ (fun a b ↦
        map_add PadicInt.Coe.ringHom a b),
        Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map,
        hCmap, hFmap]
    change
      ((skewAdjointOperator (L.pairingMatrix_padic p) C).map
        PadicInt.Coe.ringHom) i j = 0
    rw [hmap, hXop]
    rfl
  exact ⟨⟨C, hCskew⟩, hCmap, hCmem⟩

/-- At an odd prime, adding a perturbation from the explicit determinant-loss
form-coordinate ball preserves the selected inverse-Cayley density source. -/
theorem
    add_mem_localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceAmbientSet_of_mem_formElementaryBall_add_pairingDeterminantVal
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] (hp2 : p ≠ 2)
    (X Y :
      (skewAdjointMatricesLieSubalgebra
        (L.rationalFormMatrix.map (algebraMap ℚ ℚ_[p]))).toSubmodule)
    (hX : X ∈
      L.localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceAmbientSet
        p)
    (hY : Y ∈
      skewAdjointFormElementaryPadicUniformCoordinateBall
        p
        (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p +
          padicValInt p L.pairingDeterminant)
        L.rationalFormMatrix (L.form_symm.map _)
          L.rationalFormMatrix_det_ne_zero) :
    X + Y ∈
      L.localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceAmbientSet
        p := by
  let k :=
    L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p
  obtain ⟨Xz, hXzmap, hXzmem⟩ :=
    L.exists_integral_skewAdjoint_lift_mem_span_pow_of_mem_densityCongruenceSourceAmbientSet
      p hp2 X hX
  obtain ⟨Yz, hYzmap, hYzmem⟩ :=
    L.exists_integral_skewAdjoint_lift_mem_span_pow_of_mem_formElementaryUniformCoordinateBall_add_pairingDeterminantVal
      p k Y hY
  have hmap :
      ((Xz + Yz :
          (skewAdjointMatricesLieSubalgebra
            (L.pairingMatrix_padic p)).toSubmodule) :
        Matrix (Fin n) (Fin n) ℤ_[p]).map
          PadicInt.Coe.ringHom =
        ((X + Y :
          (skewAdjointMatricesLieSubalgebra
            (L.rationalFormMatrix.map (algebraMap ℚ ℚ_[p]))).toSubmodule) :
          Matrix (Fin n) (Fin n) ℚ_[p]) := by
    simp only [Submodule.coe_add, Matrix.map_add _ (fun a b ↦
      map_add PadicInt.Coe.ringHom a b), hXzmap, hYzmap]
  have hmem : ∀ i j,
      ((Xz + Yz :
          (skewAdjointMatricesLieSubalgebra
            (L.pairingMatrix_padic p)).toSubmodule) :
        Matrix (Fin n) (Fin n) ℤ_[p]) i j ∈
          (Ideal.span {(p : ℤ_[p]) ^ k} : Ideal ℤ_[p]) := by
    intro i j
    exact Ideal.add_mem _ (hXzmem i j) (hYzmem i j)
  exact
    L.mem_localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceAmbientSet_of_integral_skewAdjoint_lift_mem_span_pow
      p (X + Y) (Xz + Yz) hmap hmem

/-- The explicit determinant-loss form-coordinate ball acts by additive
translations on the odd-prime density source: membership is unchanged by any
such translation. -/
theorem
    add_mem_localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceAmbientSet_iff_of_mem_formElementaryBall_add_pairingDeterminantVal
    (L : PositiveDefiniteIntegralLattice n) (p : ℕ) [Fact (Nat.Prime p)] (hp2 : p ≠ 2)
    (X Y :
      (skewAdjointMatricesLieSubalgebra
        (L.rationalFormMatrix.map (algebraMap ℚ ℚ_[p]))).toSubmodule)
    (hY : Y ∈
      skewAdjointFormElementaryPadicUniformCoordinateBall
        p
        (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p +
          padicValInt p L.pairingDeterminant)
        L.rationalFormMatrix (L.form_symm.map _)
          L.rationalFormMatrix_det_ne_zero) :
    X + Y ∈
        L.localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceAmbientSet
          p ↔
      X ∈
        L.localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceAmbientSet
          p := by
  have hnegY : -Y ∈
      skewAdjointFormElementaryPadicUniformCoordinateBall
        p
        (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p +
          padicValInt p L.pairingDeterminant)
        L.rationalFormMatrix (L.form_symm.map _)
          L.rationalFormMatrix_det_ne_zero := by
    apply
      (mem_skewAdjointFormElementaryPadicUniformCoordinateBall_iff_upper
        p
        (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p +
          padicValInt p L.pairingDeterminant)
        L.rationalFormMatrix (L.form_symm.map _)
          L.rationalFormMatrix_det_ne_zero (-Y)).2
    intro q
    have hq :=
      (mem_skewAdjointFormElementaryPadicUniformCoordinateBall_iff_upper
        p
        (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth p +
          padicValInt p L.pairingDeterminant)
        L.rationalFormMatrix (L.form_symm.map _)
          L.rationalFormMatrix_det_ne_zero Y).1 hY q
    simpa using hq
  constructor
  · intro hXY
    have h :=
      L.add_mem_localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceAmbientSet_of_mem_formElementaryBall_add_pairingDeterminantVal
        p hp2 (X + Y) (-Y) hXY hnegY
    simpa [add_assoc] using h
  · intro hX
    exact
      L.add_mem_localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceAmbientSet_of_mem_formElementaryBall_add_pairingDeterminantVal
        p hp2 X Y hX hY

end PositiveDefiniteIntegralLattice
