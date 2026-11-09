import SMSFormula.PadicSpecialOrthogonalDifferentialDensityDyadicAttainedTwoTorsion
import SMSFormula.PadicSpecialOrthogonalDifferentialDensityDyadicTranslation

/-!
# Predecessor-level dyadic density translation

The dyadic forward-Cayley difference contains a scalar factor two.  Retaining
that factor improves the translation theorem by one level: both the source
coordinate and its perturbation need only be divisible by `2^(k-1)` for their
forward Cayley matrices to agree modulo `2^k`.

After the determinant loss, a form-coordinate perturbation at original
residue level minus one has exactly this divisibility.  The strengthened ring
lemma therefore proves that the whole dyadic density source is saturated by
the predecessor form-coordinate ball.  No finite fiber count, quotient, or
gauge value is asserted here.
-/

noncomputable section

open Matrix
open scoped Matrix Matrix.Norms.Operator

namespace Matrix

variable {n : ℕ}

/-- The scalar two in the dyadic forward-Cayley difference recovers one
power: a depth-`k-1` perturbation changes the forward transform only at
depth `k`. -/
theorem entriesMemIdeal_cayleyRingForwardMatrix_add_sub_dyadic_pred
    (k : ℕ) (hk : 2 ≤ k)
    (X Y : Matrix (Fin n) (Fin n) ℤ_[2])
    (hX : entriesMemIdeal
      (Ideal.span {(2 : ℤ_[2]) ^ (k - 1)}) X)
    (hY : entriesMemIdeal
      (Ideal.span {(2 : ℤ_[2]) ^ (k - 1)}) Y) :
    IsUnit (1 - X) ∧
      IsUnit (1 - (X + Y)) ∧
      entriesMemIdeal
        (Ideal.span {(2 : ℤ_[2]) ^ k})
        (cayleyRingForwardMatrix (X + Y) -
          cayleyRingForwardMatrix X) := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hkpred : 1 ≤ k - 1 := by omega
  have hXY : entriesMemIdeal
      (Ideal.span {(2 : ℤ_[2]) ^ (k - 1)}) (X + Y) := by
    intro i j
    exact Ideal.add_mem _ (hX i j) (hY i j)
  have hXunit : IsUnit (1 - X) :=
    padicIntMatrix_one_sub_isUnit_of_mem_span_pow hkpred X hX
  have hXYunit : IsUnit (1 - (X + Y)) :=
    padicIntMatrix_one_sub_isUnit_of_mem_span_pow hkpred (X + Y) hXY
  refine ⟨hXunit, hXYunit, ?_⟩
  let UX : GL (Fin n) ℤ_[2] := hXunit.unit
  let UXY : GL (Fin n) ℤ_[2] := hXYunit.unit
  have hUX : UX.1 = 1 - X := hXunit.unit_spec
  have hUXY : UXY.1 = 1 - (X + Y) := hXYunit.unit_spec
  have hcross := cayleyRingForwardMatrix_sub_cross
    (X + Y) X hXYunit hXunit
  have hright : entriesMemIdeal
      (Ideal.span {(2 : ℤ_[2]) ^ k})
      (cayleyRingTwoMatrix * ((X + Y) - X)) := by
    rw [show (X + Y) - X = Y by abel]
    rw [show cayleyRingTwoMatrix (ι := Fin n) (R := ℤ_[2]) * Y =
        (2 : ℤ_[2]) • Y by
      rw [smul_eq_diagonal_mul]
      rfl]
    intro i j
    rcases Ideal.mem_span_singleton.mp (hY i j) with ⟨z, hz⟩
    apply Ideal.mem_span_singleton.mpr
    refine ⟨z, ?_⟩
    rw [Matrix.smul_apply, smul_eq_mul, hz, ← mul_assoc,
      mul_comm (2 : ℤ_[2]) ((2 : ℤ_[2]) ^ (k - 1)),
      ← pow_succ,
      Nat.sub_add_cancel (by omega : 1 ≤ k)]
  have hequiv :
      entriesMemIdeal
          (Ideal.span {(2 : ℤ_[2]) ^ k})
          (cayleyRingForwardMatrix (X + Y) - cayleyRingForwardMatrix X) ↔
        entriesMemIdeal
          (Ideal.span {(2 : ℤ_[2]) ^ k})
          ((1 - (X + Y)) *
            (cayleyRingForwardMatrix (X + Y) - cayleyRingForwardMatrix X) *
              (1 - X)) := by
    rw [← hUXY, ← hUX,
      entriesMemIdeal_mul_unit_iff,
      entriesMemIdeal_unit_mul_iff]
  apply hequiv.mpr
  rw [hcross]
  exact hright

end Matrix

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

local instance fact_prime_two_predecessor_translation : Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

/-- Adding a perturbation from the predecessor of the original dyadic
residue level preserves the complete selected density source. -/
theorem
    add_mem_dyadicDensityCongruenceSourceAmbientSet_of_mem_formElementaryBall_pred_residueLevel
    (L : PositiveDefiniteIntegralLattice n)
    (X Y :
      (skewAdjointMatricesLieSubalgebra
        (L.rationalFormMatrix.map (algebraMap ℚ ℚ_[2]))).toSubmodule)
    (hX : X ∈
      L.localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceAmbientSet
        2)
    (hY : Y ∈
      skewAdjointFormElementaryPadicUniformCoordinateBall
        2
        (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueLevel
            2 - 1)
        L.rationalFormMatrix (L.form_symm.map _)
          L.rationalFormMatrix_det_ne_zero) :
    X + Y ∈
      L.localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceAmbientSet
        2 := by
  let k :=
    L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth 2
  have hk : 2 ≤ k :=
    L.two_le_localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth 2
  have hlevel :
      (k - 1) + padicValInt 2 L.pairingDeterminant =
        L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueLevel
            2 - 1 := by
    dsimp [k]
    unfold
      localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueLevel
    omega
  have hYlift : Y ∈
      skewAdjointFormElementaryPadicUniformCoordinateBall
        2 ((k - 1) + padicValInt 2 L.pairingDeterminant)
        L.rationalFormMatrix (L.form_symm.map _)
          L.rationalFormMatrix_det_ne_zero := by
    rwa [hlevel]
  obtain ⟨Xz, hXzmap, hXzmem⟩ :=
    L.exists_integral_skewAdjoint_lift_mem_span_pow_pred_of_mem_dyadicDensityCongruenceSourceAmbientSet
      X hX
  obtain ⟨Yz, hYzmap, hYzmem⟩ :=
    L.exists_integral_skewAdjoint_lift_mem_span_pow_of_mem_formElementaryUniformCoordinateBall_add_pairingDeterminantVal
      2 (k - 1) Y hYlift
  obtain ⟨hXzsource, hsumsource, hforwardDiff⟩ :=
    Matrix.entriesMemIdeal_cayleyRingForwardMatrix_add_sub_dyadic_pred
      k hk
      (Xz : Matrix (Fin n) (Fin n) ℤ_[2])
      (Yz : Matrix (Fin n) (Fin n) ℤ_[2])
      hXzmem hYzmem
  obtain ⟨g, hg, hXinv⟩ :=
    L.exists_densityCongruenceKernel_eq_inverseCayley_of_mem_sourceAmbientSet
      2 X hX
  let e :=
    skewAdjointPadicCayleyTranslatedHomeomorph
      L.rationalFormMatrix 2 L.rationalFormMatrix_det_ne_zero 1
  let target :=
    L.localPadicSpecialOrthogonalDifferentialDensityCongruenceTargetPoint
      2 g hg
  have happly :
      e (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceInverseCayley
        2 g hg) = target := by
    exact e.apply_symm_apply target
  have hforwardq :
      cayleyRingForwardMatrix
          (X : Matrix (Fin n) (Fin n) ℚ_[2]) =
        ((g :
          specialFormPreservingMatrixSubgroup
            (L.rationalFormMatrix.map (algebraMap ℚ ℚ_[2]))).1.1.1 :
              Matrix (Fin n) (Fin n) ℚ_[2]) := by
    rw [hXinv]
    calc
      cayleyRingForwardMatrix
          (((L.localPadicSpecialOrthogonalDifferentialDensityCongruenceInverseCayley
              2 g hg).1 : Matrix (Fin n) (Fin n) ℚ_[2])) =
        (e
          (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceInverseCayley
            2 g hg)).1.1.1.1 := by
          rw [coe_skewAdjointPadicCayleyTranslatedHomeomorph_apply]
          change _ =
            (1 : Matrix (Fin n) (Fin n) ℚ_[2]) * _
          rw [Matrix.one_mul]
          rfl
      _ = target.1.1.1.1 := congrArg (fun z ↦ z.1.1.1.1) happly
      _ = _ := rfl
  let gh :=
    L.localPadicSpecialOrthogonalDifferentialStabilizerToHistorical 2 g
  let G : GL (Fin n) ℤ_[2] :=
    L.localPadicLatticeStabilizerIntegralGL 2 gh.1
  have hGmap :
      G.1.map PadicInt.Coe.ringHom =
        ((g :
          specialFormPreservingMatrixSubgroup
            (L.rationalFormMatrix.map (algebraMap ℚ ℚ_[2]))).1.1.1 :
              Matrix (Fin n) (Fin n) ℚ_[2]) := by
    ext i j
    exact L.localPadicLatticeStabilizerIntegralGL_apply 2 gh.1 i j
  have hforwardXz :
      cayleyRingForwardMatrix
          (Xz : Matrix (Fin n) (Fin n) ℤ_[2]) = G.1 := by
    apply Matrix.ext
    intro i j
    apply PadicInt.ext
    have hmap := Matrix.map_cayleyRingForwardMatrix_padicInt
      (Xz : Matrix (Fin n) (Fin n) ℤ_[2]) hXzsource
    have hmap' :
        (cayleyRingForwardMatrix
            (Xz : Matrix (Fin n) (Fin n) ℤ_[2])).map
              PadicInt.Coe.ringHom =
          ((g :
            specialFormPreservingMatrixSubgroup
              (L.rationalFormMatrix.map (algebraMap ℚ ℚ_[2]))).1.1.1 :
                Matrix (Fin n) (Fin n) ℚ_[2]) := by
      exact hmap.trans (by rw [hXzmap, hforwardq])
    exact congrFun (congrFun (hmap'.trans hGmap.symm) i) j
  have hreduceSum : ∀ i j,
      PadicInt.toZModPow k
          (cayleyRingForwardMatrix
            ((Xz : Matrix (Fin n) (Fin n) ℤ_[2]) +
              (Yz : Matrix (Fin n) (Fin n) ℤ_[2])) i j) =
        (1 : Matrix (Fin n) (Fin n) (ZMod (2 ^ k))) i j := by
    intro i j
    have hker := hforwardDiff i j
    have hker' :
        ((cayleyRingForwardMatrix
            ((Xz : Matrix (Fin n) (Fin n) ℤ_[2]) +
              (Yz : Matrix (Fin n) (Fin n) ℤ_[2])) -
          cayleyRingForwardMatrix
            (Xz : Matrix (Fin n) (Fin n) ℤ_[2])) i j) ∈
          RingHom.ker (PadicInt.toZModPow k) := by
      simpa only [PadicInt.ker_toZModPow] using hker
    rw [RingHom.mem_ker] at hker'
    change
      PadicInt.toZModPow k
        (cayleyRingForwardMatrix
            ((Xz : Matrix (Fin n) (Fin n) ℤ_[2]) +
              (Yz : Matrix (Fin n) (Fin n) ℤ_[2])) i j -
          cayleyRingForwardMatrix
            (Xz : Matrix (Fin n) (Fin n) ℤ_[2]) i j) = 0 at hker'
    rw [map_sub] at hker'
    rw [sub_eq_zero.mp hker', hforwardXz]
    exact
      L.localPadicSpecialOrthogonalDifferentialDensityCongruence_reduction_apply
        2 g hg i j
  have hsumMap :
      (((Xz + Yz :
          (skewAdjointMatricesLieSubalgebra
            (L.pairingMatrix_padic 2)).toSubmodule) :
          Matrix (Fin n) (Fin n) ℤ_[2]).map PadicInt.Coe.ringHom) =
        ((X + Y :
          (skewAdjointMatricesLieSubalgebra
            (L.rationalFormMatrix.map (algebraMap ℚ ℚ_[2]))).toSubmodule) :
          Matrix (Fin n) (Fin n) ℚ_[2]) := by
    simp only [Submodule.coe_add, Matrix.map_add _ (fun a b ↦
      map_add PadicInt.Coe.ringHom a b), hXzmap, hYzmap]
  exact
    L.mem_localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceAmbientSet_of_integral_forwardCayley_reduction
      2 (X + Y) (Xz + Yz) hsumMap hsumsource hreduceSum

/-- The predecessor form-coordinate ball acts by additive translations on
the complete dyadic density source. -/
theorem
    add_mem_dyadicDensityCongruenceSourceAmbientSet_iff_of_mem_formElementaryBall_pred_residueLevel
    (L : PositiveDefiniteIntegralLattice n)
    (X Y :
      (skewAdjointMatricesLieSubalgebra
        (L.rationalFormMatrix.map (algebraMap ℚ ℚ_[2]))).toSubmodule)
    (hY : Y ∈
      skewAdjointFormElementaryPadicUniformCoordinateBall
        2
        (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueLevel
            2 - 1)
        L.rationalFormMatrix (L.form_symm.map _)
          L.rationalFormMatrix_det_ne_zero) :
    X + Y ∈
        L.localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceAmbientSet
          2 ↔
      X ∈
        L.localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceAmbientSet
          2 := by
  have hnegY : -Y ∈
      skewAdjointFormElementaryPadicUniformCoordinateBall
        2
        (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueLevel
            2 - 1)
        L.rationalFormMatrix (L.form_symm.map _)
          L.rationalFormMatrix_det_ne_zero := by
    apply
      (mem_skewAdjointFormElementaryPadicUniformCoordinateBall_iff_upper
        2
        (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueLevel
            2 - 1)
        L.rationalFormMatrix (L.form_symm.map _)
          L.rationalFormMatrix_det_ne_zero (-Y)).2
    intro q
    have hq :=
      (mem_skewAdjointFormElementaryPadicUniformCoordinateBall_iff_upper
        2
        (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueLevel
            2 - 1)
        L.rationalFormMatrix (L.form_symm.map _)
          L.rationalFormMatrix_det_ne_zero Y).1 hY q
    simpa using hq
  constructor
  · intro hXY
    have h :=
      L.add_mem_dyadicDensityCongruenceSourceAmbientSet_of_mem_formElementaryBall_pred_residueLevel
        (X + Y) (-Y) hXY hnegY
    simpa [add_assoc] using h
  · intro hX
    exact
      L.add_mem_dyadicDensityCongruenceSourceAmbientSet_of_mem_formElementaryBall_pred_residueLevel
        X Y hX hY

end PositiveDefiniteIntegralLattice
