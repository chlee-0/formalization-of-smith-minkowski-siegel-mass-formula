import SMSFormula.PadicSpecialOrthogonalDifferentialDensityDyadicRelativeFactorStability
import SMSFormula.PadicSpecialOrthogonalDifferentialDensityDyadicDoubledAttainedResidue
import SMSFormula.PadicSpecialOrthogonalDifferentialDensityDyadicPredecessorTranslation

/-!
# Halving relative scaled dyadic Cayley differences

For two elements of the shifted dyadic denominator subgroup, the difference
of their integral scaled Cayley coordinates is integrally skew-adjoint.  If
its entries are divisible by the complete selected power `2^k`, it admits an
integral skew-adjoint half divisible by `2^(k-1)`.  The numerator two in the
forward Cayley formula then places the half coordinate in the actual dyadic
density source.

Reducing the identity `2V=D` at the original level proves that the finite
residue of the scaled-coordinate difference belongs to the literal doubled
attained image.  Conversely, a doubled attained witness and the exact
residue-preimage lift recover complete-depth entrywise divisibility.  Thus
relative principal-kernel membership is identified with the literal doubled
attained residue relation.  No additive closure, quotient, cardinality, or
gauge value is asserted in this module.
-/

noncomputable section

open Matrix
open scoped Matrix Matrix.Norms.Operator

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

local instance fact_prime_two_scaled_difference : Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

/-- Scalar extension of an integral skew-adjoint dyadic coordinate to the
rational dyadic skew-adjoint carrier. -/
def localPadicSpecialOrthogonalDifferentialDyadicIntegralSkewAdjointToPadic
    (L : PositiveDefiniteIntegralLattice n)
    (Xz :
      (skewAdjointMatricesLieSubalgebra
        (L.pairingMatrix_padic 2)).toSubmodule) :
    (skewAdjointMatricesLieSubalgebra
      (L.rationalFormMatrix.map (algebraMap ℚ ℚ_[2]))).toSubmodule := by
  let Xq : Matrix (Fin n) (Fin n) ℚ_[2] :=
    (Xz : Matrix (Fin n) (Fin n) ℤ_[2]).map PadicInt.Coe.ringHom
  refine ⟨Xq, ?_⟩
  apply (mem_ker_skewAdjointOperator_iff _ _).mp
  apply LinearMap.mem_ker.mpr
  have hXz :
      skewAdjointOperator (L.pairingMatrix_padic 2)
          (Xz : Matrix (Fin n) (Fin n) ℤ_[2]) = 0 :=
    LinearMap.mem_ker.mp
      ((mem_ker_skewAdjointOperator_iff _ _).mpr Xz.property)
  have hmap :
      (skewAdjointOperator (L.pairingMatrix_padic 2)
          (Xz : Matrix (Fin n) (Fin n) ℤ_[2])).map PadicInt.Coe.ringHom =
        skewAdjointOperator
          (L.rationalFormMatrix.map (algebraMap ℚ ℚ_[2])) Xq := by
    simp only [skewAdjointOperator_apply]
    rw [Matrix.map_add _ (fun a b ↦ map_add PadicInt.Coe.ringHom a b),
      Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map,
      L.rationalFormMatrix_map_padic_eq_pairingMatrix_padicField]
    rfl
  rw [← hmap, hXz]
  simp

@[simp] theorem
    coe_localPadicSpecialOrthogonalDifferentialDyadicIntegralSkewAdjointToPadic
    (L : PositiveDefiniteIntegralLattice n)
    (Xz :
      (skewAdjointMatricesLieSubalgebra
        (L.pairingMatrix_padic 2)).toSubmodule) :
    (L.localPadicSpecialOrthogonalDifferentialDyadicIntegralSkewAdjointToPadic
        Xz : Matrix (Fin n) (Fin n) ℚ_[2]) =
      (Xz : Matrix (Fin n) (Fin n) ℤ_[2]).map PadicInt.Coe.ringHom :=
  rfl

/-- The integral scaled-coordinate difference, as an element of the integral
skew-adjoint module. -/
def
    localPadicSpecialOrthogonalDifferentialDensityDyadicScaledDifferenceIntegral
    (L : PositiveDefiniteIntegralLattice n)
    (g h :
      L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceSubgroup) :
    (skewAdjointMatricesLieSubalgebra
      (L.pairingMatrix_padic 2)).toSubmodule :=
  L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceScaledInverseCayleyIntegral
      g -
    L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceScaledInverseCayleyIntegral
      h

@[simp] theorem
    coe_localPadicSpecialOrthogonalDifferentialDensityDyadicScaledDifferenceIntegral
    (L : PositiveDefiniteIntegralLattice n)
    (g h :
      L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceSubgroup) :
    (L.localPadicSpecialOrthogonalDifferentialDensityDyadicScaledDifferenceIntegral
        g h : Matrix (Fin n) (Fin n) ℤ_[2]) =
      L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceScaledInverseCayleyMatrix
          g -
        L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceScaledInverseCayleyMatrix
          h :=
  rfl

/-- The residue of the absolute scaled-coordinate difference in the enlarged
determinant-loss carrier. -/
def
    localPadicSpecialOrthogonalDifferentialDensityDyadicScaledDifferenceResidue
    (L : PositiveDefiniteIntegralLattice n)
    (g h :
      L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceSubgroup) :
    L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicDeterminantLossResidue :=
  L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceScaledDeterminantLossResidue
      g -
    L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceScaledDeterminantLossResidue
      h

/-- The underlying finite residue is the reduction of the literal difference
of the two absolute scaled form-coordinate points. -/
theorem
    coe_localPadicSpecialOrthogonalDifferentialDensityDyadicScaledDifferenceResidue
    (L : PositiveDefiniteIntegralLattice n)
    (g h :
      L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceSubgroup) :
    (L.localPadicSpecialOrthogonalDifferentialDensityDyadicScaledDifferenceResidue
        g h).1 =
      skewAdjointFormElementaryPadicCoordinateReduction
        2
        (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueLevel
          2)
        L.rationalFormMatrix (L.form_symm.map _)
          L.rationalFormMatrix_det_ne_zero
        (L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceScaledFormCoordinatePoint
            g -
          L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceScaledFormCoordinatePoint
            h) := by
  rw [map_sub]
  rfl

/-- Entrywise complete-depth divisibility supplies an integral skew-adjoint
half of the scaled-coordinate difference, with exact predecessor
divisibility. -/
theorem
    exists_integralSkewAdjoint_half_scaledDifference_of_entriesMemIdeal
    (L : PositiveDefiniteIntegralLattice n)
    (g h :
      L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceSubgroup)
    (hD : Matrix.entriesMemIdeal
      (Ideal.span
        {(2 : ℤ_[2]) ^
          L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth 2})
      (L.localPadicSpecialOrthogonalDifferentialDensityDyadicScaledDifferenceIntegral
        g h : Matrix (Fin n) (Fin n) ℤ_[2])) :
    ∃ Vz :
        (skewAdjointMatricesLieSubalgebra
          (L.pairingMatrix_padic 2)).toSubmodule,
      (2 : ℤ_[2]) • (Vz : Matrix (Fin n) (Fin n) ℤ_[2]) =
        (L.localPadicSpecialOrthogonalDifferentialDensityDyadicScaledDifferenceIntegral
          g h : Matrix (Fin n) (Fin n) ℤ_[2]) ∧
      Matrix.entriesMemIdeal
        (Ideal.span
          {(2 : ℤ_[2]) ^
            (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth 2 - 1)})
        (Vz : Matrix (Fin n) (Fin n) ℤ_[2]) := by
  let k :=
    L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth 2
  let D : Matrix (Fin n) (Fin n) ℤ_[2] :=
    L.localPadicSpecialOrthogonalDifferentialDensityDyadicScaledDifferenceIntegral
      g h
  obtain ⟨V, htwo, hVmem⟩ :=
    Matrix.exists_padicIntMatrix_half_mem_span_pow_pred
      k (by
        exact le_trans (by norm_num : 1 ≤ 2)
          (L.two_le_localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth
            2))
      D hD
  have hDop : skewAdjointOperator (L.pairingMatrix_padic 2) D = 0 :=
    LinearMap.mem_ker.mp
      ((mem_ker_skewAdjointOperator_iff _ _).mpr
        (L.localPadicSpecialOrthogonalDifferentialDensityDyadicScaledDifferenceIntegral
          g h).property)
  have hVopTwo :
      (2 : ℤ_[2]) • skewAdjointOperator (L.pairingMatrix_padic 2) V = 0 := by
    rw [← LinearMap.map_smul, htwo, hDop]
  have hVop : skewAdjointOperator (L.pairingMatrix_padic 2) V = 0 := by
    apply Matrix.ext
    intro i j
    have hij := congr_fun (congr_fun hVopTwo i) j
    simp only [Matrix.smul_apply, Matrix.zero_apply, smul_eq_mul] at hij
    exact (mul_eq_zero.mp hij).resolve_left (by norm_num)
  let Vz :
      (skewAdjointMatricesLieSubalgebra
        (L.pairingMatrix_padic 2)).toSubmodule :=
    ⟨V,
      (mem_ker_skewAdjointOperator_iff _ _).mp
        (LinearMap.mem_ker.mpr hVop)⟩
  exact ⟨Vz, htwo, hVmem⟩

/-- A predecessor-divisible integral skew-adjoint dyadic coordinate belongs
to the actual selected density source. -/
theorem
    integralSkewAdjointToPadic_mem_dyadicDensitySource_of_entriesMemIdeal_pred
    (L : PositiveDefiniteIntegralLattice n)
    (Vz :
      (skewAdjointMatricesLieSubalgebra
        (L.pairingMatrix_padic 2)).toSubmodule)
    (hV : Matrix.entriesMemIdeal
      (Ideal.span
        {(2 : ℤ_[2]) ^
          (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth 2 - 1)})
      (Vz : Matrix (Fin n) (Fin n) ℤ_[2])) :
    L.localPadicSpecialOrthogonalDifferentialDyadicIntegralSkewAdjointToPadic
        Vz ∈
      L.localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceAmbientSet
        2 := by
  let k :=
    L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth 2
  let V : Matrix (Fin n) (Fin n) ℤ_[2] := Vz
  have hk : 2 ≤ k :=
    L.two_le_localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth 2
  have hzero : Matrix.entriesMemIdeal
      (Ideal.span {(2 : ℤ_[2]) ^ (k - 1)})
      (0 : Matrix (Fin n) (Fin n) ℤ_[2]) := by
    intro i j
    simp
  obtain ⟨_, hVsource, hforward⟩ :=
    Matrix.entriesMemIdeal_cayleyRingForwardMatrix_add_sub_dyadic_pred
      k hk (0 : Matrix (Fin n) (Fin n) ℤ_[2]) V hzero hV
  have hCzero :
      cayleyRingForwardMatrix (0 : Matrix (Fin n) (Fin n) ℤ_[2]) = 1 := by
    simp [cayleyRingForwardMatrix]
  have hreduce : ∀ i j,
      PadicInt.toZModPow k (cayleyRingForwardMatrix V i j) =
        (1 : Matrix (Fin n) (Fin n) (ZMod (2 ^ k))) i j := by
    intro i j
    have hij := hforward i j
    rw [zero_add, hCzero] at hij
    have hker :
        (cayleyRingForwardMatrix V - 1) i j ∈
          RingHom.ker (PadicInt.toZModPow k) := by
      simpa only [PadicInt.ker_toZModPow] using hij
    rw [RingHom.mem_ker] at hker
    change
      PadicInt.toZModPow k
          (cayleyRingForwardMatrix V i j -
            (1 : Matrix (Fin n) (Fin n) ℤ_[2]) i j) = 0 at hker
    rw [map_sub] at hker
    have hone :
        PadicInt.toZModPow k
            ((1 : Matrix (Fin n) (Fin n) ℤ_[2]) i j) =
          (1 : Matrix (Fin n) (Fin n) (ZMod (2 ^ k))) i j := by
      by_cases hij' : i = j <;> simp [Matrix.one_apply, hij']
    rw [hone] at hker
    exact sub_eq_zero.mp hker
  exact
    L.mem_localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceAmbientSet_of_integral_forwardCayley_reduction
      2
      (L.localPadicSpecialOrthogonalDifferentialDyadicIntegralSkewAdjointToPadic
        Vz)
      Vz rfl (by simpa only [zero_add] using hVsource) hreduce

/-- Complete-depth divisibility of a scaled-coordinate difference places its
finite residue in the literal doubled original attained image. -/
theorem
    scaledDifferenceResidue_mem_doubledAttainedResidueSet_of_entriesMemIdeal
    (L : PositiveDefiniteIntegralLattice n)
    (g h :
      L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceSubgroup)
    (hD : Matrix.entriesMemIdeal
      (Ideal.span
        {(2 : ℤ_[2]) ^
          L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth 2})
      (L.localPadicSpecialOrthogonalDifferentialDensityDyadicScaledDifferenceIntegral
        g h : Matrix (Fin n) (Fin n) ℤ_[2])) :
    L.localPadicSpecialOrthogonalDifferentialDensityDyadicScaledDifferenceResidue
        g h ∈
      L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicDoubledAttainedResidueSet := by
  obtain ⟨Vz, htwo, hVmem⟩ :=
    L.exists_integralSkewAdjoint_half_scaledDifference_of_entriesMemIdeal
      g h hD
  let Vq :=
    L.localPadicSpecialOrthogonalDifferentialDyadicIntegralSkewAdjointToPadic
      Vz
  have hVsource : Vq ∈
      L.localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceAmbientSet
        2 :=
    L.integralSkewAdjointToPadic_mem_dyadicDensitySource_of_entriesMemIdeal_pred
      Vz hVmem
  let Vs :
      L.localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceAmbientSet
        2 :=
    ⟨Vq, hVsource⟩
  let v :=
    L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicFormCoordinatePoint
      Vs
  let a :
      L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueIndex
        2 := by
    refine
      ⟨skewAdjointFormElementaryPadicCoordinateReduction
          2
          (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueLevel
            2)
          L.rationalFormMatrix (L.form_symm.map _)
            L.rationalFormMatrix_det_ne_zero v, ?_⟩
    exact
      ⟨v,
        L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicFormCoordinatePoint_mem_source
          Vs,
        rfl⟩
  refine ⟨a, ?_⟩
  apply Subtype.ext
  change
    2 • a.1 =
      (L.localPadicSpecialOrthogonalDifferentialDensityDyadicScaledDifferenceResidue
        g h).1
  have htwoq := congrArg
    (fun M : Matrix (Fin n) (Fin n) ℤ_[2] ↦
      M.map PadicInt.Coe.ringHom) htwo
  have htwov : 2 • v =
      L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceScaledFormCoordinatePoint
          g -
        L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceScaledFormCoordinatePoint
          h := by
    apply Subtype.ext
    apply Subtype.ext
    exact htwoq
  change
    2 •
        skewAdjointFormElementaryPadicCoordinateReduction
          2
          (L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueLevel
            2)
          L.rationalFormMatrix (L.form_symm.map _)
            L.rationalFormMatrix_det_ne_zero v = _
  rw [← map_nsmul]
  rw [htwov]
  rw [map_sub]
  rfl

/-- Membership of the finite scaled-coordinate difference in the doubled
attained image recovers complete-depth entrywise divisibility of its literal
integral representative. -/
theorem
    scaledDifference_entriesMemIdeal_of_residue_mem_doubledAttainedResidueSet
    (L : PositiveDefiniteIntegralLattice n)
    (g h :
      L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceSubgroup)
    (hres :
      L.localPadicSpecialOrthogonalDifferentialDensityDyadicScaledDifferenceResidue
          g h ∈
        L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicDoubledAttainedResidueSet) :
    Matrix.entriesMemIdeal
      (Ideal.span
        {(2 : ℤ_[2]) ^
          L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth 2})
      (L.localPadicSpecialOrthogonalDifferentialDensityDyadicScaledDifferenceIntegral
        g h : Matrix (Fin n) (Fin n) ℤ_[2]) := by
  let k :=
    L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth 2
  let m :=
    L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueLevel
      2
  let d :=
    L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceScaledFormCoordinatePoint
        g -
      L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceScaledFormCoordinatePoint
        h
  let D : Matrix (Fin n) (Fin n) ℤ_[2] :=
    L.localPadicSpecialOrthogonalDifferentialDensityDyadicScaledDifferenceIntegral
      g h
  rcases hres with ⟨a, ha⟩
  let x :=
    L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueCenter
      2 a
  have hxsource : x.1 ∈
      L.localPadicSpecialOrthogonalDifferentialDensityCongruenceSourceAmbientSet
        2 :=
    L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueCenter_mem_source
      2 a
  have hred :
      skewAdjointFormElementaryPadicCoordinateReduction
          2 m L.rationalFormMatrix (L.form_symm.map _)
            L.rationalFormMatrix_det_ne_zero d =
        skewAdjointFormElementaryPadicCoordinateReduction
          2 m L.rationalFormMatrix (L.form_symm.map _)
            L.rationalFormMatrix_det_ne_zero (2 • x) := by
    have ha' := congrArg Subtype.val ha
    change
      2 • a.1 =
        (L.localPadicSpecialOrthogonalDifferentialDensityDyadicScaledDifferenceResidue
          g h).1 at ha'
    rw [←
      L.localPadicSpecialOrthogonalDifferentialDensityCongruenceFormCoordinateResidueCenter_reduction
        2 a,
      ← map_nsmul] at ha'
    rw [L.coe_localPadicSpecialOrthogonalDifferentialDensityDyadicScaledDifferenceResidue]
      at ha'
    exact ha'.symm
  have hdiffBall : d.1 - (2 • x).1 ∈
      skewAdjointFormElementaryPadicUniformCoordinateBall
        2 m L.rationalFormMatrix (L.form_symm.map _)
          L.rationalFormMatrix_det_ne_zero :=
    (skewAdjointFormElementaryPadicCoordinateReduction_eq_iff_sub_mem_uniformCoordinateBall
      2 m L.rationalFormMatrix (L.form_symm.map _)
        L.rationalFormMatrix_det_ne_zero (2 • x) d).1 hred
  have hm : m = k + padicValInt 2 L.pairingDeterminant := by
    rfl
  have hdiffBall' : d.1 - (2 • x).1 ∈
      skewAdjointFormElementaryPadicUniformCoordinateBall
        2 (k + padicValInt 2 L.pairingDeterminant)
          L.rationalFormMatrix (L.form_symm.map _)
            L.rationalFormMatrix_det_ne_zero := by
    rwa [← hm]
  obtain ⟨Yz, hYmap, hYmem⟩ :=
    L.exists_integral_skewAdjoint_lift_mem_span_pow_of_mem_formElementaryUniformCoordinateBall_add_pairingDeterminantVal
      2 k (d.1 - (2 • x).1) hdiffBall'
  obtain ⟨Xz, hXmap, hXmem⟩ :=
    L.exists_integral_skewAdjoint_lift_mem_span_pow_pred_of_mem_dyadicDensityCongruenceSourceAmbientSet
      x.1 hxsource
  have htwoXmem : Matrix.entriesMemIdeal
      (Ideal.span {(2 : ℤ_[2]) ^ k})
      ((2 : ℤ_[2]) • (Xz : Matrix (Fin n) (Fin n) ℤ_[2])) := by
    intro i j
    rcases Ideal.mem_span_singleton.mp (hXmem i j) with ⟨z, hz⟩
    apply Ideal.mem_span_singleton.mpr
    refine ⟨z, ?_⟩
    rw [Matrix.smul_apply, smul_eq_mul, hz, ← mul_assoc,
      mul_comm (2 : ℤ_[2]) ((2 : ℤ_[2]) ^ (k - 1)), ← pow_succ,
      Nat.sub_add_cancel (by
        exact le_trans (by norm_num : 1 ≤ 2)
          (L.two_le_localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth
            2))]
  have hDmap : D.map PadicInt.Coe.ringHom =
      (d.1 : Matrix (Fin n) (Fin n) ℚ_[2]) := by
    simp only [D, d,
      localPadicSpecialOrthogonalDifferentialDensityDyadicScaledDifferenceIntegral,
      Submodule.coe_sub,
      Matrix.map_sub _ (fun a b ↦ map_sub PadicInt.Coe.ringHom a b)]
    rfl
  have htwoXmap :
      (((2 : ℤ_[2]) • (Xz : Matrix (Fin n) (Fin n) ℤ_[2])).map
          PadicInt.Coe.ringHom) =
        (2 : ℚ_[2]) • (x.1 : Matrix (Fin n) (Fin n) ℚ_[2]) := by
    calc
      (((2 : ℤ_[2]) • (Xz : Matrix (Fin n) (Fin n) ℤ_[2])).map
          PadicInt.Coe.ringHom) =
          (2 : ℚ_[2]) •
            ((Xz : Matrix (Fin n) (Fin n) ℤ_[2]).map
              PadicInt.Coe.ringHom) := by
        ext i j
        simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul,
          map_mul, map_ofNat]
      _ = (2 : ℚ_[2]) • (x.1 : Matrix (Fin n) (Fin n) ℚ_[2]) := by
        rw [hXmap]
  have hdecompMap :
      (((Yz : Matrix (Fin n) (Fin n) ℤ_[2]) +
          (2 : ℤ_[2]) • (Xz : Matrix (Fin n) (Fin n) ℤ_[2])).map
            PadicInt.Coe.ringHom) =
        D.map PadicInt.Coe.ringHom := by
    rw [Matrix.map_add _ (fun a b ↦ map_add PadicInt.Coe.ringHom a b),
      hYmap, htwoXmap, hDmap]
    change
      (d.1 : Matrix (Fin n) (Fin n) ℚ_[2]) -
          (2 : ℚ_[2]) • (x.1 : Matrix (Fin n) (Fin n) ℚ_[2]) +
        (2 : ℚ_[2]) • (x.1 : Matrix (Fin n) (Fin n) ℚ_[2]) =
      (d.1 : Matrix (Fin n) (Fin n) ℚ_[2])
    abel
  have hdecomp :
      D =
        (Yz : Matrix (Fin n) (Fin n) ℤ_[2]) +
          (2 : ℤ_[2]) • (Xz : Matrix (Fin n) (Fin n) ℤ_[2]) := by
    apply Matrix.ext
    intro i j
    apply PadicInt.ext
    exact congr_fun (congr_fun hdecompMap.symm i) j
  change Matrix.entriesMemIdeal (Ideal.span {(2 : ℤ_[2]) ^ k}) D
  rw [hdecomp]
  intro i j
  exact Ideal.add_mem _ (hYmem i j) (htwoXmem i j)

/-- The relative doubled-attained residue relation is exactly complete-depth
entrywise divisibility of the integral scaled-coordinate difference. -/
theorem
    scaledDifferenceResidue_mem_doubledAttainedResidueSet_iff_entriesMemIdeal
    (L : PositiveDefiniteIntegralLattice n)
    (g h :
      L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceSubgroup) :
    L.localPadicSpecialOrthogonalDifferentialDensityDyadicScaledDifferenceResidue
          g h ∈
        L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicDoubledAttainedResidueSet ↔
      Matrix.entriesMemIdeal
        (Ideal.span
          {(2 : ℤ_[2]) ^
            L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDepth 2})
        (L.localPadicSpecialOrthogonalDifferentialDensityDyadicScaledDifferenceIntegral
          g h : Matrix (Fin n) (Fin n) ℤ_[2]) := by
  constructor
  · exact
      L.scaledDifference_entriesMemIdeal_of_residue_mem_doubledAttainedResidueSet
        g h
  · exact
      L.scaledDifferenceResidue_mem_doubledAttainedResidueSet_of_entriesMemIdeal
        g h

/-- The relative depth-`k` principal-kernel relation is exactly membership of
the scaled-coordinate residue difference in the literal doubled original
attained image. -/
theorem
    mul_inv_mem_dyadicDensityPrincipalKernel_iff_scaledDifferenceResidue_mem_doubledAttainedResidueSet
    (L : PositiveDefiniteIntegralLattice n)
    (g h :
      L.localPadicSpecialOrthogonalDifferentialDensityDyadicDenominatorCongruenceSubgroup) :
    g * h⁻¹ ∈
        L.localPadicSpecialOrthogonalDifferentialDensityPrincipalKernelInDyadicDenominatorCongruence ↔
      L.localPadicSpecialOrthogonalDifferentialDensityDyadicScaledDifferenceResidue
          g h ∈
        L.localPadicSpecialOrthogonalDifferentialDensityCongruenceDyadicDoubledAttainedResidueSet := by
  rw [L.mul_inv_mem_dyadicDensityPrincipalKernel_iff_scaledInverseCayley_sub_entriesMemIdeal]
  rw [L.scaledDifferenceResidue_mem_doubledAttainedResidueSet_iff_entriesMemIdeal]
  rfl

end PositiveDefiniteIntegralLattice
