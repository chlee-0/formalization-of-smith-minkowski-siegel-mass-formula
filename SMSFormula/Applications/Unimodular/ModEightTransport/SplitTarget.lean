import SMSFormula.Applications.Unimodular.ModEightTransport.NativeTransport
import SMSFormula.Applications.Unimodular.E8PowerSeedMass

/-!
# Split hyperbolic targets for the Type II mod-eight transport route

This module builds the concrete common split target used by the
normal-form route.  It does not classify arbitrary Type II forms; it proves that
once a lattice has a packaged mod-eight certificate to this target, the existing
native-count adapter compares it with the repository seed in the same rank.
-/

noncomputable section
open Matrix PositiveDefiniteIntegralLattice

namespace TypeIIModEightCertificates

/-- Reflexive finite Gram-congruence certificate. -/
def reflCertificate {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι R) : GramCongruenceCertificate A A where
  changeMatrix := 1
  inverseMatrix := 1
  congruence := by simp
  mul_inverse := by simp
  inverse_mul := by simp

/-- The repository block-sum matrix over `ZMod 8` is the generic finite-certificate
block sum reindexed to the stored `Fin (m+n)` coordinates. -/
theorem blockSumMatrix_eq_reindex_sumBlock {m n : ℕ}
    (A : Matrix (Fin m) (Fin m) R) (B : Matrix (Fin n) (Fin n) R) :
    PositiveDefiniteIntegralLattice.blockSumMatrix A B =
      Matrix.reindex finSumFinEquiv finSumFinEquiv (sumBlockMatrix A B) := by
  ext i j
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
  cases i <;> cases j <;> simp [PositiveDefiniteIntegralLattice.blockSumMatrix, sumBlockMatrix]

/-- The split hyperbolic target in rank `8*k`, grouped as one `H^4` block per E8 block. -/
def hyperbolicSplitTarget : (k : ℕ) → Matrix (Fin (8 * k)) (Fin (8 * k)) R
  | 0 => 1
  | k + 1 =>
      Matrix.reindex (finCongr (by omega : 8 * k + 8 = 8 * (k + 1)))
        (finCongr (by omega : 8 * k + 8 = 8 * (k + 1)))
        (PositiveDefiniteIntegralLattice.blockSumMatrix (hyperbolicSplitTarget k) H4)

/-- The stored E8-power Type II seed has the split hyperbolic mod-eight normal form. -/
def typeIISeedSplitCertificate : (k : ℕ) →
    GramCongruenceCertificate
      ((PositiveDefiniteIntegralLattice.typeIISeed k).pairingMatrix.map (Int.cast : ℤ → R))
      (hyperbolicSplitTarget k)
  | 0 => by
      simpa [PositiveDefiniteIntegralLattice.typeIISeed, hyperbolicSplitTarget] using
        (reflCertificate (1 : Matrix (Fin 0) (Fin 0) R))
  | k + 1 => by
      let h : 8 * k + 8 = 8 * (k + 1) := by omega
      let Cfin : GramCongruenceCertificate
          (Matrix.reindex finSumFinEquiv finSumFinEquiv
            (sumBlockMatrix (((PositiveDefiniteIntegralLattice.typeIISeed k).pairingMatrix).map (Int.cast : ℤ → R))
              (PositiveDefiniteIntegralLattice.e8CartanMatrix.map (Int.cast : ℤ → R))))
          (Matrix.reindex finSumFinEquiv finSumFinEquiv
            (sumBlockMatrix (hyperbolicSplitTarget k) H4)) :=
        finBlockCertificate (typeIISeedSplitCertificate k) e8ToH4Certificate
      have hs :
          (PositiveDefiniteIntegralLattice.blockSumMatrix (PositiveDefiniteIntegralLattice.typeIISeed k).pairingMatrix
              PositiveDefiniteIntegralLattice.e8CartanMatrix).map (Int.cast : ℤ → R) =
            Matrix.reindex finSumFinEquiv finSumFinEquiv
              (sumBlockMatrix (((PositiveDefiniteIntegralLattice.typeIISeed k).pairingMatrix).map (Int.cast : ℤ → R))
                (PositiveDefiniteIntegralLattice.e8CartanMatrix.map (Int.cast : ℤ → R))) :=
        blockSumMatrix_map_zmodEight (PositiveDefiniteIntegralLattice.typeIISeed k).pairingMatrix
          PositiveDefiniteIntegralLattice.e8CartanMatrix
      have ht :
          PositiveDefiniteIntegralLattice.blockSumMatrix (hyperbolicSplitTarget k) H4 =
            Matrix.reindex finSumFinEquiv finSumFinEquiv
              (sumBlockMatrix (hyperbolicSplitTarget k) H4) :=
        blockSumMatrix_eq_reindex_sumBlock (hyperbolicSplitTarget k) H4
      let C0 : GramCongruenceCertificate
          ((PositiveDefiniteIntegralLattice.blockSumMatrix (PositiveDefiniteIntegralLattice.typeIISeed k).pairingMatrix
              PositiveDefiniteIntegralLattice.e8CartanMatrix).map (Int.cast : ℤ → R))
          (PositiveDefiniteIntegralLattice.blockSumMatrix (hyperbolicSplitTarget k) H4) := by
        rw [hs, ht]
        exact Cfin
      let C := reindexCertificate (finCongr h) C0
      simpa [PositiveDefiniteIntegralLattice.typeIISeed, hyperbolicSplitTarget, PositiveDefiniteIntegralLattice.blockSumLattice_pairingMatrix,
        PositiveDefiniteIntegralLattice.reindexLattice_pairingMatrix, PositiveDefiniteIntegralLattice.e8Lattice_pairingMatrix] using C

end TypeIIModEightCertificates

namespace TypeIIModEightNativeTransport

/-- A certificate from a rank-`8*k` lattice to the split target compares its
native dyadic count with the checked Type II seed in the same rank. -/
theorem native_count_eq_typeIISeed_of_split_certificate (k : ℕ)
    (L : PositiveDefiniteIntegralLattice (8 * k)) (hL : L.IsUnimodular)
    (C : TypeIIModEightCertificates.GramCongruenceCertificate
      (L.pairingMatrix.map (Int.cast : ℤ → ZMod 8))
      (TypeIIModEightCertificates.hyperbolicSplitTarget k)) :
    associatedBilinearDualQuotientCount L 2 3 =
      associatedBilinearDualQuotientCount (PositiveDefiniteIntegralLattice.typeIISeed k) 2 3 :=
  native_count_eq_of_common_target_certificate L (PositiveDefiniteIntegralLattice.typeIISeed k) hL
    (PositiveDefiniteIntegralLattice.typeIISeed_isUnimodular k) C
    (TypeIIModEightCertificates.typeIISeedSplitCertificate k)

/-- The same split certificate compares dyadic local factors with the checked Type II seed. -/
theorem localFactor_eq_typeIISeed_of_split_certificate (k : ℕ)
    (L : PositiveDefiniteIntegralLattice (8 * k)) (hL : L.IsUnimodular)
    (C : TypeIIModEightCertificates.GramCongruenceCertificate
      (L.pairingMatrix.map (Int.cast : ℤ → ZMod 8))
      (TypeIIModEightCertificates.hyperbolicSplitTarget k)) :
    L.massLocalFactor 2 =
      (PositiveDefiniteIntegralLattice.typeIISeed k).massLocalFactor 2 :=
  localFactor_eq_of_common_target_certificate L (PositiveDefiniteIntegralLattice.typeIISeed k) hL
    (PositiveDefiniteIntegralLattice.typeIISeed_isUnimodular k) C
    (TypeIIModEightCertificates.typeIISeedSplitCertificate k)

/-- A split-target certificate in positive rank transports the ordinary genus
mass to the checked E8-power seed in the same rank. -/
theorem ordinaryGenusMass_eq_typeIISeed_of_split_certificate (k : ℕ) (hk : 0 < k)
    (L : PositiveDefiniteIntegralLattice (8 * k)) (hL : L.IsUnimodular)
    (C : TypeIIModEightCertificates.GramCongruenceCertificate
      (L.pairingMatrix.map (Int.cast : ℤ → ZMod 8))
      (TypeIIModEightCertificates.hyperbolicSplitTarget k)) :
    L.ordinaryGenusMass = (PositiveDefiniteIntegralLattice.typeIISeed k).ordinaryGenusMass := by
  have hm : 1 < 4 * k := by nlinarith
  have heven : Even (4 * k) := ⟨2 * k, by omega⟩
  exact mass_eq_of_common_target_certificate_evenHalf_of_rank_eq
    (n := 8 * k) (m := 4 * k) (by omega) hm heven L (PositiveDefiniteIntegralLattice.typeIISeed k) hL
    (PositiveDefiniteIntegralLattice.typeIISeed_isUnimodular k) C
    (TypeIIModEightCertificates.typeIISeedSplitCertificate k)

/-- A split-target certificate in positive rank gives the Type II Bernoulli
ordinary genus mass formula by comparison with the E8-power seed. -/
theorem ordinaryGenusMass_eq_typeIIConstant_of_split_certificate (k : ℕ) (hk : 0 < k)
    (L : PositiveDefiniteIntegralLattice (8 * k)) (hL : L.IsUnimodular)
    (C : TypeIIModEightCertificates.GramCongruenceCertificate
      (L.pairingMatrix.map (Int.cast : ℤ → ZMod 8))
      (TypeIIModEightCertificates.hyperbolicSplitTarget k)) :
    L.ordinaryGenusMass = UnimodularMass.typeIIConstant (8 * k) := by
  rw [ordinaryGenusMass_eq_typeIISeed_of_split_certificate k hk L hL C,
    PositiveDefiniteIntegralLattice.typeIISeed_ordinaryGenusMass_eq_typeIIConstant_of_pos k hk]

end TypeIIModEightNativeTransport

#assert_standard_axioms TypeIIModEightCertificates.reflCertificate
#assert_standard_axioms TypeIIModEightCertificates.blockSumMatrix_eq_reindex_sumBlock
#assert_standard_axioms TypeIIModEightCertificates.hyperbolicSplitTarget
#assert_standard_axioms TypeIIModEightCertificates.typeIISeedSplitCertificate
#assert_standard_axioms TypeIIModEightNativeTransport.native_count_eq_typeIISeed_of_split_certificate
#assert_standard_axioms TypeIIModEightNativeTransport.localFactor_eq_typeIISeed_of_split_certificate
#assert_standard_axioms TypeIIModEightNativeTransport.ordinaryGenusMass_eq_typeIISeed_of_split_certificate
#assert_standard_axioms TypeIIModEightNativeTransport.ordinaryGenusMass_eq_typeIIConstant_of_split_certificate
