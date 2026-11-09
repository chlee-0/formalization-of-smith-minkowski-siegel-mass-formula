import SMSFormula.AdelicGaussianCapstoneBadSetRequirement
import SMSFormula.AdelicGaussianShellWeightRationalIdentity
import SMSFormula.RationalQuadraticComplementIntegralLattice

/-!
# The presentation denominator of an integral presentation is supported on the bad set

Let `E` be the block-to-ambient matrix of a presentation `P` of the anisotropic complement of `x`:
`E (z, a) = a x + e(z)`.  If `x` and the images `e(e_k)` of the standard basis vectors are integral,
`E` is an integer matrix, `E⁻¹ = adj(E)/det(E)` has denominators dividing `det E`, and
`det(E)² · det F_V = det F_block`.  So every prime of the presentation denominator `D_P`
divides `det F_block` and is odd-unimodular bad for the block.  With the enlarged bad set this
gives the denominator hypothesis `hden` with `S := B`.  Nothing is chosen.
-/

noncomputable section

open PositiveDefiniteIntegralLattice

namespace RationalQuadraticSpaceMatrix
namespace AnisotropicComplementPresentation

variable {n m : ℕ} {V : RationalQuadraticSpaceMatrix n} {x : Fin n → ℚ}
variable (P : V.AnisotropicComplementPresentation x m)

theorem eq_complementInclude_add_lineInclude (y : Fin (m + 1) → ℚ) :
    y = nonisotropicLastComplementInclude (fun i ↦ y i.castSucc) +
      nonisotropicLastLineInclude (y (Fin.last m)) := by
  funext i
  cases i using Fin.lastCases <;>
    simp [nonisotropicLastComplementInclude, nonisotropicLastLineInclude]

/-- The block-to-ambient matrix is integral when `x` and the complement images of the basis vectors
are integral. -/
theorem blockToAmbientRationalMatrix_mem_intRange (hx : V.nativeRationalQuadraticForm x ≠ 0)
    (hxint : ∀ i, x i ∈ (algebraMap ℤ ℚ).range)
    (hcomp : ∀ (k : Fin m) (i : Fin n),
      ((P.complementIsometry (Pi.single k 1) : V.anisotropicRationalOrthogonalComplement x) :
        Fin n → ℚ) i ∈ (algebraMap ℤ ℚ).range)
    (i : Fin n) (j : Fin (m + 1)) :
    P.blockToAmbientRationalMatrix hx i j ∈ (algebraMap ℤ ℚ).range := by
  rw [blockToAmbientRationalMatrix, LinearMap.toMatrix'_apply]
  change P.blockToAmbientIsometryEquiv hx (Pi.single j 1) i ∈ (algebraMap ℤ ℚ).range
  rw [eq_complementInclude_add_lineInclude (Pi.single j (1 : ℚ)), blockToAmbientIsometryEquiv_apply]
  cases j using Fin.lastCases with
  | last =>
    have h0 : (fun k : Fin m ↦ (Pi.single (Fin.last m) (1 : ℚ) : Fin (m + 1) → ℚ) k.castSucc) = 0 := by
      funext k
      exact Pi.single_eq_of_ne (Fin.castSucc_ne_last k) _
    rw [h0, map_zero, Pi.single_eq_same, one_smul, ZeroMemClass.coe_zero, add_zero]
    exact hxint i
  | cast k =>
    have h1 : (fun k' : Fin m ↦ (Pi.single k.castSucc (1 : ℚ) : Fin (m + 1) → ℚ) k'.castSucc) =
        Pi.single k 1 := by
      funext k'
      by_cases hk : k' = k
      · subst hk; simp
      · rw [Pi.single_eq_of_ne (fun h ↦ hk (Fin.castSucc_injective _ h)), Pi.single_eq_of_ne hk]
    rw [h1, Pi.single_eq_of_ne (Fin.castSucc_ne_last k).symm, zero_smul, zero_add]
    exact hcomp k i

end AnisotropicComplementPresentation
end RationalQuadraticSpaceMatrix

namespace RationalQuadraticSpaceMatrix
namespace AnisotropicComplementPresentation

variable {m : ℕ} {V : RationalQuadraticSpaceMatrix (m + 1)} {x : Fin (m + 1) → ℚ}
variable (P : V.AnisotropicComplementPresentation x m)

/-- Off the odd-unimodular bad places of the block, an integral presentation has `p ∤ D_P`. -/
theorem not_dvd_presentationDenominator_of_integral (L : PositiveDefiniteIntegralLattice (m + 1))
    (hV : V = L.rationalQuadraticSpaceMatrix) (hx : V.nativeRationalQuadraticForm x ≠ 0)
    (hE : ∀ i j, P.blockToAmbientRationalMatrix hx i j ∈ (algebraMap ℤ ℚ).range)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ)
    (hv : v ∉ (P.blockSpace hx).cliffordSpinCandidateOddUnimodularBadPlaces) :
    ¬ (Rat.HeightOneSpectrum.primesEquiv v : ℕ) ∣ P.presentationDenominator hx := by
  classical
  subst hV
  have hp : (Rat.HeightOneSpectrum.primesEquiv v : ℕ).Prime := (Rat.HeightOneSpectrum.primesEquiv v).2
  choose Ez hEz using hE
  let Mz : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ := Matrix.of fun i j ↦ Ez i j
  have hEmap : P.blockToAmbientRationalMatrix hx = Mz.map (Int.cast : ℤ → ℚ) := by
    ext i j
    simp only [Matrix.map_apply, Mz, Matrix.of_apply]
    rw [← hEz i j]
    rfl
  have hdetE : (P.blockToAmbientRationalMatrix hx).det = (Mz.det : ℚ) := by
    rw [hEmap]
    exact ((Int.castRingHom ℚ).map_det Mz).symm
  have hEinv : P.ambientToBlockRationalMatrix hx = (P.blockToAmbientRationalMatrix hx)⁻¹ :=
    (Matrix.inv_eq_right_inv (P.blockToAmbientRationalMatrix_mul_ambientToBlockRationalMatrix hx)).symm
  have hden_inv : ∀ i j, ((P.ambientToBlockRationalMatrix hx i j).den : ℤ) ∣ Mz.det := by
    intro i j
    have hadj : (Mz.map (Int.cast : ℤ → ℚ)).adjugate = Mz.adjugate.map (Int.cast : ℤ → ℚ) :=
      ((Int.castRingHom ℚ).map_adjugate Mz).symm
    have hentry : P.ambientToBlockRationalMatrix hx i j = ((Mz.adjugate i j : ℤ) : ℚ) / (Mz.det : ℚ) := by
      rw [hEinv, Matrix.inv_def, hdetE, Matrix.smul_apply, smul_eq_mul, hEmap, hadj, Matrix.map_apply,
        Ring.inverse_eq_inv, div_eq_inv_mul]
    rw [hentry, ← Rat.divInt_eq_div]
    exact Rat.den_dvd _ _
  have hden_E : ∀ i j, (P.blockToAmbientRationalMatrix hx i j).den = 1 := by
    intro i j
    rw [← hEz i j]
    simp
  -- p ∣ D_P forces p ∣ det E
  intro hdvd
  have hprod1 : (∏ i, ∏ j, (P.blockToAmbientRationalMatrix hx i j).den) = 1 :=
    Finset.prod_eq_one fun i _ ↦ Finset.prod_eq_one fun j _ ↦ hden_E i j
  unfold presentationDenominator at hdvd
  rw [hprod1, one_mul] at hdvd
  obtain ⟨i, -, hi⟩ := (Prime.dvd_finset_prod_iff hp.prime _).1 hdvd
  obtain ⟨j, -, hj⟩ := (Prime.dvd_finset_prod_iff hp.prime _).1 hi
  have hpdz : ((Rat.HeightOneSpectrum.primesEquiv v : ℕ) : ℤ) ∣ Mz.det :=
    dvd_trans (Int.natCast_dvd_natCast.2 hj) (hden_inv i j)
  -- det F_block = (det E)² det F_V is an integer divisible by p
  have hblock : (P.blockSpace hx).pairingMatrix.det = ((Mz.det ^ 2 * L.pairingMatrix.det : ℤ) : ℚ) := by
    have h := P.blockToAmbientRationalMatrix_det_sq_mul hx
    have hB : (P.blockSpace hx).pairingMatrix.det =
        P.lowerSpace.pairingMatrix.det * L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x :=
      nonisotropicLastBlockMatrix_det _ _
    have hF : L.rationalQuadraticSpaceMatrix.pairingMatrix.det = ((L.pairingMatrix.det : ℤ) : ℚ) := by
      rw [show L.rationalQuadraticSpaceMatrix.pairingMatrix = L.pairingMatrix.map (algebraMap ℤ ℚ) from rfl]
      exact ((algebraMap ℤ ℚ).map_det L.pairingMatrix).symm
    rw [hB, ← h, hdetE, hF]
    push_cast
    ring
  have hnum : (P.blockSpace hx).pairingMatrix.det.num = Mz.det ^ 2 * L.pairingMatrix.det := by
    rw [hblock, Rat.num_intCast]
  have hpnum : (Rat.HeightOneSpectrum.primesEquiv v : ℕ) ∣
      (P.blockSpace hx).pairingMatrix.det.num.natAbs := by
    rw [hnum]
    exact Int.natCast_dvd.1 (Dvd.dvd.mul_right (dvd_pow hpdz two_ne_zero) _)
  apply hv
  rw [mem_cliffordSpinCandidateOddUnimodularBadPlaces_iff, Rat.matrixPairBadPrimeSet,
    Nat.mem_primeFactors]
  refine ⟨hp, ?_, ?_⟩
  · unfold Rat.matrixPairBadPrimeSupportNat
    exact (((Dvd.dvd.mul_left hpnum _).mul_right _).mul_right _).mul_right _
  · have hdp : Rat.matrixDenominatorProduct (P.blockSpace hx).pairingMatrix ≠ 0 := by
      unfold Rat.matrixDenominatorProduct
      rw [Finset.prod_ne_zero_iff]
      intro i _
      rw [Finset.prod_ne_zero_iff]
      intro j _
      exact Rat.den_ne_zero _
    have hn0 : (P.blockSpace hx).pairingMatrix.det.num.natAbs ≠ 0 :=
      Int.natAbs_ne_zero.2 (Rat.num_ne_zero.2 (P.blockSpace hx).form_det_ne_zero)
    have hd0 : (P.blockSpace hx).pairingMatrix.det.den ≠ 0 := Rat.den_ne_zero _
    unfold Rat.matrixPairBadPrimeSupportNat
    positivity

end AnisotropicComplementPresentation
end RationalQuadraticSpaceMatrix

namespace PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase

local instance ipdDecidableEqK : DecidableEq (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  Classical.decEq _

/-- With the enlarged bad set and an integral presentation, no prime outside `B` divides the
presentation denominator (the hypothesis `hden` with `S := B`). -/
theorem capstone_hden_self {s : ℕ} (L : PositiveDefiniteIntegralLattice (s + 2 + 1)) {x : Fin (s + 2 + 1) → ℚ}
    (P : L.rationalQuadraticSpaceMatrix.AnisotropicComplementPresentation x (s + 2))
    (hx : L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x ≠ 0)
    (hE : ∀ i j, P.blockToAmbientRationalMatrix hx i j ∈ (algebraMap ℤ ℚ).range)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ)
    (hv : v ∉ P.lowerSpace.lastExtensionHorizontalBadPlaces
          (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x) hx ∪
        (P.blockSpace hx).cliffordGeneralSpinHorizontalIntegralBadPlaces) :
    ¬ (Rat.HeightOneSpectrum.primesEquiv v : ℕ) ∣ P.presentationDenominator hx := by
  classical
  refine P.not_dvd_presentationDenominator_of_integral L rfl hx hE v fun h ↦ hv ?_
  exact Finset.mem_union_left _ (P.lowerSpace.mem_lastExtensionHorizontalBadPlaces_of_oddUnimodular _ hx h)

end PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase

namespace PositiveDefiniteIntegralLattice

/-- Existence of an integral presentation: for an integral vector `x` with `Q(x) ≠ 0` there is an
integral complement lattice with an isometry whose block-to-ambient matrix is integral. -/
theorem exists_integralLatticeAnisotropicComplementPresentation_integral {m : ℕ}
    (L : PositiveDefiniteIntegralLattice (m + 1)) (x : Fin (m + 1) → ℚ)
    (hx : L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm x ≠ 0)
    (hxint : ∀ i, x i ∈ (algebraMap ℤ ℚ).range) :
    ∃ LW : PositiveDefiniteIntegralLattice m, ∃ e : LW.rationalQuadraticSpaceMatrix.quadraticForm.IsometryEquiv
        (L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm.orthogonalRestriction x),
      ∀ i j, (RationalQuadraticSpaceMatrix.integralLatticeAnisotropicComplementPresentation LW L.rationalQuadraticSpaceMatrix x e
        |>.blockToAmbientRationalMatrix hx i j) ∈ (algebraMap ℤ ℚ).range := by
  obtain ⟨LW, e, he⟩ := L.exists_integralLattice_isometryEquiv_orthogonalRestriction_integral x hx
  exact ⟨LW, e, fun i j ↦
    (RationalQuadraticSpaceMatrix.integralLatticeAnisotropicComplementPresentation LW L.rationalQuadraticSpaceMatrix x e)
      |>.blockToAmbientRationalMatrix_mem_intRange hx hxint he i j⟩

end PositiveDefiniteIntegralLattice
