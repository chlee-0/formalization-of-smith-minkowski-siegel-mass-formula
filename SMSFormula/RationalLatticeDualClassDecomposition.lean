import SMSFormula.RationalLatticeCosetClassTube
import SMSFormula.AdelicGaussianShellRationalDilation
import SMSFormula.RationalAdeleDilatedFactorTubeLimit

/-!
# The dilated dual indicator as a sum over the discriminant group (dual test)

`A = ℤⁿ/Sℤⁿ` is the `PolarDiscriminantGroup` and `d = |det S|`.

* `discriminantResidue : A →+ (ℤ/d)ⁿ`, `[u] ↦ adj(S) u mod d`, is well defined and injective, and an integer
  residue `r` lies in its image iff `S r ≡ 0 (mod d)` (`mem_range_discriminantResidue_iff`).
* The dilated dual indicator `1_{L^#}(·/d)` (`realDilatedPolarDualIndicator`) equals
  `Σ_{a ∈ A} 1_{U_a}`, `U_a = {x ∈ Ẑⁿ : x ≡ adj(S) a (mod d)}` (`realDilatedPolarDualIndicator_eq_sum`): it is a
  residue function at level `d` whose value at the lift of `r` is `[S r ≡ 0 (mod d)]`.
* Rank four: the class tube masses along `j!` converge (`tendsto_dualClassTubeLimit`), to `d²/d⁴ · ∏'δ^{cos}_p(u, λ)`
  at the target `q(adj(S)u) + d²λ` and to `0` at every target `≢ q(adj(S)u) (mod d²)`; hence the tube masses of the
  dilated dual indicator converge to `Σ_a` of the class limits (`tendsto_finiteTubeMass_realDilatedPolarDualIndicator`).
Nothing is chosen: the classes are indexed by `A` itself.
-/

noncomputable section

open MeasureTheory Filter Topology Finset RationalQuadraticSpaceMatrix
open scoped Matrix

namespace PositiveDefiniteIntegralLattice

open IntegralFiniteAdelePhase

variable {n : ℕ}

/-! ## The discriminant class residue -/

/-- `u ↦ adj(S) u mod d` as an additive hom. -/
def adjugateResidueHom (L : PositiveDefiniteIntegralLattice n) :
    (Fin n → ℤ) →+ (Fin n → ZMod L.polarGramMatrix.det.natAbs) :=
  ((Int.castAddHom (ZMod L.polarGramMatrix.det.natAbs)).compLeft (Fin n)).comp
    (Matrix.mulVecLin L.polarGramMatrix.adjugate).toAddMonoidHom

theorem adjugateResidueHom_apply (L : PositiveDefiniteIntegralLattice n) (u : Fin n → ℤ) :
    L.adjugateResidueHom u = L.adjugateResidue u := rfl

theorem intCast_det_eq_zero (L : PositiveDefiniteIntegralLattice n) :
    ((L.polarGramMatrix.det : ℤ) : ZMod L.polarGramMatrix.det.natAbs) = 0 := by
  rw [← L.natAbs_det_eq, Int.cast_natCast]
  exact ZMod.natCast_self L.polarGramMatrix.det.natAbs

theorem polarGramRange_le_ker_adjugateResidueHom (L : PositiveDefiniteIntegralLattice n) :
    L.polarGramRange ≤ L.adjugateResidueHom.ker := by
  intro u hu
  obtain ⟨y, rfl⟩ := (L.mem_polarGramRange_iff u).1 hu
  rw [AddMonoidHom.mem_ker, adjugateResidueHom_apply]
  funext i
  simp only [adjugateResidue, Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec,
    Matrix.one_mulVec, Pi.smul_apply, smul_eq_mul, Int.cast_mul, L.intCast_det_eq_zero, zero_mul,
    Pi.zero_apply]

/-- The discriminant class residue `[u] ↦ adj(S) u mod d`. -/
def discriminantResidue (L : PositiveDefiniteIntegralLattice n) :
    L.PolarDiscriminantGroup →+ (Fin n → ZMod L.polarGramMatrix.det.natAbs) :=
  QuotientAddGroup.lift L.polarGramRange L.adjugateResidueHom L.polarGramRange_le_ker_adjugateResidueHom

theorem discriminantResidue_mk (L : PositiveDefiniteIntegralLattice n) (u : Fin n → ℤ) :
    L.discriminantResidue (u : L.PolarDiscriminantGroup) = L.adjugateResidue u := rfl

theorem discriminantResidue_injective (L : PositiveDefiniteIntegralLattice n) :
    Function.Injective L.discriminantResidue := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  induction a using QuotientAddGroup.induction_on with
  | H u =>
  rw [discriminantResidue_mk] at ha
  rw [QuotientAddGroup.eq_zero_iff]
  have hdiv : ∀ i, (L.polarGramMatrix.det.natAbs : ℤ) ∣ (L.polarGramMatrix.adjugate *ᵥ u) i := fun i ↦ by
    have := congrFun ha i
    simp only [adjugateResidue, Pi.zero_apply] at this
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 this
  choose t ht using hdiv
  refine (L.mem_polarGramRange_iff u).2 ⟨t, ?_⟩
  have hD := L.natAbs_det_eq
  have h1 : L.polarGramMatrix *ᵥ (L.polarGramMatrix.adjugate *ᵥ u) = L.polarGramMatrix.det • u := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_adjugate, Matrix.smul_mulVec, Matrix.one_mulVec]
  have h2 : L.polarGramMatrix.adjugate *ᵥ u = L.polarGramMatrix.det • t := by
    funext i
    rw [ht i, hD]
    rfl
  rw [h2, Matrix.mulVec_smul] at h1
  funext i
  have := congrFun h1 i
  simp only [Pi.smul_apply, smul_eq_mul] at this
  exact mul_left_cancel₀ L.polarGramMatrix_det_ne_zero this

/-- An integer residue is a discriminant class residue iff `S r ≡ 0 (mod d)`. -/
theorem mem_range_discriminantResidue_iff (L : PositiveDefiniteIntegralLattice n) (r : Fin n → ℤ) :
    (fun i ↦ ((r i : ℤ) : ZMod L.polarGramMatrix.det.natAbs)) ∈ Set.range L.discriminantResidue ↔
      ∀ i, (L.polarGramMatrix.det.natAbs : ℤ) ∣ (L.polarGramMatrix *ᵥ r) i := by
  have hD := L.natAbs_det_eq
  constructor
  · rintro ⟨a, ha⟩
    induction a using QuotientAddGroup.induction_on with
    | H u =>
    rw [discriminantResidue_mk] at ha
    have hdiv : ∀ i, (L.polarGramMatrix.det.natAbs : ℤ) ∣ r i - (L.polarGramMatrix.adjugate *ᵥ u) i := fun i ↦ by
      have := congrFun ha i
      simp only [adjugateResidue] at this
      exact (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1 this
    choose t ht using hdiv
    have hr : r = L.polarGramMatrix.adjugate *ᵥ u + L.polarGramMatrix.det • t := by
      funext i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [← hD]
      linarith [ht i]
    intro i
    rw [hr, Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mul_adjugate, Matrix.smul_mulVec,
      Matrix.one_mulVec, Matrix.mulVec_smul]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [← hD]
    exact dvd_add (dvd_mul_right _ _) (dvd_mul_right _ _)
  · intro h
    choose s hs using h
    refine ⟨(s : L.PolarDiscriminantGroup), ?_⟩
    rw [discriminantResidue_mk]
    have h1 : L.polarGramMatrix.adjugate *ᵥ (L.polarGramMatrix *ᵥ r) = L.polarGramMatrix.det • r := by
      rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec]
    have h2 : L.polarGramMatrix *ᵥ r = L.polarGramMatrix.det • s := by
      funext i
      rw [hs i, hD]
      rfl
    rw [h2, Matrix.mulVec_smul] at h1
    funext i
    have := congrFun h1 i
    simp only [Pi.smul_apply, smul_eq_mul] at this
    have h3 := mul_left_cancel₀ L.polarGramMatrix_det_ne_zero this
    simp only [adjugateResidue, h3]

/-! ## The dilated dual indicator at integral points -/

theorem finiteAdelicPolarMatrix_mulVec_intVector (L : PositiveDefiniteIntegralLattice n) (q : ℚ) (r : Fin n → ℤ) :
    L.rationalQuadraticSpaceMatrix.finiteAdelicPolarMatrix *ᵥ
        (algebraMap ℚ RationalFiniteAdele q • fun i ↦ algebraMap ℚ RationalFiniteAdele ((r i : ℤ) : ℚ)) =
      fun i ↦ algebraMap ℚ RationalFiniteAdele (q * (((L.polarGramMatrix *ᵥ r) i : ℤ) : ℚ)) := by
  rw [L.rationalQuadraticSpaceMatrix_finiteAdelicPolarMatrix_eq_map_polarGramMatrix, Matrix.mulVec_smul]
  funext i
  simp only [Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, Matrix.map_apply, map_mul,
    Int.cast_sum, Int.cast_mul, map_sum, map_intCast, eq_intCast]

/-- The dilated dual indicator at an integral vector `r`: `1_{L^#}(r/d) = [S r ≡ 0 (mod d)]`. -/
theorem realDilatedPolarDualIndicator_intVector (L : PositiveDefiniteIntegralLattice n) (r : Fin n → ℤ) :
    realDilatedPolarDualIndicator L (fun i ↦ algebraMap ℚ RationalFiniteAdele ((r i : ℤ) : ℚ)) =
      if ∀ i, (L.polarGramMatrix.det.natAbs : ℤ) ∣ (L.polarGramMatrix *ᵥ r) i then 1 else 0 := by
  classical
  have hd0 : ((L.polarGramMatrix.det.natAbs : ℕ) : ℚ) ≠ 0 := by exact_mod_cast L.natAbs_det_ne_zero
  unfold realDilatedPolarDualIndicator realFinitePolarDualLatticeIndicator finitePolarDualLatticeIndicator
  rw [show (L.polarDeterminant.natAbs : ℚ) = (L.polarGramMatrix.det.natAbs : ℚ) from rfl,
    finiteAdelicPolarMatrix_mulVec_intVector]
  by_cases h : ∀ i, (L.polarGramMatrix.det.natAbs : ℤ) ∣ (L.polarGramMatrix *ᵥ r) i
  · rw [if_pos h, rationalFiniteAdeleVectorIntegralIndicator_of_mem, Complex.one_re]
    intro i
    obtain ⟨c, hc⟩ := h i
    refine (rational_mem_integralFiniteAdeleSubring_iff _).2 ⟨c, ?_⟩
    rw [hc, Int.cast_mul, Int.cast_natCast, eq_intCast, inv_mul_cancel_left₀ hd0]
  · rw [if_neg h, rationalFiniteAdeleVectorIntegralIndicator_of_not_mem, Complex.zero_re]
    intro hmem
    apply h
    intro i
    obtain ⟨c, hc⟩ := (rational_mem_integralFiniteAdeleSubring_iff _).1 (hmem i)
    refine ⟨c, ?_⟩
    have hc' : (c : ℚ) = ((L.polarGramMatrix.det.natAbs : ℚ))⁻¹ * (((L.polarGramMatrix *ᵥ r) i : ℤ) : ℚ) := hc
    have h1 : ((((L.polarGramMatrix *ᵥ r) i : ℤ)) : ℚ) = (((L.polarGramMatrix.det.natAbs : ℤ) * c : ℤ) : ℚ) := by
      rw [Int.cast_mul, Int.cast_natCast, hc', mul_inv_cancel_left₀ hd0]
    exact_mod_cast h1

/-- The dilated dual indicator is the sum of the discriminant class indicators. -/
theorem realDilatedPolarDualIndicator_eq_sum (L : PositiveDefiniteIntegralLattice n) (x : Fin n → RationalFiniteAdele) :
    ((realDilatedPolarDualIndicator L x : ℝ) : ℂ) =
      ∑ a : L.PolarDiscriminantGroup,
        residueRestrictedIndicator n L.polarGramMatrix.det.natAbs {L.discriminantResidue a} x := by
  classical
  have hcar := isStandardCarried_realDilatedPolarDualIndicator L
  have hper : IsStandardPeriodic L.polarGramMatrix.det.natAbs
      (fun y ↦ ((realDilatedPolarDualIndicator L y : ℝ) : ℂ)) :=
    isStandardPeriodic_realDilatedPolarDualIndicator L
  rw [eq_sum_residueRestrictedIndicator hcar hper x]
  have hval : ∀ ρ : Fin n → ZMod L.polarGramMatrix.det.natAbs,
      ((realDilatedPolarDualIndicator L (residueFiniteAdeleLift _ ρ) : ℝ) : ℂ) =
        if ρ ∈ Set.range L.discriminantResidue then 1 else 0 := by
    intro ρ
    have hlift : residueFiniteAdeleLift L.polarGramMatrix.det.natAbs ρ =
        fun i ↦ algebraMap ℚ RationalFiniteAdele ((((ρ i).val : ℤ)) : ℚ) := rfl
    have hρ : ρ = fun i ↦ ((((ρ i).val : ℤ)) : ZMod L.polarGramMatrix.det.natAbs) := by
      funext i
      simp
    have hiff : ρ ∈ Set.range L.discriminantResidue ↔
        ∀ i, (L.polarGramMatrix.det.natAbs : ℤ) ∣ (L.polarGramMatrix *ᵥ fun i ↦ ((ρ i).val : ℤ)) i := by
      have := L.mem_range_discriminantResidue_iff (fun i ↦ ((ρ i).val : ℤ))
      rwa [← hρ] at this
    rw [hlift, realDilatedPolarDualIndicator_intVector]
    by_cases h : ρ ∈ Set.range L.discriminantResidue
    · rw [if_pos (hiff.1 h), if_pos h, Complex.ofReal_one]
    · rw [if_neg (fun h' ↦ h (hiff.2 h')), if_neg h, Complex.ofReal_zero]
  simp_rw [hval, ite_mul, one_mul, zero_mul]
  rw [← Finset.sum_filter]
  rw [show (Finset.univ.filter fun ρ ↦ ρ ∈ Set.range L.discriminantResidue) =
      Finset.univ.image L.discriminantResidue by
    ext ρ
    simp]
  rw [Finset.sum_image fun a _ b _ h ↦ L.discriminantResidue_injective h]

theorem finiteTubeMass_realDilatedPolarDualIndicator (L : PositiveDefiniteIntegralLattice n) (w : ℕ) (M : ℤ) :
    L.finiteTubeMass (fun x ↦ ((realDilatedPolarDualIndicator L x : ℝ) : ℂ)) w M =
      ∑ a : L.PolarDiscriminantGroup,
        L.finiteTubeMass (residueRestrictedIndicator n L.polarGramMatrix.det.natAbs {L.discriminantResidue a})
          w M := by
  unfold finiteTubeMass
  simp_rw [realDilatedPolarDualIndicator_eq_sum, Finset.sum_mul]
  rw [integral_finset_sum _ fun a _ ↦ L.integrable_residueRestrictedIndicator_mul_tube _ _ _ _,
    Finset.mul_sum]

/-! ## The class tube limits (rank four) -/

/-- The `j!`-tube limit of the discriminant class `a` at the target `M`. -/
def dualClassTubeLimit (L : PositiveDefiniteIntegralLattice n) (a : L.PolarDiscriminantGroup) (M : ℤ) : ℂ :=
  limUnder atTop fun j ↦ L.finiteTubeMass
    (residueRestrictedIndicator n L.polarGramMatrix.det.natAbs {L.discriminantResidue a}) (Nat.factorial j) M

theorem tendsto_dualClassTubeLimit_of_eq (L : PositiveDefiniteIntegralLattice 4) (u : Fin 4 → ℤ) (lam : ℤ)
    (hM : L.cosetStandardTarget u lam ≠ 0) :
    Tendsto (fun j ↦ L.finiteTubeMass
        (residueRestrictedIndicator 4 L.polarGramMatrix.det.natAbs {L.discriminantResidue u}) (Nat.factorial j)
        (L.cosetStandardTarget u lam)) atTop
      (𝓝 ((L.polarGramMatrix.det.natAbs : ℂ) ^ 2 / (L.polarGramMatrix.det.natAbs : ℂ) ^ 4 *
        ∏' p : Nat.Primes, ((L.cosetLocalDensity u lam p : ℝ) : ℂ))) := by
  rw [discriminantResidue_mk]
  exact L.tendsto_finiteTubeMass_adjugateClass u lam hM

theorem dualClassTubeLimit_of_eq (L : PositiveDefiniteIntegralLattice 4) (u : Fin 4 → ℤ) (lam : ℤ)
    (hM : L.cosetStandardTarget u lam ≠ 0) :
    L.dualClassTubeLimit u (L.cosetStandardTarget u lam) =
      (L.polarGramMatrix.det.natAbs : ℂ) ^ 2 / (L.polarGramMatrix.det.natAbs : ℂ) ^ 4 *
        ∏' p : Nat.Primes, ((L.cosetLocalDensity u lam p : ℝ) : ℂ) :=
  (L.tendsto_dualClassTubeLimit_of_eq u lam hM).limUnder_eq

theorem tendsto_dualClassTubeLimit_of_ne (L : PositiveDefiniteIntegralLattice n) (u : Fin n → ℤ) {M : ℤ}
    (hM : ∀ lam : ℤ, M ≠ L.cosetStandardTarget u lam) :
    Tendsto (fun j ↦ L.finiteTubeMass
        (residueRestrictedIndicator n L.polarGramMatrix.det.natAbs {L.discriminantResidue u}) (Nat.factorial j) M)
      atTop (𝓝 0) := by
  rw [discriminantResidue_mk]
  exact tendsto_const_nhds.congr'
    ((L.eventually_finiteTubeMass_adjugateClass_eq_zero u hM).mono fun j hj ↦ hj.symm)

theorem dualClassTubeLimit_of_ne (L : PositiveDefiniteIntegralLattice n) (u : Fin n → ℤ) {M : ℤ}
    (hM : ∀ lam : ℤ, M ≠ L.cosetStandardTarget u lam) : L.dualClassTubeLimit u M = 0 :=
  (L.tendsto_dualClassTubeLimit_of_ne u hM).limUnder_eq

/-- Every class tube converges (rank four, `M ≠ 0`). -/
theorem tendsto_dualClassTubeLimit (L : PositiveDefiniteIntegralLattice 4) (a : L.PolarDiscriminantGroup) {M : ℤ}
    (hM : M ≠ 0) :
    Tendsto (fun j ↦ L.finiteTubeMass
        (residueRestrictedIndicator 4 L.polarGramMatrix.det.natAbs {L.discriminantResidue a}) (Nat.factorial j) M)
      atTop (𝓝 (L.dualClassTubeLimit a M)) := by
  induction a using QuotientAddGroup.induction_on with
  | H u =>
  by_cases h : ∃ lam, M = L.cosetStandardTarget u lam
  · obtain ⟨lam, rfl⟩ := h
    rw [L.dualClassTubeLimit_of_eq u lam hM]
    exact L.tendsto_dualClassTubeLimit_of_eq u lam hM
  · push_neg at h
    rw [L.dualClassTubeLimit_of_ne u h]
    exact L.tendsto_dualClassTubeLimit_of_ne u h

/-- The dilated dual indicator's tube limit is the sum of the class limits (rank four). -/
theorem tendsto_finiteTubeMass_realDilatedPolarDualIndicator (L : PositiveDefiniteIntegralLattice 4) {M : ℤ} (hM : M ≠ 0) :
    Tendsto (fun j ↦ L.finiteTubeMass (fun x ↦ ((realDilatedPolarDualIndicator L x : ℝ) : ℂ))
        (Nat.factorial j) M) atTop (𝓝 (∑ a, L.dualClassTubeLimit a M)) := by
  simp_rw [finiteTubeMass_realDilatedPolarDualIndicator]
  exact tendsto_finset_sum _ fun a _ ↦ L.tendsto_dualClassTubeLimit a hM

end PositiveDefiniteIntegralLattice
