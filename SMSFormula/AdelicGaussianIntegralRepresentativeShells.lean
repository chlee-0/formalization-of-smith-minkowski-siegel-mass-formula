import SMSFormula.AdelicGaussianShellRationalDilation

/-!
# Shell identities are needed only at shells with an integral representative

The core theorem needs its representative vector `x` to be integral at the bad places.  Any shell
`b` with a rational representative `x` is carried by the dilation `x ↦ k x` (`k` the product of the
coordinate denominators of `x`) to the shell `k² b`, which has the integral representative `k x`, and
the test `ψ` is carried to `ψ(·/k)`.  The real Gaussian core is stable under this dilation (width
`w ↦ w / k²`, carrier unchanged, period `d ↦ d k`), and the shell identity is dilation-invariant
(`shellIdentity_iff_dilate`).

So `τ(Spin_V) = 1` follows from the shell identities for nonnegative core tests of every width at the
shells that contain an integral vector: exactly where the core theorem's integrality hypothesis is
automatic.  Nothing is chosen in any statement; the denominators are used only inside proofs.
-/

noncomputable section

open MeasureTheory PositiveDefiniteIntegralLattice RationalQuadraticSpaceMatrix
open scoped ENNReal

namespace PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase

variable {n : ℕ}

theorem realShiftedGaussian_smul_center (L : PositiveDefiniteIntegralLattice n) (b : ℝ) {t : ℝ} (ht : t ≠ 0)
    (u x : Fin n → ℝ) :
    realShiftedGaussian L b u (t • x) = realShiftedGaussian L (b * t ^ 2) (t⁻¹ • u) x := by
  rw [realShiftedGaussian_eq, realShiftedGaussian_eq,
    SMSFormula.ShiftedGaussian.quadraticShiftedGaussian_apply,
    SMSFormula.ShiftedGaussian.quadraticShiftedGaussian_apply]
  simp only [ContinuousMap.id_apply]
  have hsplit : t • x - u = t • (x - t⁻¹ • u) := by
    rw [smul_sub, smul_smul, mul_inv_cancel₀ ht, one_smul]
  rw [hsplit, QuadraticMap.map_smul, smul_eq_mul]
  congr 1
  ring

/-- The real Gaussian core is stable under dilation by `1/k`: width `w ↦ w / k²`. -/
theorem comp_rationalDilation_mem_realGaussianCore (L : PositiveDefiniteIntegralLattice n) {w : ℝ} {k : ℕ}
    (hk : k ≠ 0) {f : (Fin n → RationalAdele) → ℝ} (hf : f ∈ realGaussianCore L w) :
    (fun x ↦ f (rationalAdeleVectorRationalDilation ((k : ℚ))⁻¹ x)) ∈
      realGaussianCore L (w * ((k : ℝ))⁻¹ ^ 2) := by
  have hkq : (k : ℚ) ≠ 0 := by exact_mod_cast hk
  have hkr : ((k : ℝ))⁻¹ ≠ 0 := inv_ne_zero (by exact_mod_cast hk)
  have hk1 : (k : RationalFiniteAdele) * algebraMap ℚ RationalFiniteAdele ((k : ℚ))⁻¹ = 1 := by
    rw [← map_natCast (algebraMap ℚ RationalFiniteAdele) k, ← map_mul, mul_inv_cancel₀ hkq, map_one]
  let T : ((Fin n → RationalAdele) → ℝ) →ₗ[ℝ] ((Fin n → RationalAdele) → ℝ) :=
    { toFun := fun f x ↦ f (rationalAdeleVectorRationalDilation ((k : ℚ))⁻¹ x)
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  have hle : realGaussianCore L w ≤ (realGaussianCore L (w * ((k : ℝ))⁻¹ ^ 2)).comap T := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨u, c, d, g, hc, hd, hcar, hper, rfl⟩
    refine Submodule.mem_comap.2 (Submodule.subset_span ⟨(k : ℝ) • u, c, d * k,
      fun y ↦ g (algebraMap ℚ RationalFiniteAdele ((k : ℚ))⁻¹ • y), hc, mul_ne_zero hd hk, ?_, ?_, ?_⟩)
    · intro y hy
      refine hcar _ fun hmem ↦ hy ?_
      change c • y ∈ integralFiniteAdeleVectors n
      have hmem' : c • (algebraMap ℚ RationalFiniteAdele ((k : ℚ))⁻¹ • y) ∈
          integralFiniteAdeleVectors n := hmem
      intro i
      have hi := hmem' i
      simp only [Pi.smul_apply, nsmul_eq_mul, smul_eq_mul] at hi ⊢
      have hrw : (c : RationalFiniteAdele) * y i =
          (k : RationalFiniteAdele) *
            ((c : RationalFiniteAdele) * (algebraMap ℚ RationalFiniteAdele ((k : ℚ))⁻¹ * y i)) := by
        rw [show (k : RationalFiniteAdele) *
            ((c : RationalFiniteAdele) * (algebraMap ℚ RationalFiniteAdele ((k : ℚ))⁻¹ * y i)) =
            ((k : RationalFiniteAdele) * algebraMap ℚ RationalFiniteAdele ((k : ℚ))⁻¹) *
              ((c : RationalFiniteAdele) * y i) by ring, hk1, one_mul]
      rw [hrw]
      exact Subring.mul_mem _ (by exact_mod_cast algebraMap_intCast_mem_integralFiniteAdeleSubring k) hi
    · intro y v hv
      have hshift : algebraMap ℚ RationalFiniteAdele ((k : ℚ))⁻¹ • (y + (d * k) • v) =
          algebraMap ℚ RationalFiniteAdele ((k : ℚ))⁻¹ • y + d • v := by
        rw [smul_add]
        congr 1
        funext i
        rw [Pi.smul_apply, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, nsmul_eq_mul, nsmul_eq_mul,
          Nat.cast_mul]
        rw [show algebraMap ℚ RationalFiniteAdele ((k : ℚ))⁻¹ *
            ((d : RationalFiniteAdele) * (k : RationalFiniteAdele) * v i) =
            ((k : RationalFiniteAdele) * algebraMap ℚ RationalFiniteAdele ((k : ℚ))⁻¹) *
              ((d : RationalFiniteAdele) * v i) by ring, hk1, one_mul]
      simp only
      rw [hshift]
      exact hper _ v hv
    · funext x
      change realShiftedGaussian L w u (rationalAdeleVectorRealPart n
          (rationalAdeleVectorRationalDilation ((k : ℚ))⁻¹ x)) *
          g (rationalAdeleVectorFinitePart n (rationalAdeleVectorRationalDilation ((k : ℚ))⁻¹ x)) =
        realShiftedGaussian L (w * ((k : ℝ))⁻¹ ^ 2) ((k : ℝ) • u) (rationalAdeleVectorRealPart n x) *
          g (algebraMap ℚ RationalFiniteAdele ((k : ℚ))⁻¹ • rationalAdeleVectorFinitePart n x)
      rw [rationalAdeleVectorRealPart_rationalDilation, rationalAdeleVectorFinitePart_rationalDilation]
      push_cast
      rw [realShiftedGaussian_smul_center L w hkr, inv_inv]
  exact hle hf

/-- The dilated core member. -/
def realGaussianCoreDilate (L : PositiveDefiniteIntegralLattice n) {w : ℝ} {k : ℕ} (hk : k ≠ 0)
    (ψ : realGaussianCore L w) : realGaussianCore L (w * ((k : ℝ))⁻¹ ^ 2) :=
  ⟨fun x ↦ ψ.val (rationalAdeleVectorRationalDilation ((k : ℚ))⁻¹ x),
    comp_rationalDilation_mem_realGaussianCore L hk ψ.property⟩

end PositiveDefiniteIntegralLattice.IntegralFiniteAdelePhase

namespace PositiveDefiniteIntegralLattice

/-- Every rational vector has a positive integer multiple with integral coordinates. -/
theorem exists_nat_smul_integral {n : ℕ} (x : Fin n → ℚ) :
    ∃ k : ℕ, k ≠ 0 ∧ ∃ z : Fin n → ℤ, (fun i ↦ (z i : ℚ)) = (k : ℚ) • x := by
  classical
  refine ⟨∏ i, (x i).den, Finset.prod_ne_zero_iff.2 fun i _ ↦ Rat.den_ne_zero _, ?_⟩
  have hint : ∀ i, ∃ z : ℤ, (z : ℚ) = (∏ j, (x j).den : ℕ) * x i := by
    intro i
    obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem (fun j ↦ (x j).den) (Finset.mem_univ i)
    refine ⟨c * (x i).num, ?_⟩
    rw [hc]
    push_cast
    rw [mul_comm ((x i).den : ℚ) (c : ℚ), mul_assoc, Rat.den_mul_eq_num]
  choose z hz using hint
  exact ⟨z, funext fun i ↦ by rw [hz i]; rfl⟩

/-- Reduction to integral representatives: if the shell identity holds for every nonnegative core test
of every width at every shell containing an integral vector, then it holds for every core test at
every shell. -/
theorem shellIdentity_of_integralRepresentative
    {r : ℕ} (L : PositiveDefiniteIntegralLattice (r + 2)) [Nonempty (Fin (r + 2))] (hr : 1 ≤ r)
    (inst : Fintype L.ConcreteProperRationalDoubleCosetSet)
    {P : ℝ} (hP : 0 < P) (hconv : massLocalInverseProductTendsTo L P)
    (hshell : ∀ (w : ℝ), 0 < w → ∀ ψ : IntegralFiniteAdelePhase.realGaussianCore L w,
      (∀ y, 0 ≤ ψ.val y) →
      ∀ b : L.rationalQuadraticSpaceMatrix.RepresentedNonzeroRationalNorm,
      (∃ z : Fin (r + 2) → ℤ,
        L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm (fun i ↦ (z i : ℚ)) = b.1) →
      L.probabilityNormalizedFullAdelicCliffordGeneralSpinRepresentedNormTheta hr inst hP hconv b
          (fun y ↦ ENNReal.ofReal (ψ.val y)) rationalIdeleClassUnitLogCutoff *
        (cliffordSpinCandidateRawOnoTamagawaDataOfLattice
          L (by omega) inst hP hconv).spinTamagawaNumberENNReal =
      ENNReal.ofReal (L.rationalQuadraticSpaceMatrix.realValueDensity ψ.val
        (algebraMap ℚ RationalAdele b.1)))
    {w : ℝ} (hw : 0 < w) (ψ : IntegralFiniteAdelePhase.realGaussianCore L w)
    (hψ : ∀ y, 0 ≤ ψ.val y) (b : L.rationalQuadraticSpaceMatrix.RepresentedNonzeroRationalNorm) :
    L.probabilityNormalizedFullAdelicCliffordGeneralSpinRepresentedNormTheta hr inst hP hconv b
        (fun y ↦ ENNReal.ofReal (ψ.val y)) rationalIdeleClassUnitLogCutoff *
      (cliffordSpinCandidateRawOnoTamagawaDataOfLattice
        L (by omega) inst hP hconv).spinTamagawaNumberENNReal =
    ENNReal.ofReal (L.rationalQuadraticSpaceMatrix.realValueDensity ψ.val
      (algebraMap ℚ RationalAdele b.1)) := by
  obtain ⟨x, hx⟩ := b.2.2
  obtain ⟨k, hk, z, hz⟩ := exists_nat_smul_integral x
  have hkq : (k : ℚ) ≠ 0 := by exact_mod_cast hk
  have hw' : 0 < w * ((k : ℝ))⁻¹ ^ 2 := by
    have : (0 : ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero hk
    positivity
  have h := hshell _ hw' (IntegralFiniteAdelePhase.realGaussianCoreDilate L hk ψ)
    (fun y ↦ hψ _) (RepresentedNonzeroRationalNorm.dilate _ b hkq) ⟨z, by
      rw [hz, QuadraticMap.map_smul, hx, smul_eq_mul, RepresentedNonzeroRationalNorm.dilate_coe]
      ring⟩
  exact (L.shellIdentity_iff_dilate hr inst hP hconv ψ.val b hkq rationalIdeleClassUnitLogCutoff).1 h

/-- The theta–Eisenstein comparison at integral representatives: `τ(Spin_V) = 1` from the shell
identities for nonnegative core tests at the shells containing an integral vector (where the
core theorem's integrality hypothesis `hxint` is automatic), for a width `a` with `C(a) ≠ 1`. -/
theorem spinTamagawaNumberENNReal_eq_one_of_integralRepresentativeShellIdentities
    {r : ℕ} (L : PositiveDefiniteIntegralLattice (r + 2)) [Nonempty (Fin (r + 2))] (hr : 1 ≤ r)
    (hrank : 5 ≤ r + 2) (inst : Fintype L.ConcreteProperRationalDoubleCosetSet)
    {P : ℝ} (hP : 0 < P) (hconv : massLocalInverseProductTendsTo L P)
    {a : ℝ} (ha : 0 < a)
    (hC : (L.polarRealDeterminantScale : ℝ)⁻¹ * (1 / a ^ (1 / 2 : ℝ)) ^ (r + 2) ≠ 1)
    (hshell : ∀ (w : ℝ), 0 < w → ∀ ψ : IntegralFiniteAdelePhase.realGaussianCore L w,
      (∀ y, 0 ≤ ψ.val y) →
      ∀ b : L.rationalQuadraticSpaceMatrix.RepresentedNonzeroRationalNorm,
      (∃ z : Fin (r + 2) → ℤ,
        L.rationalQuadraticSpaceMatrix.nativeRationalQuadraticForm (fun i ↦ (z i : ℚ)) = b.1) →
      L.probabilityNormalizedFullAdelicCliffordGeneralSpinRepresentedNormTheta hr inst hP hconv b
          (fun y ↦ ENNReal.ofReal (ψ.val y)) rationalIdeleClassUnitLogCutoff *
        (cliffordSpinCandidateRawOnoTamagawaDataOfLattice
          L (by omega) inst hP hconv).spinTamagawaNumberENNReal =
      ENNReal.ofReal (L.rationalQuadraticSpaceMatrix.realValueDensity ψ.val
        (algebraMap ℚ RationalAdele b.1))) :
    (cliffordSpinCandidateRawOnoTamagawaDataOfLattice
      L (by omega) inst hP hconv).spinTamagawaNumberENNReal = 1 := by
  have hD : (0 : ℝ) < (L.polarDeterminant.natAbs : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Int.natAbs_ne_zero.2 L.polarDeterminant_pos.ne')
  refine L.spinTamagawaNumberENNReal_eq_one_of_integerCoreShellIdentities hr hrank inst hP hconv ha hC
    (fun b _ ↦ L.shellIdentity_of_integralRepresentative hr inst hP hconv hshell ha
      (IntegralFiniteAdelePhase.polarGaussianLatticeCore L a)
      (IntegralFiniteAdelePhase.polarGaussianLatticeCore_nonneg L a) b)
    (fun b _ ↦ L.shellIdentity_of_integralRepresentative hr inst hP hconv hshell
      (by positivity) (IntegralFiniteAdelePhase.polarGaussianDualDilatedCore L a⁻¹)
      (IntegralFiniteAdelePhase.polarGaussianDualDilatedCore_nonneg L a⁻¹) b)

end PositiveDefiniteIntegralLattice
