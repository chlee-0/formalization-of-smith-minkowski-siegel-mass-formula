import SMSFormula.RationalLatticeDiscriminantInvariantVanishing
import SMSFormula.RationalAdeleVectorPeriodicGaussianReparametrized

/-!
# The rational boundary limit of the class theta

For a nonzero integer `c`, an integer `d` and a discriminant class `a`, the class theta
`θ_a(τ) = Σ_{u ∈ a} e(τ q(S⁻¹u))` approaches the rational boundary point `-d/c` as

`√(σⁿ det S⁻¹) · θ_a(-d/c - ε + iσ) → m⁻ⁿ Σ_{r mod m} w_{c,d,a}(r)`

whenever `σ → 0⁺` and `ε/σ → 0` (`tendsto_polarClassTheta_boundary`).  Here `m = 2c²|det S|` is the
column level and `w_{c,d,a}(r) = [r ∈ a] e(-(d/c) q(S⁻¹r))` is the column weight.

The weight is periodic modulo `m ℤⁿ` (`gaussColumnWeight_intCast`):
* the class is unchanged, because `m ℤⁿ ⊆ S ℤⁿ` by the adjugate;
* the phase changes by an integer multiple of `2πi`, via the `polarDualNorm_add_gram` with the shift
  `S·(2c²·sign(det S)·adj(S) k)`.
So the periodic-Gaussian Abel lemma (`tendsto_periodicShiftedMatrixGaussian_along`) applies with the matrix
`S⁻¹`.  The imaginary part of its complex scale is exactly a small real displacement `-ε` of `τ`, which is the
form used for the S-transport of the columns.  Nothing is chosen.
-/

noncomputable section

open Matrix Complex Filter Topology

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ} (L : PositiveDefiniteIntegralLattice n)

noncomputable instance : DecidableEq L.PolarDiscriminantGroup := Classical.decEq _

/-! ## The column level and the rational dual phase -/

/-- The column level `m(c) = 2 c² |det S|`. -/
def gaussColumnLevel (c : ℤ) : ℕ := 2 * c.natAbs ^ 2 * L.polarGramMatrix.det.natAbs

theorem gaussColumnLevel_ne_zero {c : ℤ} (hc : c ≠ 0) : L.gaussColumnLevel c ≠ 0 := by
  unfold gaussColumnLevel
  have h1 : c.natAbs ≠ 0 := Int.natAbs_ne_zero.2 hc
  have h2 : L.polarGramMatrix.det.natAbs ≠ 0 := Int.natAbs_ne_zero.2 L.polarGramMatrix_det_ne_zero
  positivity

theorem gaussColumnLevel_cast (c : ℤ) :
    ((L.gaussColumnLevel c : ℕ) : ℤ) = (2 * c ^ 2 * L.polarGramMatrix.det.sign) * L.polarGramMatrix.det := by
  unfold gaussColumnLevel
  rw [mul_assoc (2 * c ^ 2), Int.sign_mul_self]
  push_cast
  rw [sq_abs]

/-- The rational dual phase `e(x q(S⁻¹u))`. -/
def polarDualPhase (x : ℚ) (u : Fin n → ℤ) : ℂ :=
  exp (2 * Real.pi * I * (x : ℂ) * (L.polarDualNorm u : ℂ))

/-- The level shift `m k` as an element `S y` of the polar sublattice. -/
theorem polarGramMatrix_mulVec_levelShift (c : ℤ) (k : Fin n → ℤ) :
    L.polarGramMatrix *ᵥ ((2 * c ^ 2 * L.polarGramMatrix.det.sign) • (L.polarGramMatrix.adjugate *ᵥ k)) =
      ((L.gaussColumnLevel c : ℕ) : ℤ) • k := by
  rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, Matrix.mul_adjugate, Matrix.smul_mulVec,
    Matrix.one_mulVec, smul_smul, gaussColumnLevel_cast]

/-- The phase is periodic modulo `m(c) ℤⁿ` at `x = -d/c`. -/
theorem polarDualPhase_add_level {c : ℤ} (hc : c ≠ 0) (d : ℤ) (u k : Fin n → ℤ) :
    L.polarDualPhase (-(d : ℚ) / c) (u + ((L.gaussColumnLevel c : ℕ) : ℤ) • k) =
      L.polarDualPhase (-(d : ℚ) / c) u := by
  set s : ℤ := 2 * c ^ 2 * L.polarGramMatrix.det.sign with hs
  set v : Fin n → ℤ := L.polarGramMatrix.adjugate *ᵥ k with hv
  rw [← L.polarGramMatrix_mulVec_levelShift c k]
  unfold polarDualPhase
  rw [L.polarDualNorm_add_gram, dotProduct_smul, L.quadForm_smul, smul_eq_mul]
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc
  have hint : ((-(d : ℚ) / c : ℚ) : ℂ) * ((((s * (u ⬝ᵥ v) + s ^ 2 * L.quadForm v : ℤ) : ℝ)) : ℂ) =
      ((-(2 * d * c * L.polarGramMatrix.det.sign) * (u ⬝ᵥ v + s * L.quadForm v) : ℤ) : ℂ) := by
    rw [hs]
    push_cast
    field_simp
  rw [show 2 * (Real.pi : ℂ) * I * ((-(d : ℚ) / c : ℚ) : ℂ) *
      (((L.polarDualNorm u + ((s * (u ⬝ᵥ v) + s ^ 2 * L.quadForm v : ℤ) : ℝ)) : ℝ) : ℂ) =
      2 * Real.pi * I * ((-(d : ℚ) / c : ℚ) : ℂ) * (L.polarDualNorm u : ℂ) +
        2 * Real.pi * I * (((-(d : ℚ) / c : ℚ) : ℂ) *
          ((((s * (u ⬝ᵥ v) + s ^ 2 * L.quadForm v : ℤ) : ℝ)) : ℂ)) by push_cast; ring,
    Complex.exp_add, hint, exp_two_pi_I_intCast, mul_one]

/-! ## The column weight -/

/-- The integer lift of a residue vector. -/
def residueLift {m : ℕ} (r : Fin n → ZMod m) : Fin n → ℤ := fun i ↦ ((r i).val : ℤ)

theorem residueLift_intCast {m : ℕ} [NeZero m] (z : Fin n → ℤ) :
    residueLift (fun i ↦ (z i : ZMod m)) = z + (m : ℤ) • (fun i ↦ -(z i / m)) := by
  funext i
  simp only [residueLift, ZMod.val_intCast, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [Int.emod_def]
  ring

theorem coe_add_levelShift {c : ℤ} (u k : Fin n → ℤ) :
    ((u + ((L.gaussColumnLevel c : ℕ) : ℤ) • k : Fin n → ℤ) : L.PolarDiscriminantGroup) =
      (u : L.PolarDiscriminantGroup) := by
  rw [QuotientAddGroup.mk_add, add_eq_left, QuotientAddGroup.eq_zero_iff]
  exact (L.mem_polarGramRange_iff _).2 ⟨_, L.polarGramMatrix_mulVec_levelShift c k⟩

/-- The column weight `w_{c,d,a}(r) = [r ∈ a] e(-(d/c) q(S⁻¹r))` on residues modulo `m(c)`. -/
def gaussColumnWeight (c d : ℤ) (a : L.PolarDiscriminantGroup)
    (r : Fin n → ZMod (L.gaussColumnLevel c)) : ℂ :=
  if ((residueLift r : Fin n → ℤ) : L.PolarDiscriminantGroup) = a then
    L.polarDualPhase (-(d : ℚ) / c) (residueLift r) else 0

/-- The weight is periodic: at the reduction of an integer vector it is the class-restricted phase. -/
theorem gaussColumnWeight_intCast {c : ℤ} (hc : c ≠ 0) (d : ℤ) (a : L.PolarDiscriminantGroup)
    (z : Fin n → ℤ) :
    haveI : NeZero (L.gaussColumnLevel c) := ⟨L.gaussColumnLevel_ne_zero hc⟩
    L.gaussColumnWeight c d a (fun i ↦ (z i : ZMod (L.gaussColumnLevel c))) =
      if (z : L.PolarDiscriminantGroup) = a then L.polarDualPhase (-(d : ℚ) / c) z else 0 := by
  haveI : NeZero (L.gaussColumnLevel c) := ⟨L.gaussColumnLevel_ne_zero hc⟩
  unfold gaussColumnWeight
  rw [residueLift_intCast, L.coe_add_levelShift, L.polarDualPhase_add_level hc]

/-! ## The boundary limit -/

/-- The Gaussian summand at `S⁻¹` times the phase is the class-theta summand at `τ = -d/c - ε + iσ`. -/
theorem polarDualPhase_mul_shiftedMatrixGaussianSummand (x : ℚ) (σ ε : ℝ) (u : Fin n → ℤ) :
    L.polarDualPhase x u *
        shiftedMatrixGaussianSummand L.rationalQuadraticSpaceMatrix.realPolarMatrix⁻¹
          ((σ : ℂ) + (ε : ℂ) * I) 0 u =
      exp (2 * Real.pi * I * ((x : ℂ) - ε + σ * I) * (L.polarDualNorm u : ℂ)) := by
  unfold polarDualPhase shiftedMatrixGaussianSummand polarDualNorm
  rw [← Complex.exp_add]
  congr 1
  simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero, mul_zero, add_zero]
  push_cast
  ring_nf
  rw [I_sq]
  ring

/-- The rational boundary limit (2.7): `√(σⁿ det S⁻¹) θ_a(-d/c - ε + iσ) → m⁻ⁿ Σ_r w_{c,d,a}(r)`. -/
theorem tendsto_polarClassTheta_boundary {c : ℤ} (hc : c ≠ 0) (d : ℤ) (a : L.PolarDiscriminantGroup)
    {κ : Type*} {l : Filter κ} (σ ε : κ → ℝ) (hσ : Tendsto σ l (𝓝[>] 0))
    (hε : Tendsto (fun x ↦ ε x / σ x) l (𝓝 0)) :
    haveI : NeZero (L.gaussColumnLevel c) := ⟨L.gaussColumnLevel_ne_zero hc⟩
    Tendsto (fun x ↦ (Real.sqrt ((σ x) ^ n * (L.rationalQuadraticSpaceMatrix.realPolarMatrix⁻¹).det) : ℂ) *
        L.polarClassTheta (((-(d : ℚ) / c : ℚ) : ℂ) - ε x + σ x * I) a) l
      (𝓝 ((((L.gaussColumnLevel c : ℝ) ^ n : ℂ)⁻¹) * ∑ r, L.gaussColumnWeight c d a r)) := by
  haveI : NeZero (L.gaussColumnLevel c) := ⟨L.gaussColumnLevel_ne_zero hc⟩
  classical
  have h := tendsto_periodicShiftedMatrixGaussian_along
    (L.rationalQuadraticSpaceMatrix.realPolarMatrix⁻¹)
    L.rationalQuadraticSpaceMatrix_realPolarMatrix_posDef.inv
    (L.gaussColumnWeight c d a) σ ε hσ hε
  refine h.congr fun x ↦ ?_
  congr 1
  unfold polarClassTheta
  simp_rw [L.gaussColumnWeight_intCast hc]
  rw [← tsum_subtype_eq_of_support_subset (s := {u : Fin n → ℤ | (u : L.PolarDiscriminantGroup) = a})]
  · refine tsum_congr fun u ↦ ?_
    have hu : ((u : Fin n → ℤ) : L.PolarDiscriminantGroup) = a := u.2
    rw [if_pos hu, L.polarDualPhase_mul_shiftedMatrixGaussianSummand]
  · intro u hu
    by_contra hna
    simp only [Set.mem_setOf_eq] at hna
    exact hu (by simp [hna])

end PositiveDefiniteIntegralLattice
