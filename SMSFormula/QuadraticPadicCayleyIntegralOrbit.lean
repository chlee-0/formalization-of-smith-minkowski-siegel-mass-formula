import SMSFormula.QuadraticPadicCayleyOrbitAction
import SMSFormula.QuadraticPadicIntegralOrbitTransitivity
import SMSFormula.LocalOrthogonalHaar

/-! The integral orbit of `x_old` at a good place. For a symmetric Gram matrix `F`
over `ℚ_p` with integral entries, the polar form of `F.toQuadraticMap'` is
integral on the standard lattice, and it is unimodular when `‖det F‖ = 1` and
`p` is odd (through the integral adjugate). A determinant-one linear isometry is
an element of the special form-preserving group acting by matrix
multiplication. The lattice-preserving subgroup `K_int` (matrices mapping the
standard lattice into itself together with their inverses) therefore acts
transitively on the integral points of every unit value: at a good place
(`p` odd, Gram matrix of `W ⊕ ⟨a⟩` integral with unit determinant, `a` a
unit, rank at least two) `K_int · x_old = X_a(ℤ_p)`. The good-place conditions
are supplied hypotheses on the matrix; no representative, chart or
normalization is chosen. -/
noncomputable section
open MeasureTheory Matrix PositiveDefiniteIntegralLattice Set QuadraticMap
open scoped ENNReal

namespace QuadraticMap

variable {p : ℕ} [Fact p.Prime] {N : ℕ}

theorem padic_norm_sum_le_one {ι : Type*} (s : Finset ι) (f : ι → ℚ_[p])
    (h : ∀ i ∈ s, ‖f i‖ ≤ 1) : ‖∑ i ∈ s, f i‖ ≤ 1 :=
  Finset.sum_induction f (fun z ↦ ‖z‖ ≤ 1) (fun _ _ ha hb ↦ padic_norm_add_le_one ha hb)
    (by simp) h

theorem padic_norm_sum_lt_one {ι : Type*} (s : Finset ι) (f : ι → ℚ_[p])
    (h : ∀ i ∈ s, ‖f i‖ < 1) : ‖∑ i ∈ s, f i‖ < 1 :=
  Finset.sum_induction f (fun z ↦ ‖z‖ < 1) (fun _ _ ha hb ↦ padic_norm_add_lt_one ha hb)
    (by simp) h

theorem padic_norm_dotProduct_mulVec_le_one {F : Matrix (Fin N) (Fin N) ℚ_[p]}
    (hint : ∀ i j, ‖F i j‖ ≤ 1) {x y : Fin N → ℚ_[p]} (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) :
    ‖x ⬝ᵥ F *ᵥ y‖ ≤ 1 := by
  rw [padicVector_norm_le_one_iff] at hx hy
  simp only [dotProduct, Matrix.mulVec]
  refine padic_norm_sum_le_one _ _ fun i _ ↦ ?_
  rw [norm_mul]
  refine mul_le_one₀ (hx i) (norm_nonneg _) (padic_norm_sum_le_one _ _ fun j _ ↦ ?_)
  rw [norm_mul]
  exact mul_le_one₀ (hint i j) (norm_nonneg _) (hy j)

theorem polar_toQuadraticMap'_apply (F : Matrix (Fin N) (Fin N) ℚ_[p]) (x y : Fin N → ℚ_[p]) :
    polar (F.toQuadraticMap') x y = x ⬝ᵥ F *ᵥ y + y ⬝ᵥ F *ᵥ x := by
  simp only [Matrix.toQuadraticMap', Matrix.toQuadraticForm', LinearMap.BilinMap.polar_toQuadraticMap,
    Matrix.toLinearMap₂'_apply']

/-- Integral Gram entries give an integral polar form. -/
theorem isPadicIntegralPolar_toQuadraticMap' {F : Matrix (Fin N) (Fin N) ℚ_[p]}
    (hint : ∀ i j, ‖F i j‖ ≤ 1) : IsPadicIntegralPolar (p := p) (F.toQuadraticMap') := by
  intro x y hx hy
  rw [polar_toQuadraticMap'_apply]
  exact padic_norm_add_le_one (padic_norm_dotProduct_mulVec_le_one hint hx hy)
    (padic_norm_dotProduct_mulVec_le_one hint hy hx)

theorem padicVector_norm_single_le_one (j : Fin N) :
    ‖(Pi.single j (1 : ℚ_[p]) : Fin N → ℚ_[p])‖ ≤ 1 := by
  rw [padicVector_norm_le_one_iff]
  intro i
  by_cases hi : i = j
  · subst hi; simp
  · simp [Pi.single_eq_of_ne hi]

/-- Integral symmetric Gram entries with unit determinant give a unimodular polar
form away from `2`. -/
theorem isPadicUnimodularPolar_toQuadraticMap' (hp : p ≠ 2) {F : Matrix (Fin N) (Fin N) ℚ_[p]}
    (hF : F.IsSymm) (hint : ∀ i j, ‖F i j‖ ≤ 1) (hdet : ‖F.det‖ = 1) :
    IsPadicUnimodularPolar (p := p) (F.toQuadraticMap') := by
  intro x hx hsmall
  have hFx : ∀ j, ‖(F *ᵥ x) j‖ < 1 := by
    intro j
    have h := hsmall (Pi.single j 1) (padicVector_norm_single_le_one j)
    have hsym : x ᵥ* F = F *ᵥ x := by
      rw [← Matrix.mulVec_transpose, hF.eq]
    rw [polar_toQuadraticMap'_apply, Matrix.dotProduct_mulVec, hsym, dotProduct_single,
      single_dotProduct, mul_one, one_mul, ← two_mul, norm_mul,
      padic_norm_two_of_ne_two hp, one_mul] at h
    exact h
  -- the adjugate of an integral matrix is integral
  let F' : Matrix (Fin N) (Fin N) ℤ_[p] := fun i j ↦ ⟨F i j, hint i j⟩
  have hFF' : F = (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p]).mapMatrix F' := by
    ext i j; rfl
  have hadj : ∀ i k, ‖F.adjugate i k‖ ≤ 1 := by
    intro i k
    rw [hFF', ← RingHom.map_adjugate]
    change ‖((F'.adjugate i k : ℤ_[p]) : ℚ_[p])‖ ≤ 1
    rw [PadicInt.padic_norm_e_of_padicInt]
    exact PadicInt.norm_le_one _
  have hkey : F.det • x = F.adjugate *ᵥ (F *ᵥ x) := by
    rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec]
  rw [pi_norm_lt_iff zero_lt_one]
  intro i
  have hi := congrFun hkey i
  rw [Pi.smul_apply, smul_eq_mul] at hi
  have hnorm : ‖F.det * x i‖ = ‖x i‖ := by rw [norm_mul, hdet, one_mul]
  rw [← hnorm, hi]
  simp only [Matrix.mulVec, dotProduct]
  refine padic_norm_sum_lt_one _ _ fun k _ ↦ ?_
  rw [norm_mul]
  calc ‖F.adjugate i k‖ * ‖(F *ᵥ x) k‖ ≤ 1 * ‖(F *ᵥ x) k‖ :=
        mul_le_mul_of_nonneg_right (hadj i k) (norm_nonneg _)
    _ < 1 := by rw [one_mul]; exact hFx k

/-- A determinant-one linear isometry of `F.toQuadraticMap'` is an element of the
special form-preserving group acting by matrix multiplication. -/
theorem exists_specialFormPreserving_mulVec_eq {F : Matrix (Fin N) (Fin N) ℚ_[p]} (hF : F.IsSymm)
    (g : (Fin N → ℚ_[p]) ≃ₗ[ℚ_[p]] (Fin N → ℚ_[p]))
    (hg : ∀ x, F.toQuadraticMap' (g x) = F.toQuadraticMap' x)
    (hdet : LinearMap.det (g : (Fin N → ℚ_[p]) →ₗ[ℚ_[p]] (Fin N → ℚ_[p])) = 1) :
    ∃ γ : specialFormPreservingMatrixSubgroup F,
      ∀ x, (γ.1.1.1 : Matrix (Fin N) (Fin N) ℚ_[p]) *ᵥ x = g x := by
  letI : Invertible (2 : ℚ_[p]) := invertibleOfNonzero two_ne_zero
  set M := LinearMap.toMatrix' (g : (Fin N → ℚ_[p]) →ₗ[ℚ_[p]] (Fin N → ℚ_[p])) with hM
  have hcomp : (F.toQuadraticMap').comp (g : (Fin N → ℚ_[p]) →ₗ[ℚ_[p]] (Fin N → ℚ_[p])) =
      F.toQuadraticMap' := QuadraticMap.ext fun x ↦ hg x
  have hform : Mᵀ * F * M = F := by
    have h := QuadraticForm.toMatrix'_comp (F.toQuadraticMap')
      (g : (Fin N → ℚ_[p]) →ₗ[ℚ_[p]] (Fin N → ℚ_[p]))
    rw [hcomp, Matrix.toMatrix'_toQuadraticMap'_of_isSymm _ hF] at h
    exact h.symm
  have hMdet : M.det = 1 := by rw [hM, LinearMap.det_toMatrix']; exact hdet
  refine ⟨specialOrthogonalMatrixSetToSpecialSubgroup F
    ⟨M, (Matrix.formPreservingConstraint_eq_zero_iff F M).mpr hform, hMdet⟩, fun x ↦ ?_⟩
  change M *ᵥ x = g x
  rw [hM, LinearMap.toMatrix'_mulVec]
  rfl

/-- The lattice-preserving subgroup of the special form-preserving group:
elements mapping the standard lattice into itself together with their inverses. -/
def padicLatticeSpecialSubgroup (F : Matrix (Fin N) (Fin N) ℚ_[p]) :
    Subgroup (specialFormPreservingMatrixSubgroup F) where
  carrier := {g | ∀ x : Fin N → ℚ_[p], ‖x‖ ≤ 1 →
    ‖(g.1.1.1 : Matrix (Fin N) (Fin N) ℚ_[p]) *ᵥ x‖ ≤ 1 ∧
      ‖((g⁻¹).1.1.1 : Matrix (Fin N) (Fin N) ℚ_[p]) *ᵥ x‖ ≤ 1}
  one_mem' := fun x hx ↦ by
    refine ⟨?_, ?_⟩ <;>
    · change ‖((1 : (Matrix (Fin N) (Fin N) ℚ_[p])ˣ) : Matrix (Fin N) (Fin N) ℚ_[p]) *ᵥ x‖ ≤ 1
      rw [Units.val_one, Matrix.one_mulVec]; exact hx
  mul_mem' := by
    intro g h hg hh x hx
    refine ⟨?_, ?_⟩
    · change ‖(g.1.1.1 * h.1.1.1) *ᵥ x‖ ≤ 1
      rw [← Matrix.mulVec_mulVec]
      exact (hg _ (hh x hx).1).1
    · rw [_root_.mul_inv_rev]
      change ‖((h⁻¹).1.1.1 * (g⁻¹).1.1.1) *ᵥ x‖ ≤ 1
      rw [← Matrix.mulVec_mulVec]
      exact (hh _ (hg x hx).2).2
  inv_mem' := by
    intro g hg x hx
    refine ⟨(hg x hx).2, ?_⟩
    rw [inv_inv]
    exact (hg x hx).1

/-- An element acting on the lattice through a lattice-preserving isometry lies
in the lattice-preserving subgroup. -/
theorem mem_padicLatticeSpecialSubgroup_of_mulVec_eq {F : Matrix (Fin N) (Fin N) ℚ_[p]}
    (γ : specialFormPreservingMatrixSubgroup F) (g : (Fin N → ℚ_[p]) ≃ₗ[ℚ_[p]] (Fin N → ℚ_[p]))
    (hγ : ∀ x, (γ.1.1.1 : Matrix (Fin N) (Fin N) ℚ_[p]) *ᵥ x = g x)
    (hgL : ∀ x, ‖x‖ ≤ 1 → ‖g x‖ ≤ 1) (hgL' : ∀ x, ‖x‖ ≤ 1 → ‖g.symm x‖ ≤ 1) :
    γ ∈ padicLatticeSpecialSubgroup F := by
  have hinv : ((γ.1.1.1 : Matrix (Fin N) (Fin N) ℚ_[p]) * ((γ⁻¹).1.1.1 : Matrix (Fin N) (Fin N) ℚ_[p])) = 1 := by
    change (γ * γ⁻¹).1.1.1 = 1
    rw [mul_inv_cancel]; rfl
  intro x hx
  refine ⟨by rw [hγ]; exact hgL x hx, ?_⟩
  have h : ((γ⁻¹).1.1.1 : Matrix (Fin N) (Fin N) ℚ_[p]) *ᵥ x = g.symm x := by
    rw [LinearEquiv.eq_symm_apply, ← hγ, Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
  rw [h]
  exact hgL' x hx

/-- A matrix has integral entries exactly when it maps the standard lattice into
itself. -/
theorem padic_matrix_entries_le_one_iff (M : Matrix (Fin N) (Fin N) ℚ_[p]) :
    (∀ i j, ‖M i j‖ ≤ 1) ↔ ∀ x : Fin N → ℚ_[p], ‖x‖ ≤ 1 → ‖M *ᵥ x‖ ≤ 1 := by
  constructor
  · intro h x hx
    rw [padicVector_norm_le_one_iff] at hx ⊢
    intro i
    simp only [Matrix.mulVec, dotProduct]
    exact padic_norm_sum_le_one _ _ fun j _ ↦ by
      rw [norm_mul]; exact mul_le_one₀ (h i j) (norm_nonneg _) (hx j)
  · intro h i j
    have := (norm_le_pi_norm (M *ᵥ Pi.single j 1) i).trans (h _ (padicVector_norm_single_le_one j))
    simpa [Matrix.mulVec_single] using this

/-- The integral subgroup of the special form-preserving group: the pullback
of the integral matrix units `localPadicIntegralMatrixUnitsSubgroup`. -/
def padicIntegralSpecialSubgroup (F : Matrix (Fin N) (Fin N) ℚ_[p]) :
    Subgroup (specialFormPreservingMatrixSubgroup F) :=
  (localPadicIntegralMatrixUnitsSubgroup p N).comap
    ((formPreservingMatrixSubgroup F).subtype.comp (specialFormPreservingMatrixSubgroup F).subtype)

/-- The integral subgroup is the lattice-preserving subgroup. -/
theorem padicIntegralSpecialSubgroup_eq_padicLatticeSpecialSubgroup
    (F : Matrix (Fin N) (Fin N) ℚ_[p]) :
    padicIntegralSpecialSubgroup F = padicLatticeSpecialSubgroup F := by
  ext g
  change (∀ i j, g.1.1.1 i j ∈ PadicInt.subring p) ∧ (∀ i j, (g.1.1⁻¹).1 i j ∈ PadicInt.subring p) ↔
    ∀ x : Fin N → ℚ_[p], ‖x‖ ≤ 1 → ‖(g.1.1.1 : Matrix (Fin N) (Fin N) ℚ_[p]) *ᵥ x‖ ≤ 1 ∧
      ‖((g⁻¹).1.1.1 : Matrix (Fin N) (Fin N) ℚ_[p]) *ᵥ x‖ ≤ 1
  simp only [PadicInt.mem_subring_iff]
  rw [padic_matrix_entries_le_one_iff, padic_matrix_entries_le_one_iff]
  exact ⟨fun h x hx ↦ ⟨h.1 x hx, h.2 x hx⟩, fun h ↦ ⟨fun x hx ↦ (h x hx).1, fun x hx ↦ (h x hx).2⟩⟩

theorem isOpen_padicIntegralSpecialSubgroup (F : Matrix (Fin N) (Fin N) ℚ_[p]) :
    IsOpen (padicIntegralSpecialSubgroup F : Set (specialFormPreservingMatrixSubgroup F)) :=
  (isOpen_localPadicIntegralMatrixUnitsSubgroup p N).preimage
    (continuous_subtype_val.comp continuous_subtype_val)

theorem isCompact_padicIntegralSpecialSubgroup (F : Matrix (Fin N) (Fin N) ℚ_[p]) :
    IsCompact (padicIntegralSpecialSubgroup F : Set (specialFormPreservingMatrixSubgroup F)) := by
  letI : T2Space (Matrix (Fin N) (Fin N) ℚ_[p]) :=
    inferInstanceAs (T2Space (Fin N → Fin N → ℚ_[p]))
  have hclosed₁ : IsClosed (formPreservingMatrixSubgroup F : Set (Matrix (Fin N) (Fin N) ℚ_[p])ˣ) :=
    isClosed_eq ((Units.continuous_val.matrix_transpose.matrix_mul continuous_const).matrix_mul
      Units.continuous_val) continuous_const
  have hclosed₂ : IsClosed (specialFormPreservingMatrixSubgroup F :
      Set (formPreservingMatrixSubgroup F)) := by
    have hset : (specialFormPreservingMatrixSubgroup F : Set (formPreservingMatrixSubgroup F)) =
        {g | g.1.1.det = 1} := by
      ext g; exact mem_specialFormPreservingMatrixSubgroup_iff F g
    rw [hset]
    exact isClosed_eq ((Units.continuous_val.comp continuous_subtype_val).matrix_det)
      continuous_const
  exact (hclosed₁.isClosedEmbedding_subtypeVal.comp hclosed₂.isClosedEmbedding_subtypeVal).isCompact_preimage
    (isCompact_localPadicIntegralMatrixUnitsSubgroup p N)

end QuadraticMap

namespace RationalQuadraticSpaceMatrix
variable {n : ℕ} (W : RationalQuadraticSpaceMatrix n) (p : ℕ) [Fact (Nat.Prime p)]
variable (a : ℚ) (ha : a ≠ 0)

/-- Good-place integral orbit: at an odd prime where the Gram matrix of
`W ⊕ ⟨a⟩` is integral with unit determinant and `a` is a unit, the orbit of
`x_old` under the lattice-preserving subgroup is the set of integral points of
`{Q = a}`. -/
theorem range_smul_lastFiberBasePoint_padicLattice (hp : p ≠ 2) (hn : 1 ≤ n)
    (hint : ∀ i j, ‖((W.nonisotropicLastExtension a ha).pairingMatrix.map (algebraMap ℚ ℚ_[p])) i j‖ ≤ 1)
    (hdet : ‖((W.nonisotropicLastExtension a ha).pairingMatrix.map (algebraMap ℚ ℚ_[p])).det‖ = 1)
    (ha1 : ‖(algebraMap ℚ ℚ_[p] a)‖ = 1) :
    range (fun γ : padicLatticeSpecialSubgroup
        ((W.nonisotropicLastExtension a ha).pairingMatrix.map (algebraMap ℚ ℚ_[p])) ↦
        γ • W.lastFiberBasePoint p a ha) =
      {y | ‖y.1‖ ≤ 1} := by
  set F := (W.nonisotropicLastExtension a ha).pairingMatrix.map (algebraMap ℚ ℚ_[p]) with hFdef
  have hF : F.IsSymm := (W.nonisotropicLastExtension a ha).commutativeScalarExtensionFormMatrix_isSymm ℚ_[p]
  have hlast : ‖(lastCoordinateVector : Fin (n+1) → ℚ_[p])‖ ≤ 1 :=
    padicVector_norm_single_le_one (Fin.last n)
  ext y
  simp only [mem_range, mem_setOf_eq]
  constructor
  · rintro ⟨γ, rfl⟩
    exact (γ.2 _ hlast).1
  · intro hy
    have hQ : (W.nonisotropicLastExtension a ha).commutativeScalarExtensionQuadraticForm ℚ_[p] =
        F.toQuadraticMap' := rfl
    have hv : F.toQuadraticMap' (lastCoordinateVector : Fin (n+1) → ℚ_[p]) = F.toQuadraticMap' y.1 := by
      rw [← hQ, y.2]; exact W.nonisotropicLastExtension_quadratic_last a ha
    have hQy : ‖(F.toQuadraticMap' y.1 : ℚ_[p])‖ = 1 := by
      rw [← hQ, y.2]; exact ha1
    obtain ⟨g, hgQ, hgdet, hgL, hgL', hgv⟩ := exists_padicIntegral_isometry_det_one_apply_eq
      (F.toQuadraticMap') hp (by omega) (isPadicIntegralPolar_toQuadraticMap' hint)
      (isPadicUnimodularPolar_toQuadraticMap' hp hF hint hdet) hlast hy hv hQy
    obtain ⟨γ, hγ⟩ := exists_specialFormPreserving_mulVec_eq hF g hgQ hgdet
    refine ⟨⟨γ, mem_padicLatticeSpecialSubgroup_of_mulVec_eq γ g hγ hgL hgL'⟩, Subtype.ext ?_⟩
    change (γ.1.1.1 : Matrix (Fin (n+1)) (Fin (n+1)) ℚ_[p]) *ᵥ lastCoordinateVector = y.1
    rw [hγ, hgv]

/-- Good-place integral orbit for the integral subgroup. -/
theorem range_smul_lastFiberBasePoint_padicIntegral (hp : p ≠ 2) (hn : 1 ≤ n)
    (hint : ∀ i j, ‖((W.nonisotropicLastExtension a ha).pairingMatrix.map (algebraMap ℚ ℚ_[p])) i j‖ ≤ 1)
    (hdet : ‖((W.nonisotropicLastExtension a ha).pairingMatrix.map (algebraMap ℚ ℚ_[p])).det‖ = 1)
    (ha1 : ‖(algebraMap ℚ ℚ_[p] a)‖ = 1) :
    range (fun γ : padicIntegralSpecialSubgroup
        ((W.nonisotropicLastExtension a ha).pairingMatrix.map (algebraMap ℚ ℚ_[p])) ↦
        γ • W.lastFiberBasePoint p a ha) =
      {y | ‖y.1‖ ≤ 1} := by
  rw [padicIntegralSpecialSubgroup_eq_padicLatticeSpecialSubgroup]
  exact W.range_smul_lastFiberBasePoint_padicLattice p a ha hp hn hint hdet ha1

end RationalQuadraticSpaceMatrix
