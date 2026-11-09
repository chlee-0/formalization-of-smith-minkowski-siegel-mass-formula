import SMSFormula.RationalCliffordSpinCandidateFiniteAdelicAdmissiblePrincipalBlock

/-!
# Fixed-block topology for finite-adelic Clifford--Spin candidate points

For a finite exceptional set `S`, this file compares the genuine open
finite-adelic admissible block with the explicit mixed product of its local
factors.  Forward local evaluation is continuous.  Reverse assembly is proved
continuous coordinate by coordinate through the principal restricted product
whose filter is the complement of the normalized exceptional set.

The topology on candidate points is induced by the finite Clifford and matrix
coordinate family.  Consequently only those assembled coordinates are needed
for reverse continuity; inverse-coordinate integrality remains part of the
local subgroup definition and is used for algebraic closure.
-/

noncomputable section

open PositiveDefiniteIntegralLattice
open scoped Matrix RestrictedProduct

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1200000

local instance finiteAdelicSpinAdmissibleTopologyPrimeFact
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

local instance finiteAdelicSpinAdmissibleTopologyDecidableEq :
    DecidableEq (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  Classical.decEq _

/-! ## The mixed and restricted-family block topologies -/

/-- The already constructed mixed-to-restricted-block map is continuous for
the displayed product and inherited subtype topologies. -/
theorem
    continuous_finiteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlockToBlockHom
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Continuous
      (V.finiteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlockToBlockHom
        S) := by
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  exact
    V.continuous_finiteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlockFamilyHom
      S

/-- Reading a normalized restricted family componentwise as a mixed local
family is continuous. -/
theorem
    continuous_finiteAdelicCliffordSpinCandidateAdmissiblePrincipalBlockToMixedHom
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Continuous
      (V.finiteAdelicCliffordSpinCandidateAdmissiblePrincipalBlockToMixedHom
        S) := by
  apply continuous_pi
  intro v
  apply Continuous.subtype_mk
  exact (continuous_apply v).comp
    (continuous_subtype_val.comp continuous_subtype_val)

/-- The explicit mixed product and the normalized restricted-family block are
continuously multiplicatively equivalent. -/
noncomputable def
    finiteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlockContinuousMulEquiv
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    V.FiniteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlock S ≃ₜ*
      V.FiniteAdelicCliffordSpinCandidateAdmissiblePrincipalBlock S :=
  ContinuousMulEquiv.mk
    (V.finiteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlockMulEquiv S)
    (V.continuous_finiteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlockToBlockHom
      S)
    (V.continuous_finiteAdelicCliffordSpinCandidateAdmissiblePrincipalBlockToMixedHom
      S)

/-! ## Genuine block and forward evaluation -/

/-- The genuine open finite-adelic normalized principal-block carrier. -/
abbrev FiniteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlock
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :=
  V.finiteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlockSubgroup S

/-- Componentwise evaluation from the genuine block to the mixed local
product. -/
def finiteAdelicCliffordSpinCandidateGenuineAdmissibleBlockToMixedHom
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    V.FiniteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlock S →*
      V.FiniteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlock S where
  toFun a v :=
    ⟨V.finiteAdelicCliffordSpinCandidateHeightOneComponentHom v a.1, by
      intro hv
      have ha :
          V.IsFiniteAdelicCliffordSpinCandidateIntegralOutside
            (V.cliffordSpinCandidateAdmissibleExceptionalPlaces S) a.1 :=
        (V.mem_finiteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlockSubgroup_iff
          S a.1).1 a.2
      exact
        (V.finiteAdelicCliffordSpinCandidateHeightOneComponent_isIntegral_iff
          a.1 v).2
          ((V.isFiniteAdelicCliffordSpinCandidateIntegralOutside_iff
            (V.cliffordSpinCandidateAdmissibleExceptionalPlaces S) a.1).1
              ha v hv)⟩
  map_one' := by
    funext v
    apply Subtype.ext
    exact (V.finiteAdelicCliffordSpinCandidateHeightOneComponentHom v).map_one
  map_mul' := by
    intro a b
    funext v
    apply Subtype.ext
    exact (V.finiteAdelicCliffordSpinCandidateHeightOneComponentHom v).map_mul
      a.1 b.1

@[simp]
theorem
    finiteAdelicCliffordSpinCandidateGenuineAdmissibleBlockToMixedHom_apply_component
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (a : V.FiniteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlock S)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    (V.finiteAdelicCliffordSpinCandidateGenuineAdmissibleBlockToMixedHom S a v).1 =
      V.finiteAdelicCliffordSpinCandidateHeightOneComponentHom v a.1 :=
  rfl

/-- Forward evaluation on a genuine normalized block is continuous. -/
theorem
    continuous_finiteAdelicCliffordSpinCandidateGenuineAdmissibleBlockToMixedHom
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Continuous
      (V.finiteAdelicCliffordSpinCandidateGenuineAdmissibleBlockToMixedHom S) := by
  apply continuous_pi
  intro v
  apply Continuous.subtype_mk
  exact
    (V.continuous_finiteAdelicCliffordSpinCandidateHeightOneComponent v).comp
      continuous_subtype_val

/-! ## Reverse assembly and algebraic equivalence -/

/-- Assemble a mixed normalized block into the genuine finite-adelic block. -/
def finiteAdelicCliffordSpinCandidateAdmissibleMixedToGenuineBlockHom
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    V.FiniteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlock S →*
      V.FiniteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlock S where
  toFun g := by
    let p :=
      V.finiteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlockToBlockHom
        S g
    let e := V.finiteAdelicCliffordSpinCandidateRestrictedFamilyMulEquiv
    refine ⟨e.symm p.1, ?_⟩
    change e (e.symm p.1) ∈
      V.finiteAdelicCliffordSpinCandidateAdmissiblePrincipalBlockSubgroup S
    rw [e.apply_symm_apply]
    exact p.2
  map_one' := by
    apply Subtype.ext
    let p :=
      V.finiteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlockToBlockHom S
    let e := V.finiteAdelicCliffordSpinCandidateRestrictedFamilyMulEquiv
    change e.symm (p 1).1 = 1
    rw [p.map_one, Subgroup.coe_one, e.symm.map_one]
  map_mul' := by
    intro g h
    apply Subtype.ext
    let p :=
      V.finiteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlockToBlockHom S
    let e := V.finiteAdelicCliffordSpinCandidateRestrictedFamilyMulEquiv
    change e.symm (p (g * h)).1 = e.symm (p g).1 * e.symm (p h).1
    rw [p.map_mul, Subgroup.coe_mul, e.symm.map_mul]

@[simp]
theorem finiteAdelicCliffordSpinCandidateAdmissibleMixedToGenuineBlockHom_apply
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (g : V.FiniteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlock S) :
    (V.finiteAdelicCliffordSpinCandidateAdmissibleMixedToGenuineBlockHom S g).1 =
      V.finiteAdelicCliffordSpinCandidateRestrictedFamilyAssembly
        (V.finiteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlockToBlockHom
          S g).1 :=
  rfl

/-- Genuine finite-adelic evaluation and mixed-block assembly are inverse
multiplicative maps. -/
def finiteAdelicCliffordSpinCandidateGenuineAdmissibleBlockMulEquiv
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    V.FiniteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlock S ≃*
      V.FiniteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlock S where
  toFun :=
    V.finiteAdelicCliffordSpinCandidateGenuineAdmissibleBlockToMixedHom S
  invFun :=
    V.finiteAdelicCliffordSpinCandidateAdmissibleMixedToGenuineBlockHom S
  left_inv := by
    intro a
    apply Subtype.ext
    apply V.finiteAdelicCliffordSpinCandidateHeightOneComponentsHom_injective
    funext v
    exact congr_fun
      (V.finiteAdelicCliffordSpinCandidateHeightOneComponents_assembly
        (V.finiteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlockToBlockHom
          S
          (V.finiteAdelicCliffordSpinCandidateGenuineAdmissibleBlockToMixedHom
            S a)).1)
      v
  right_inv := by
    intro g
    funext v
    apply Subtype.ext
    exact congr_fun
      (V.finiteAdelicCliffordSpinCandidateHeightOneComponents_assembly
        (V.finiteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlockToBlockHom
          S g).1)
      v
  map_mul' :=
    (V.finiteAdelicCliffordSpinCandidateGenuineAdmissibleBlockToMixedHom S).map_mul

/-! ## Fixed principal restricted products -/

private abbrev RationalFiniteAdeleSpinAdmissiblePrincipalBlock
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :=
  Πʳ v : IsDedekindDomain.HeightOneSpectrum ℤ,
    [v.adicCompletion ℚ, v.adicCompletionIntegers ℚ]_[
      Filter.principal
        {v : IsDedekindDomain.HeightOneSpectrum ℤ |
          v ∉ V.cliffordSpinCandidateAdmissibleExceptionalPlaces S}]

private theorem cofinite_le_spinAdmissiblePrincipal_compl
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Filter.cofinite ≤ Filter.principal
      {v : IsDedekindDomain.HeightOneSpectrum ℤ |
        v ∉ V.cliffordSpinCandidateAdmissibleExceptionalPlaces S} := by
  rw [Filter.le_principal_iff]
  exact
    (V.cliffordSpinCandidateAdmissibleExceptionalPlaces S).eventually_cofinite_notMem

/-- One Clifford coordinate of a mixed block, assembled first in the fixed
principal restricted product. -/
private noncomputable def admissibleMixedPrincipalBlockCliffordCoordinate
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (g : V.FiniteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlock S)
    (s : Finset (Fin n)) :
    V.RationalFiniteAdeleSpinAdmissiblePrincipalBlock S :=
  ⟨fun v =>
      (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).symm
        ((g v).1 (V.cliffordSpinCandidateCliffordCoordinate s)),
    by
      change ∀ᶠ v in Filter.principal
          {v : IsDedekindDomain.HeightOneSpectrum ℤ |
            v ∉ V.cliffordSpinCandidateAdmissibleExceptionalPlaces S},
        (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).symm
            ((g v).1 (V.cliffordSpinCandidateCliffordCoordinate s)) ∈
          v.adicCompletionIntegers ℚ
      rw [Filter.eventually_principal]
      intro v hv
      exact ((g v).2 (by simpa using hv)).1 s⟩

/-- One matrix coordinate of a mixed block, assembled first in the fixed
principal restricted product. -/
private noncomputable def admissibleMixedPrincipalBlockMatrixCoordinate
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (g : V.FiniteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlock S)
    (i j : Fin n) :
    V.RationalFiniteAdeleSpinAdmissiblePrincipalBlock S :=
  ⟨fun v =>
      (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).symm
        ((g v).1 (V.cliffordSpinCandidateMatrixCoordinate i j)),
    by
      change ∀ᶠ v in Filter.principal
          {v : IsDedekindDomain.HeightOneSpectrum ℤ |
            v ∉ V.cliffordSpinCandidateAdmissibleExceptionalPlaces S},
        (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).symm
            ((g v).1 (V.cliffordSpinCandidateMatrixCoordinate i j)) ∈
          v.adicCompletionIntegers ℚ
      rw [Filter.eventually_principal]
      intro v hv
      exact ((g v).2 (by simpa using hv)).2.1 i j⟩

private theorem continuous_admissibleMixedPrincipalBlockCliffordCoordinate
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (s : Finset (Fin n)) :
    Continuous (fun g =>
      V.admissibleMixedPrincipalBlockCliffordCoordinate S g s) := by
  apply RestrictedProduct.continuous_rng_of_principal.mpr
  apply continuous_pi
  intro v
  change Continuous (fun
    g : V.FiniteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlock S =>
      (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).symm
        ((g v).1 (V.cliffordSpinCandidateCliffordCoordinate s)))
  exact
    (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).symm.continuous.comp
      ((V.continuous_cliffordSpinCandidateCliffordCoordinate
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1] s).comp
          (continuous_subtype_val.comp (continuous_apply v)))

private theorem continuous_admissibleMixedPrincipalBlockMatrixCoordinate
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (i j : Fin n) :
    Continuous (fun g =>
      V.admissibleMixedPrincipalBlockMatrixCoordinate S g i j) := by
  apply RestrictedProduct.continuous_rng_of_principal.mpr
  apply continuous_pi
  intro v
  change Continuous (fun
    g : V.FiniteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlock S =>
      (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).symm
        ((g v).1 (V.cliffordSpinCandidateMatrixCoordinate i j)))
  exact
    (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).symm.continuous.comp
      ((V.continuous_cliffordSpinCandidateMatrixCoordinate
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1] i j).comp
          (continuous_subtype_val.comp (continuous_apply v)))

private theorem
    continuous_restrictedFamilyCliffordCoordinate_admissibleMixedBlock
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (s : Finset (Fin n)) :
    Continuous (fun
      g : V.FiniteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlock S =>
        V.finiteAdelicCliffordSpinCandidateRestrictedFamilyCliffordCoordinate
          (V.finiteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlockToBlockHom
            S g).1 s) := by
  let R := fun v : IsDedekindDomain.HeightOneSpectrum ℤ =>
    v.adicCompletion ℚ
  let A : (v : IsDedekindDomain.HeightOneSpectrum ℤ) → Set (R v) :=
    fun v => v.adicCompletionIntegers ℚ
  let hS := V.cofinite_le_spinAdmissiblePrincipal_compl S
  let inclusion :
      V.RationalFiniteAdeleSpinAdmissiblePrincipalBlock S → RationalFiniteAdele :=
    RestrictedProduct.inclusion R A hS
  have hinclusion : Continuous inclusion :=
    RestrictedProduct.continuous_inclusion hS
  have hcoordinate :
      Continuous (fun g =>
        inclusion (V.admissibleMixedPrincipalBlockCliffordCoordinate S g s)) :=
    hinclusion.comp
      (V.continuous_admissibleMixedPrincipalBlockCliffordCoordinate S s)
  apply hcoordinate.congr
  intro g
  ext v
  rfl

private theorem
    continuous_restrictedFamilyMatrixCoordinate_admissibleMixedBlock
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (i j : Fin n) :
    Continuous (fun
      g : V.FiniteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlock S =>
        V.finiteAdelicCliffordSpinCandidateRestrictedFamilyMatrixCoordinate
          (V.finiteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlockToBlockHom
            S g).1 i j) := by
  let R := fun v : IsDedekindDomain.HeightOneSpectrum ℤ =>
    v.adicCompletion ℚ
  let A : (v : IsDedekindDomain.HeightOneSpectrum ℤ) → Set (R v) :=
    fun v => v.adicCompletionIntegers ℚ
  let hS := V.cofinite_le_spinAdmissiblePrincipal_compl S
  let inclusion :
      V.RationalFiniteAdeleSpinAdmissiblePrincipalBlock S → RationalFiniteAdele :=
    RestrictedProduct.inclusion R A hS
  have hinclusion : Continuous inclusion :=
    RestrictedProduct.continuous_inclusion hS
  have hcoordinate :
      Continuous (fun g =>
        inclusion (V.admissibleMixedPrincipalBlockMatrixCoordinate S g i j)) :=
    hinclusion.comp
      (V.continuous_admissibleMixedPrincipalBlockMatrixCoordinate S i j)
  apply hcoordinate.congr
  intro g
  ext v
  rfl

/-! ## Reverse continuity and the continuous multiplicative equivalence -/

/-- Reverse coordinate assembly is continuous on every fixed normalized
principal block. -/
theorem
    continuous_finiteAdelicCliffordSpinCandidateAdmissibleMixedToGenuineBlockHom
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Continuous
      (V.finiteAdelicCliffordSpinCandidateAdmissibleMixedToGenuineBlockHom S) := by
  apply Continuous.subtype_mk
  apply continuous_induced_rng.mpr
  apply Continuous.prodMk
  · apply continuous_pi
    intro s
    have h :=
      V.continuous_restrictedFamilyCliffordCoordinate_admissibleMixedBlock S s
    apply h.congr
    intro g
    dsimp only
    rw [V.finiteAdelicCliffordSpinCandidateRestrictedFamilyMulEquiv_symm_apply,
      V.finiteAdelicCliffordSpinCandidateRestrictedFamilyAssembly_cliffordCoordinate]
    ext v
    rfl
  · apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    have h :=
      V.continuous_restrictedFamilyMatrixCoordinate_admissibleMixedBlock S i j
    apply h.congr
    intro g
    dsimp only
    rw [V.finiteAdelicCliffordSpinCandidateRestrictedFamilyMulEquiv_symm_apply,
      V.finiteAdelicCliffordSpinCandidateRestrictedFamilyAssembly_matrixCoordinate]
    ext v
    rfl

/-- The genuine normalized block and explicit mixed product are homeomorphic
through evaluation and fixed-block assembly. -/
noncomputable def
    finiteAdelicCliffordSpinCandidateGenuineAdmissibleBlockHomeomorph
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    V.FiniteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlock S ≃ₜ
      V.FiniteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlock S where
  toEquiv :=
    V.finiteAdelicCliffordSpinCandidateGenuineAdmissibleBlockMulEquiv S
  continuous_toFun :=
    V.continuous_finiteAdelicCliffordSpinCandidateGenuineAdmissibleBlockToMixedHom S
  continuous_invFun :=
    V.continuous_finiteAdelicCliffordSpinCandidateAdmissibleMixedToGenuineBlockHom S

/-- The fixed normalized block comparison is continuously multiplicative. -/
noncomputable def
    finiteAdelicCliffordSpinCandidateGenuineAdmissibleBlockContinuousMulEquiv
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    V.FiniteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlock S ≃ₜ*
      V.FiniteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlock S :=
  ContinuousMulEquiv.mk'
    (V.finiteAdelicCliffordSpinCandidateGenuineAdmissibleBlockHomeomorph S)
    (V.finiteAdelicCliffordSpinCandidateGenuineAdmissibleBlockMulEquiv S).map_mul

/-- On every fixed normalized block, finite-adelic evaluation is a continuous
multiplicative equivalence with the corresponding restricted-family block. -/
noncomputable def
    finiteAdelicCliffordSpinCandidateGenuineAdmissibleBlockToRestrictedContinuousMulEquiv
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    V.FiniteAdelicCliffordSpinCandidateGenuineAdmissiblePrincipalBlock S ≃ₜ*
      V.FiniteAdelicCliffordSpinCandidateAdmissiblePrincipalBlock S :=
  (V.finiteAdelicCliffordSpinCandidateGenuineAdmissibleBlockContinuousMulEquiv S).trans
    (V.finiteAdelicCliffordSpinCandidateAdmissibleMixedPrincipalBlockContinuousMulEquiv S)

end RationalQuadraticSpaceMatrix
