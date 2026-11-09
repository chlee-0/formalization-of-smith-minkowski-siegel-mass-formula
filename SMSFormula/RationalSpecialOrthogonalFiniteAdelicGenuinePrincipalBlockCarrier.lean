import SMSFormula.RationalSpecialOrthogonalFiniteAdelicCoherentBlockCylinder

/-!
# Genuine finite-adelic principal-block carriers

For a finite exceptional set `S`, this module packages the finite-adelic
special-orthogonal elements whose matrix and inverse entries are integral
outside `S` as a subgroup of the genuine finite-adelic group.  Its topology is
the inherited finite-adele restricted-product topology.

Simultaneous local evaluation maps this genuine block to the direct mixed
principal block.  Reverse restricted-family assembly gives the algebraic
inverse.  The component formulas and the continuity of forward evaluation are
stated explicitly.
-/

noncomputable section

open PositiveDefiniteIntegralLattice
open scoped Matrix RestrictedProduct

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1200000

local instance genuinePrincipalBlockPrimeFact
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

local instance genuinePrincipalBlockDecidableEq :
    DecidableEq (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  Classical.decEq _

/-! ## The genuine open principal-block subgroup -/

/-- The subgroup of genuine finite-adelic special-orthogonal elements whose
matrix and inverse entries are integral outside `S`. -/
def finiteAdelicSpecialOrthogonalGenuinePrincipalBlockSubgroup
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Subgroup V.FiniteAdelicSpecialOrthogonalGroup :=
  (V.finiteAdelicSpecialOrthogonalRestrictedFamilyPrincipalBlockSubgroup S).comap
    V.finiteAdelicSpecialOrthogonalRestrictedFamilyMulEquiv.toMonoidHom

/-- Membership in the genuine principal-block subgroup is literally the
entrywise finite-adele integrality condition outside `S`. -/
theorem mem_finiteAdelicSpecialOrthogonalGenuinePrincipalBlockSubgroup_iff
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (a : V.FiniteAdelicSpecialOrthogonalGroup) :
    a ∈ V.finiteAdelicSpecialOrthogonalGenuinePrincipalBlockSubgroup S ↔
      V.IsFiniteAdelicSpecialOrthogonalIntegralOutside S a := by
  change
    V.finiteAdelicSpecialOrthogonalRestrictedFamilyMulEquiv a ∈
        V.finiteAdelicSpecialOrthogonalRestrictedFamilyPrincipalBlock S ↔
      V.IsFiniteAdelicSpecialOrthogonalIntegralOutside S a
  exact
    V.finiteAdelicSpecialOrthogonalRestrictedFamilyMulEquiv_mem_principalBlock_iff
      S a

/-- The genuine principal block is open in the actual finite-adele
restricted-product topology. -/
theorem isOpen_finiteAdelicSpecialOrthogonalGenuinePrincipalBlockSubgroup
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    IsOpen
      (V.finiteAdelicSpecialOrthogonalGenuinePrincipalBlockSubgroup S :
        Set V.FiniteAdelicSpecialOrthogonalGroup) := by
  change IsOpen
    ((V.finiteAdelicSpecialOrthogonalRestrictedFamilyMulEquiv :
        V.FiniteAdelicSpecialOrthogonalGroup →
          V.FiniteAdelicSpecialOrthogonalRestrictedFamily) ⁻¹'
      V.finiteAdelicSpecialOrthogonalRestrictedFamilyPrincipalBlock S)
  exact
    V.isOpen_finiteAdelicSpecialOrthogonalRestrictedFamilyMulEquiv_preimage_principalBlock
      S

/-- The carrier of the genuine `S` principal block, with the inherited
finite-adelic topology. -/
abbrev FiniteAdelicSpecialOrthogonalGenuinePrincipalBlock
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :=
  V.finiteAdelicSpecialOrthogonalGenuinePrincipalBlockSubgroup S

/-! ## Evaluation into the direct mixed block -/

/-- Componentwise local evaluation of a genuine finite-adelic principal
block, retaining the outside-`S` integrality proof. -/
def finiteAdelicSpecialOrthogonalGenuinePrincipalBlockToMixedHom
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    V.FiniteAdelicSpecialOrthogonalGenuinePrincipalBlock S →*
      V.FiniteAdelicSpecialOrthogonalMixedPrincipalBlock S where
  toFun a v :=
    ⟨V.finiteAdelicSpecialOrthogonalHeightOneComponentHom v a.1, by
      intro hv
      have ha :
          V.IsFiniteAdelicSpecialOrthogonalIntegralOutside S a.1 :=
        (V.mem_finiteAdelicSpecialOrthogonalGenuinePrincipalBlockSubgroup_iff
          S a.1).1 a.2
      exact
        (V.finiteAdelicSpecialOrthogonalHeightOneComponent_isIntegral_iff
          a.1 v).2
          ((V.isFiniteAdelicSpecialOrthogonalIntegralOutside_iff S a.1).1
            ha v hv)⟩
  map_one' := by
    funext v
    apply Subtype.ext
    exact (V.finiteAdelicSpecialOrthogonalHeightOneComponentHom v).map_one
  map_mul' := by
    intro a b
    funext v
    apply Subtype.ext
    exact (V.finiteAdelicSpecialOrthogonalHeightOneComponentHom v).map_mul
      a.1 b.1

@[simp]
theorem
    finiteAdelicSpecialOrthogonalGenuinePrincipalBlockToMixedHom_apply_component
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (a : V.FiniteAdelicSpecialOrthogonalGenuinePrincipalBlock S)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    (V.finiteAdelicSpecialOrthogonalGenuinePrincipalBlockToMixedHom S a v).1 =
      V.finiteAdelicSpecialOrthogonalHeightOneComponentHom v a.1 :=
  rfl

/-- Evaluation from a genuine principal block to the direct mixed block is
continuous for the inherited finite-adele and direct product topologies. -/
theorem
    continuous_finiteAdelicSpecialOrthogonalGenuinePrincipalBlockToMixedHom
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Continuous
      (V.finiteAdelicSpecialOrthogonalGenuinePrincipalBlockToMixedHom S) := by
  apply continuous_pi
  intro v
  apply Continuous.subtype_mk
  exact
    (V.continuous_finiteAdelicSpecialOrthogonalHeightOneComponent v).comp
      continuous_subtype_val

/-! ## Reverse assembly -/

/-- Assemble a direct mixed principal-block family into the genuine
finite-adelic principal block. -/
def finiteAdelicSpecialOrthogonalMixedToGenuinePrincipalBlockHom
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    V.FiniteAdelicSpecialOrthogonalMixedPrincipalBlock S →*
      V.FiniteAdelicSpecialOrthogonalGenuinePrincipalBlock S where
  toFun g := by
    let p :=
      V.finiteAdelicSpecialOrthogonalMixedPrincipalBlockToPrincipalBlockHom S g
    let e := V.finiteAdelicSpecialOrthogonalRestrictedFamilyMulEquiv
    refine ⟨e.symm p.1, ?_⟩
    change e (e.symm p.1) ∈
      V.finiteAdelicSpecialOrthogonalRestrictedFamilyPrincipalBlockSubgroup S
    rw [e.apply_symm_apply]
    exact p.2
  map_one' := by
    apply Subtype.ext
    let p :=
      V.finiteAdelicSpecialOrthogonalMixedPrincipalBlockToPrincipalBlockHom S
    let e := V.finiteAdelicSpecialOrthogonalRestrictedFamilyMulEquiv
    change e.symm (p 1).1 = 1
    rw [p.map_one, Subgroup.coe_one, e.symm.map_one]
  map_mul' := by
    intro g h
    apply Subtype.ext
    let p :=
      V.finiteAdelicSpecialOrthogonalMixedPrincipalBlockToPrincipalBlockHom S
    let e := V.finiteAdelicSpecialOrthogonalRestrictedFamilyMulEquiv
    change e.symm (p (g * h)).1 = e.symm (p g).1 * e.symm (p h).1
    rw [p.map_mul, Subgroup.coe_mul, e.symm.map_mul]

@[simp]
theorem
    finiteAdelicSpecialOrthogonalMixedToGenuinePrincipalBlockHom_apply
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (g : V.FiniteAdelicSpecialOrthogonalMixedPrincipalBlock S) :
    (V.finiteAdelicSpecialOrthogonalMixedToGenuinePrincipalBlockHom S g).1 =
      V.finiteAdelicSpecialOrthogonalRestrictedFamilyAssembly
        (V.finiteAdelicSpecialOrthogonalMixedPrincipalBlockToPrincipalBlockHom
          S g).1 :=
  rfl

/-! ## Algebraic equivalence -/

/-- The genuine finite-adelic principal block is algebraically equivalent to
the direct mixed principal block. -/
def finiteAdelicSpecialOrthogonalGenuinePrincipalBlockMulEquiv
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    V.FiniteAdelicSpecialOrthogonalGenuinePrincipalBlock S ≃*
      V.FiniteAdelicSpecialOrthogonalMixedPrincipalBlock S where
  toFun :=
    V.finiteAdelicSpecialOrthogonalGenuinePrincipalBlockToMixedHom S
  invFun :=
    V.finiteAdelicSpecialOrthogonalMixedToGenuinePrincipalBlockHom S
  left_inv := by
    intro a
    apply Subtype.ext
    apply V.finiteAdelicSpecialOrthogonalHeightOneComponentsHom_injective
    funext v
    exact congr_fun
      (V.finiteAdelicSpecialOrthogonalHeightOneComponents_assembly
        (V.finiteAdelicSpecialOrthogonalMixedPrincipalBlockToPrincipalBlockHom
          S
          (V.finiteAdelicSpecialOrthogonalGenuinePrincipalBlockToMixedHom
            S a)))
      v
  right_inv := by
    intro g
    funext v
    apply Subtype.ext
    exact congr_fun
      (V.finiteAdelicSpecialOrthogonalHeightOneComponents_assembly
        (V.finiteAdelicSpecialOrthogonalMixedPrincipalBlockToPrincipalBlockHom
          S g))
      v
  map_mul' :=
    (V.finiteAdelicSpecialOrthogonalGenuinePrincipalBlockToMixedHom S).map_mul

@[simp]
theorem
    finiteAdelicSpecialOrthogonalGenuinePrincipalBlockMulEquiv_apply_component
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (a : V.FiniteAdelicSpecialOrthogonalGenuinePrincipalBlock S)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    (V.finiteAdelicSpecialOrthogonalGenuinePrincipalBlockMulEquiv S a v).1 =
      V.finiteAdelicSpecialOrthogonalHeightOneComponentHom v a.1 :=
  rfl

@[simp]
theorem
    finiteAdelicSpecialOrthogonalGenuinePrincipalBlockMulEquiv_symm_apply
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (g : V.FiniteAdelicSpecialOrthogonalMixedPrincipalBlock S) :
    (V.finiteAdelicSpecialOrthogonalGenuinePrincipalBlockMulEquiv S).symm g =
      V.finiteAdelicSpecialOrthogonalMixedToGenuinePrincipalBlockHom S g :=
  rfl

/-! ## Direct continuity of fixed-block assembly -/

private abbrev RationalFiniteAdelePrincipalBlock
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :=
  Πʳ v : IsDedekindDomain.HeightOneSpectrum ℤ,
    [v.adicCompletion ℚ, v.adicCompletionIntegers ℚ]_[
      Filter.principal
        {v : IsDedekindDomain.HeightOneSpectrum ℤ | v ∉ S}]

private theorem cofinite_le_principal_compl
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Filter.cofinite ≤ Filter.principal
      {v : IsDedekindDomain.HeightOneSpectrum ℤ | v ∉ S} := by
  rw [Filter.le_principal_iff]
  exact S.eventually_cofinite_notMem

/-- One matrix entry of a mixed block, first assembled in the fixed
principal restricted product. -/
private noncomputable def mixedPrincipalBlockMatrixEntry
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (g : V.FiniteAdelicSpecialOrthogonalMixedPrincipalBlock S)
    (i j : Fin n) :
    RationalFiniteAdelePrincipalBlock S :=
  ⟨fun v =>
      (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).symm
        ((g v).1.1.1.1 i j),
    by
      change ∀ᶠ v in Filter.principal
          {v : IsDedekindDomain.HeightOneSpectrum ℤ | v ∉ S},
        (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).symm
            ((g v).1.1.1.1 i j) ∈
          v.adicCompletionIntegers ℚ
      rw [Filter.eventually_principal]
      intro v hv
      exact ((g v).2 (by simpa using hv)).1 i j⟩

/-- One inverse-matrix entry of a mixed block, first assembled in the fixed
principal restricted product. -/
private noncomputable def mixedPrincipalBlockInverseMatrixEntry
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (g : V.FiniteAdelicSpecialOrthogonalMixedPrincipalBlock S)
    (i j : Fin n) :
    RationalFiniteAdelePrincipalBlock S :=
  ⟨fun v =>
      (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).symm
        ((((g v).1.1.1)⁻¹).1 i j),
    by
      change ∀ᶠ v in Filter.principal
          {v : IsDedekindDomain.HeightOneSpectrum ℤ | v ∉ S},
        (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).symm
            ((((g v).1.1.1)⁻¹).1 i j) ∈
          v.adicCompletionIntegers ℚ
      rw [Filter.eventually_principal]
      intro v hv
      exact ((g v).2 (by simpa using hv)).2 i j⟩

private theorem continuous_mixedPrincipalBlockMatrixEntry
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (i j : Fin n) :
    Continuous (fun g =>
      V.mixedPrincipalBlockMatrixEntry S g i j) := by
  apply RestrictedProduct.continuous_rng_of_principal.mpr
  apply continuous_pi
  intro v
  change Continuous (fun
    g : V.FiniteAdelicSpecialOrthogonalMixedPrincipalBlock S =>
    (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).symm
      ((g v).1.1.1.1 i j))
  have hmatrix :
      Continuous (fun
        g : V.FiniteAdelicSpecialOrthogonalMixedPrincipalBlock S =>
          (g v).1.1.1.1) :=
    Units.continuous_val.comp
      (continuous_subtype_val.comp
        (continuous_subtype_val.comp
          (continuous_subtype_val.comp (continuous_apply v))))
  exact
    (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).symm.continuous.comp
      ((continuous_apply j).comp ((continuous_apply i).comp hmatrix))

private theorem continuous_mixedPrincipalBlockInverseMatrixEntry
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (i j : Fin n) :
    Continuous (fun g =>
      V.mixedPrincipalBlockInverseMatrixEntry S g i j) := by
  apply RestrictedProduct.continuous_rng_of_principal.mpr
  apply continuous_pi
  intro v
  change Continuous (fun
    g : V.FiniteAdelicSpecialOrthogonalMixedPrincipalBlock S =>
    (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).symm
      ((((g v).1.1.1)⁻¹).1 i j))
  have hunits :
      Continuous (fun
        g : V.FiniteAdelicSpecialOrthogonalMixedPrincipalBlock S =>
          (g v).1.1.1) :=
    continuous_subtype_val.comp
      (continuous_subtype_val.comp
        (continuous_subtype_val.comp (continuous_apply v)))
  have hmatrix :
      Continuous (fun
        g : V.FiniteAdelicSpecialOrthogonalMixedPrincipalBlock S =>
          (((g v).1.1.1)⁻¹).1) :=
    Units.continuous_val.comp (continuous_inv.comp hunits)
  exact
    (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).symm.continuous.comp
      ((continuous_apply j).comp ((continuous_apply i).comp hmatrix))

private theorem
    continuous_restrictedFamilyMatrixEntry_mixedPrincipalBlock
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (i j : Fin n) :
    Continuous (fun g : V.FiniteAdelicSpecialOrthogonalMixedPrincipalBlock S =>
      V.finiteAdelicSpecialOrthogonalRestrictedFamilyMatrixEntry
        (V.finiteAdelicSpecialOrthogonalMixedPrincipalBlockToPrincipalBlockHom
          S g).1 i j) := by
  let R := fun v : IsDedekindDomain.HeightOneSpectrum ℤ =>
    v.adicCompletion ℚ
  let A : (v : IsDedekindDomain.HeightOneSpectrum ℤ) → Set (R v) :=
    fun v => v.adicCompletionIntegers ℚ
  let hS := cofinite_le_principal_compl S
  let inclusion :
      RationalFiniteAdelePrincipalBlock S → RationalFiniteAdele :=
    RestrictedProduct.inclusion R A hS
  have hinclusion : Continuous inclusion :=
    RestrictedProduct.continuous_inclusion hS
  have hentry :
      Continuous (fun g =>
        inclusion (V.mixedPrincipalBlockMatrixEntry S g i j)) :=
    hinclusion.comp (V.continuous_mixedPrincipalBlockMatrixEntry S i j)
  apply hentry.congr
  intro g
  ext v
  rfl

private theorem
    continuous_restrictedFamilyInverseMatrixEntry_mixedPrincipalBlock
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (i j : Fin n) :
    Continuous (fun g : V.FiniteAdelicSpecialOrthogonalMixedPrincipalBlock S =>
      V.finiteAdelicSpecialOrthogonalRestrictedFamilyInverseMatrixEntry
        (V.finiteAdelicSpecialOrthogonalMixedPrincipalBlockToPrincipalBlockHom
          S g).1 i j) := by
  let R := fun v : IsDedekindDomain.HeightOneSpectrum ℤ =>
    v.adicCompletion ℚ
  let A : (v : IsDedekindDomain.HeightOneSpectrum ℤ) → Set (R v) :=
    fun v => v.adicCompletionIntegers ℚ
  let hS := cofinite_le_principal_compl S
  let inclusion :
      RationalFiniteAdelePrincipalBlock S → RationalFiniteAdele :=
    RestrictedProduct.inclusion R A hS
  have hinclusion : Continuous inclusion :=
    RestrictedProduct.continuous_inclusion hS
  have hentry :
      Continuous (fun g =>
        inclusion (V.mixedPrincipalBlockInverseMatrixEntry S g i j)) :=
    hinclusion.comp
      (V.continuous_mixedPrincipalBlockInverseMatrixEntry S i j)
  apply hentry.congr
  intro g
  ext v
  rfl

private theorem continuous_restrictedFamilyMatrix_mixedPrincipalBlock
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Continuous (fun g : V.FiniteAdelicSpecialOrthogonalMixedPrincipalBlock S =>
      V.finiteAdelicSpecialOrthogonalRestrictedFamilyMatrix
        (V.finiteAdelicSpecialOrthogonalMixedPrincipalBlockToPrincipalBlockHom
          S g).1) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  exact
    V.continuous_restrictedFamilyMatrixEntry_mixedPrincipalBlock S i j

private theorem continuous_restrictedFamilyInverseMatrix_mixedPrincipalBlock
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Continuous (fun g : V.FiniteAdelicSpecialOrthogonalMixedPrincipalBlock S =>
      V.finiteAdelicSpecialOrthogonalRestrictedFamilyInverseMatrix
        (V.finiteAdelicSpecialOrthogonalMixedPrincipalBlockToPrincipalBlockHom
          S g).1) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  exact
    V.continuous_restrictedFamilyInverseMatrixEntry_mixedPrincipalBlock S i j

/-- Reverse assembly is continuous on every fixed principal block by direct
factorization through the corresponding principal restricted products. -/
theorem
    continuous_finiteAdelicSpecialOrthogonalMixedToGenuinePrincipalBlockHom
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Continuous
      (V.finiteAdelicSpecialOrthogonalMixedToGenuinePrincipalBlockHom S) := by
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  apply Units.continuous_iff.mpr
  constructor
  · change Continuous (fun g =>
      V.finiteAdelicSpecialOrthogonalRestrictedFamilyMatrix
        (V.finiteAdelicSpecialOrthogonalMixedPrincipalBlockToPrincipalBlockHom
          S g).1)
    exact V.continuous_restrictedFamilyMatrix_mixedPrincipalBlock S
  · change Continuous (fun g =>
      V.finiteAdelicSpecialOrthogonalRestrictedFamilyInverseMatrix
        (V.finiteAdelicSpecialOrthogonalMixedPrincipalBlockToPrincipalBlockHom
          S g).1)
    exact V.continuous_restrictedFamilyInverseMatrix_mixedPrincipalBlock S

/-- The genuine finite-adelic principal block and direct mixed block are
homeomorphic through literal evaluation and fixed-block assembly. -/
noncomputable def
    finiteAdelicSpecialOrthogonalGenuinePrincipalBlockHomeomorph
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    V.FiniteAdelicSpecialOrthogonalGenuinePrincipalBlock S ≃ₜ
      V.FiniteAdelicSpecialOrthogonalMixedPrincipalBlock S where
  toEquiv :=
    V.finiteAdelicSpecialOrthogonalGenuinePrincipalBlockMulEquiv S
  continuous_toFun :=
    V.continuous_finiteAdelicSpecialOrthogonalGenuinePrincipalBlockToMixedHom S
  continuous_invFun :=
    V.continuous_finiteAdelicSpecialOrthogonalMixedToGenuinePrincipalBlockHom S

/-- The genuine/direct principal-block identification is continuously
multiplicative. -/
noncomputable def
    finiteAdelicSpecialOrthogonalGenuinePrincipalBlockContinuousMulEquiv
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    V.FiniteAdelicSpecialOrthogonalGenuinePrincipalBlock S ≃ₜ*
      V.FiniteAdelicSpecialOrthogonalMixedPrincipalBlock S :=
  ContinuousMulEquiv.mk'
    (V.finiteAdelicSpecialOrthogonalGenuinePrincipalBlockHomeomorph S)
    (V.finiteAdelicSpecialOrthogonalGenuinePrincipalBlockMulEquiv S).map_mul

end RationalQuadraticSpaceMatrix
