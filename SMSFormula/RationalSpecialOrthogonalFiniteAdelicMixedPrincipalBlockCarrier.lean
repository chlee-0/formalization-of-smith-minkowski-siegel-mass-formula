import SMSFormula.RationalSpecialOrthogonalFiniteAdelicPrincipalBlockCarrier

/-!
# Mixed product carriers for finite-adelic principal blocks

For a rational quadratic-space matrix `V`, this module packages the local
integral special-orthogonal matrices as a subgroup at every height-one place.
Given a finite exceptional set `S`, the local principal-block factor is the
full local group at a place in `S` and the integral subgroup outside `S`.
This branching is implemented by the subgroup predicate

`v ∉ S → V.HeightOnePadicSpecialOrthogonalIsIntegral v g`.

The dependent product of these factors maps componentwise to the unrestricted
family of local special-orthogonal groups.  Its image is exactly the literal
outside-`S` integrality predicate.  Every such family is automatically
restricted, and the resulting map is a multiplicative equivalence with the
`S` principal-block subgroup of the restricted-family carrier.

The mixed carrier has only the product topology inherited from its explicit
local factors.  Componentwise inclusion into the unrestricted local product is
continuous.  No topology is transported through the final algebraic
equivalence, and no measure is constructed.
-/

noncomputable section

open PositiveDefiniteIntegralLattice
open scoped Matrix RestrictedProduct

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ}

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

local instance finiteAdelicMixedPrincipalBlockPrimeFact
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v).1) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

local instance finiteAdelicMixedPrincipalBlockDecidableEq :
    DecidableEq (IsDedekindDomain.HeightOneSpectrum ℤ) :=
  Classical.decEq _

/-! ## Integral local special-orthogonal subgroup -/

private theorem heightOnePadicSpecialOrthogonalIsIntegral_one_of_mixedBlock
    (V : RationalQuadraticSpaceMatrix n)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    V.HeightOnePadicSpecialOrthogonalIsIntegral v 1 := by
  let e := Rat.HeightOneSpectrum.adicCompletion.padicEquiv v
  constructor
  · intro i j
    change e.symm ((1 : Matrix (Fin n) (Fin n)
      ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]) i j) ∈
        v.adicCompletionIntegers ℚ
    by_cases h : i = j
    · subst j
      simp
    · simp [h]
  · intro i j
    change e.symm ((1 : Matrix (Fin n) (Fin n)
      ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).1]) i j) ∈
        v.adicCompletionIntegers ℚ
    by_cases h : i = j
    · subst j
      simp
    · simp [h]

private theorem heightOnePadicSpecialOrthogonalIsIntegral_mul_of_mixedBlock
    (V : RationalQuadraticSpaceMatrix n)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ)
    {g h : V.HeightOnePadicSpecialOrthogonalGroup v}
    (hg : V.HeightOnePadicSpecialOrthogonalIsIntegral v g)
    (hh : V.HeightOnePadicSpecialOrthogonalIsIntegral v h) :
    V.HeightOnePadicSpecialOrthogonalIsIntegral v (g * h) := by
  let e := Rat.HeightOneSpectrum.adicCompletion.padicEquiv v
  constructor
  · intro i j
    change e.symm ((g.1.1.1 * h.1.1.1) i j) ∈
      v.adicCompletionIntegers ℚ
    rw [Matrix.mul_apply, map_sum]
    exact Subring.sum_mem _ fun k _ => by
      rw [map_mul]
      exact Subring.mul_mem _ (hg.1 i k) (hh.1 k j)
  · intro i j
    change e.symm (((h.1.1⁻¹).1 * (g.1.1⁻¹).1) i j) ∈
      v.adicCompletionIntegers ℚ
    rw [Matrix.mul_apply, map_sum]
    exact Subring.sum_mem _ fun k _ => by
      rw [map_mul]
      exact Subring.mul_mem _ (hh.2 i k) (hg.2 k j)

private theorem heightOnePadicSpecialOrthogonalIsIntegral_inv_of_mixedBlock
    (V : RationalQuadraticSpaceMatrix n)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ)
    {g : V.HeightOnePadicSpecialOrthogonalGroup v}
    (hg : V.HeightOnePadicSpecialOrthogonalIsIntegral v g) :
    V.HeightOnePadicSpecialOrthogonalIsIntegral v g⁻¹ := by
  constructor
  · exact hg.2
  · simpa using hg.1

/-- The local p-adic special-orthogonal subgroup whose matrix and inverse
matrix are integral after transport to the height-one completion field. -/
def heightOnePadicSpecialOrthogonalIntegralSubgroup
    (V : RationalQuadraticSpaceMatrix n)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Subgroup (V.HeightOnePadicSpecialOrthogonalGroup v) where
  carrier :=
    {g | V.HeightOnePadicSpecialOrthogonalIsIntegral v g}
  one_mem' :=
    heightOnePadicSpecialOrthogonalIsIntegral_one_of_mixedBlock V v
  mul_mem' := by
    intro g h hg hh
    exact
      heightOnePadicSpecialOrthogonalIsIntegral_mul_of_mixedBlock
        V v hg hh
  inv_mem' := by
    intro g hg
    exact
      heightOnePadicSpecialOrthogonalIsIntegral_inv_of_mixedBlock V v hg

@[simp]
theorem mem_heightOnePadicSpecialOrthogonalIntegralSubgroup_iff
    (V : RationalQuadraticSpaceMatrix n)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ)
    (g : V.HeightOnePadicSpecialOrthogonalGroup v) :
    g ∈ V.heightOnePadicSpecialOrthogonalIntegralSubgroup v ↔
      V.HeightOnePadicSpecialOrthogonalIsIntegral v g :=
  Iff.rfl

/-- The carrier of integral local p-adic special-orthogonal matrices. -/
abbrev HeightOnePadicSpecialOrthogonalIntegralGroup
    (V : RationalQuadraticSpaceMatrix n)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :=
  V.heightOnePadicSpecialOrthogonalIntegralSubgroup v

/-! ## Local factors and their mixed dependent product -/

/-- The local factor for the `S` principal block.  At exceptional places this
is the full local group; away from `S` it is the integral local subgroup. -/
def finiteAdelicSpecialOrthogonalPrincipalBlockLocalFactorSubgroup
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    Subgroup (V.HeightOnePadicSpecialOrthogonalGroup v) where
  carrier :=
    {g | v ∉ S →
      V.HeightOnePadicSpecialOrthogonalIsIntegral v g}
  one_mem' := fun _hv =>
    heightOnePadicSpecialOrthogonalIsIntegral_one_of_mixedBlock V v
  mul_mem' := by
    intro g h hg hh hv
    exact
      heightOnePadicSpecialOrthogonalIsIntegral_mul_of_mixedBlock
        V v (hg hv) (hh hv)
  inv_mem' := by
    intro g hg hv
    exact
      heightOnePadicSpecialOrthogonalIsIntegral_inv_of_mixedBlock
        V v (hg hv)

@[simp]
theorem mem_finiteAdelicSpecialOrthogonalPrincipalBlockLocalFactorSubgroup_iff
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : IsDedekindDomain.HeightOneSpectrum ℤ)
    (g : V.HeightOnePadicSpecialOrthogonalGroup v) :
    g ∈ V.finiteAdelicSpecialOrthogonalPrincipalBlockLocalFactorSubgroup S v ↔
      (v ∉ S →
        V.HeightOnePadicSpecialOrthogonalIsIntegral v g) :=
  Iff.rfl

/-- At an exceptional place, the principal-block local factor is the full
local special-orthogonal group. -/
theorem finiteAdelicSpecialOrthogonalPrincipalBlockLocalFactorSubgroup_eq_top
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : IsDedekindDomain.HeightOneSpectrum ℤ)
    (hv : v ∈ S) :
    V.finiteAdelicSpecialOrthogonalPrincipalBlockLocalFactorSubgroup S v =
      ⊤ := by
  ext g
  simp [hv]

/-- Away from the exceptional set, the principal-block local factor is
exactly the integral local special-orthogonal subgroup. -/
theorem
    finiteAdelicSpecialOrthogonalPrincipalBlockLocalFactorSubgroup_eq_integral
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : IsDedekindDomain.HeightOneSpectrum ℤ)
    (hv : v ∉ S) :
    V.finiteAdelicSpecialOrthogonalPrincipalBlockLocalFactorSubgroup S v =
      V.heightOnePadicSpecialOrthogonalIntegralSubgroup v := by
  ext g
  simp [hv]

/-- The carrier of the local factor at `v` in the `S` principal block. -/
abbrev FiniteAdelicSpecialOrthogonalPrincipalBlockLocalFactor
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :=
  V.finiteAdelicSpecialOrthogonalPrincipalBlockLocalFactorSubgroup S v

/-- The explicit mixed dependent-product carrier for the `S` principal block.
Its factor is full at `v ∈ S` and integral at `v ∉ S`. -/
abbrev FiniteAdelicSpecialOrthogonalMixedPrincipalBlock
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :=
  (v : IsDedekindDomain.HeightOneSpectrum ℤ) →
    V.FiniteAdelicSpecialOrthogonalPrincipalBlockLocalFactor S v

/-- Componentwise inclusion of the mixed principal block into the
unrestricted family of local special-orthogonal groups. -/
def finiteAdelicSpecialOrthogonalMixedPrincipalBlockFamilyHom
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    V.FiniteAdelicSpecialOrthogonalMixedPrincipalBlock S →*
      V.HeightOnePadicSpecialOrthogonalGroupProduct where
  toFun g v := (g v).1
  map_one' := by
    funext v
    rfl
  map_mul' := by
    intro g h
    funext v
    rfl

@[simp]
theorem finiteAdelicSpecialOrthogonalMixedPrincipalBlockFamilyHom_apply
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (g : V.FiniteAdelicSpecialOrthogonalMixedPrincipalBlock S)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    V.finiteAdelicSpecialOrthogonalMixedPrincipalBlockFamilyHom S g v =
      (g v).1 :=
  rfl

/-- Componentwise inclusion of the explicit mixed carrier into the
unrestricted local product is continuous for the product topology inherited
from the displayed local factors. -/
theorem continuous_finiteAdelicSpecialOrthogonalMixedPrincipalBlockFamilyHom
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Continuous
      (V.finiteAdelicSpecialOrthogonalMixedPrincipalBlockFamilyHom S) :=
  continuous_pi fun v =>
    continuous_subtype_val.comp (continuous_apply v)

/-- The image of the mixed product in the unrestricted local product is
exactly the family-level outside-`S` integrality predicate. -/
theorem range_finiteAdelicSpecialOrthogonalMixedPrincipalBlockFamilyHom
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Set.range
        (V.finiteAdelicSpecialOrthogonalMixedPrincipalBlockFamilyHom S) =
      {g : V.HeightOnePadicSpecialOrthogonalGroupProduct |
        ∀ v, v ∉ S →
          V.HeightOnePadicSpecialOrthogonalIsIntegral v (g v)} := by
  ext g
  constructor
  · rintro ⟨x, rfl⟩
    intro v hv
    exact (x v).2 hv
  · intro hg
    let x : V.FiniteAdelicSpecialOrthogonalMixedPrincipalBlock S :=
      fun v => ⟨g v, hg v⟩
    refine ⟨x, ?_⟩
    funext v
    rfl

/-! ## Principal-block subgroup and algebraic equivalence -/

/-- The `S` principal block as a subgroup of the restricted-family carrier. -/
def finiteAdelicSpecialOrthogonalRestrictedFamilyPrincipalBlockSubgroup
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    Subgroup V.FiniteAdelicSpecialOrthogonalRestrictedFamily where
  carrier :=
    V.finiteAdelicSpecialOrthogonalRestrictedFamilyPrincipalBlock S
  one_mem' := by
    intro v _hv
    exact heightOnePadicSpecialOrthogonalIsIntegral_one_of_mixedBlock V v
  mul_mem' := by
    intro g h hg hh v hv
    exact
      heightOnePadicSpecialOrthogonalIsIntegral_mul_of_mixedBlock
        V v (hg v hv) (hh v hv)
  inv_mem' := by
    intro g hg v hv
    exact
      heightOnePadicSpecialOrthogonalIsIntegral_inv_of_mixedBlock
        V v (hg v hv)

@[simp]
theorem
    mem_finiteAdelicSpecialOrthogonalRestrictedFamilyPrincipalBlockSubgroup_iff
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (g : V.FiniteAdelicSpecialOrthogonalRestrictedFamily) :
    g ∈
        V.finiteAdelicSpecialOrthogonalRestrictedFamilyPrincipalBlockSubgroup S ↔
      g ∈ V.finiteAdelicSpecialOrthogonalRestrictedFamilyPrincipalBlock S :=
  Iff.rfl

/-- The carrier of the `S` principal-block subgroup. -/
abbrev FiniteAdelicSpecialOrthogonalRestrictedFamilyPrincipalBlock
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :=
  V.finiteAdelicSpecialOrthogonalRestrictedFamilyPrincipalBlockSubgroup S

/-- A mixed principal-block family, viewed as a restricted family in the
corresponding principal-block subgroup. -/
def finiteAdelicSpecialOrthogonalMixedPrincipalBlockToPrincipalBlockHom
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    V.FiniteAdelicSpecialOrthogonalMixedPrincipalBlock S →*
      V.FiniteAdelicSpecialOrthogonalRestrictedFamilyPrincipalBlock S where
  toFun g := by
    have hrestricted :
        V.IsFiniteAdelicSpecialOrthogonalRestrictedFamily
          (V.finiteAdelicSpecialOrthogonalMixedPrincipalBlockFamilyHom S g) :=
      S.eventually_cofinite_notMem.mono fun v hv => (g v).2 hv
    exact
      ⟨⟨V.finiteAdelicSpecialOrthogonalMixedPrincipalBlockFamilyHom S g,
          hrestricted⟩,
        fun v hv => (g v).2 hv⟩
  map_one' := by
    apply Subtype.ext
    apply Subtype.ext
    funext v
    rfl
  map_mul' := by
    intro g h
    apply Subtype.ext
    apply Subtype.ext
    funext v
    rfl

@[simp]
theorem
    finiteAdelicSpecialOrthogonalMixedPrincipalBlockToPrincipalBlockHom_apply_component
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (g : V.FiniteAdelicSpecialOrthogonalMixedPrincipalBlock S)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    (V.finiteAdelicSpecialOrthogonalMixedPrincipalBlockToPrincipalBlockHom S g).1.1
        v =
      (g v).1 :=
  rfl

/-- A restricted family in the `S` principal block, viewed in the explicit
mixed dependent product. -/
def finiteAdelicSpecialOrthogonalPrincipalBlockToMixedHom
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    V.FiniteAdelicSpecialOrthogonalRestrictedFamilyPrincipalBlock S →*
      V.FiniteAdelicSpecialOrthogonalMixedPrincipalBlock S where
  toFun g v :=
    ⟨g.1.1 v, fun hv => g.2 v hv⟩
  map_one' := by
    funext v
    apply Subtype.ext
    rfl
  map_mul' := by
    intro g h
    funext v
    apply Subtype.ext
    rfl

@[simp]
theorem
    finiteAdelicSpecialOrthogonalPrincipalBlockToMixedHom_apply_component
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (g : V.FiniteAdelicSpecialOrthogonalRestrictedFamilyPrincipalBlock S)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    (V.finiteAdelicSpecialOrthogonalPrincipalBlockToMixedHom S g v).1 =
      g.1.1 v :=
  rfl

/-- The explicit mixed dependent product is multiplicatively equivalent to
the `S` principal-block subgroup of restricted local families.  This is an
algebraic equivalence only; no topology is transported through it. -/
def finiteAdelicSpecialOrthogonalMixedPrincipalBlockMulEquiv
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ)) :
    V.FiniteAdelicSpecialOrthogonalMixedPrincipalBlock S ≃*
      V.FiniteAdelicSpecialOrthogonalRestrictedFamilyPrincipalBlock S where
  toFun :=
    V.finiteAdelicSpecialOrthogonalMixedPrincipalBlockToPrincipalBlockHom S
  invFun :=
    V.finiteAdelicSpecialOrthogonalPrincipalBlockToMixedHom S
  left_inv := by
    intro g
    funext v
    apply Subtype.ext
    rfl
  right_inv := by
    intro g
    apply Subtype.ext
    apply Subtype.ext
    funext v
    rfl
  map_mul' :=
    (V.finiteAdelicSpecialOrthogonalMixedPrincipalBlockToPrincipalBlockHom S).map_mul

@[simp]
theorem finiteAdelicSpecialOrthogonalMixedPrincipalBlockMulEquiv_apply_component
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (g : V.FiniteAdelicSpecialOrthogonalMixedPrincipalBlock S)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    (V.finiteAdelicSpecialOrthogonalMixedPrincipalBlockMulEquiv S g).1.1 v =
      (g v).1 :=
  rfl

@[simp]
theorem
    finiteAdelicSpecialOrthogonalMixedPrincipalBlockMulEquiv_symm_apply_component
    (V : RationalQuadraticSpaceMatrix n)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ))
    (g : V.FiniteAdelicSpecialOrthogonalRestrictedFamilyPrincipalBlock S)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    ((V.finiteAdelicSpecialOrthogonalMixedPrincipalBlockMulEquiv S).symm g v).1 =
      g.1.1 v :=
  rfl

end RationalQuadraticSpaceMatrix
