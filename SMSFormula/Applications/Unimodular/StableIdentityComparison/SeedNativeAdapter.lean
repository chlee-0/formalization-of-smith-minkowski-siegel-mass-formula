import SMSFormula.Applications.Unimodular.StableIdentityComparison.SeedNormAdapter
import SMSFormula.Applications.Unimodular.StableIdentityComparison.NativeAssembly
import SMSFormula.Applications.Unimodular.StableIdentityComparison.NativeQuadraticLift
import SMSFormula.RationalAdeleFiniteLocalResidueCount
import SMSFormula.StandardAxiomsGuard

noncomputable section
open Matrix BigOperators PositiveDefiniteIntegralLattice UnimodularMass

namespace StableIdentityComparisonSeedNativeAdapter

open StableIdentityComparisonSeedNormAdapter


/-- The stored seed norm on canonical `ZMod 4` representatives is the native
quadratic form of `typeIISeed k` modulo eight. -/
lemma seedNormModEight_intCast (k : ℕ) (x : Fin (8 * k) → ℤ) :
    seedNormModEight k (fun i => (x i : ZMod 4)) =
      ((typeIISeed k).quadForm x : ZMod 8) := by
  rw [← PositiveDefiniteIntegralLattice.zmodQuadForm_intCast (typeIISeed k) 8 x]
  rw [← zmodQuadForm_lift_intCast_eq (typeIISeed k) x]
  unfold seedNormModEight PositiveDefiniteIntegralLattice.zmodQuadForm
  simp [Matrix.mulVec, dotProduct, Finset.mul_sum]
  ring_nf

/-- Matrix presentation of the native depth-three coordinate solutions for the
stored Type II seed. -/
abbrev typeIISeedDepthThreeCoordinateSolutionMatrix (k : ℕ) :=
  {X : Matrix (Fin (8 * k)) (Fin (8 * k)) (ZMod (primePowModulus 2 2 : ℕ)) //
    localDualQuotientLiftFamily (n := 8 * k) 2 2 X ∈
      localDualQuotientSolutionFamilies (typeIISeed k) 2 3
        (primePowCoordinateSubmodule (n := 8 * k) 2 2)
        (primePowCoordinateSubmodule_rank (n := 8 * k) 2 2)}

instance (k : ℕ) : Fintype (typeIISeedDepthThreeCoordinateSolutionMatrix k) := by
  classical
  unfold typeIISeedDepthThreeCoordinateSolutionMatrix
  infer_instance

/-- A native depth-three solution matrix for `typeIISeed k` preserves the stored
seed norm modulo eight on `ZMod 4` coordinates. -/
theorem typeIISeedDepthThreeCoordinateSolutionMatrix_to_seedNormIsometry_mem
    (k : ℕ) (X : typeIISeedDepthThreeCoordinateSolutionMatrix k) :
    ∀ v : Fin (8 * k) → ZMod 4,
      seedNormModEight k (X.1.mulVec v) = seedNormModEight k v := by
  intro v
  let x : Fin (8 * k) → ℤ := fun i => (v i).val
  let D : Submodule ℤ (Fin (8 * k) → ℤ) := primePowCoordinateSubmodule (n := 8 * k) 2 2
  let Y : Fin (8 * k) → localDualQuotientTarget D :=
    localDualQuotientLiftFamily (n := 8 * k) 2 2 X.1
  let q : localDualQuotientTarget D := quotientBasisFamilyMap D Y x
  let y : Fin (8 * k) → ℤ := Quotient.out q
  have hq : quotientBasisFamilyMap D Y x = D.mkQ y := by
    change q = D.mkQ y
    exact (Submodule.Quotient.mk_out q).symm
  have hquad :
      ((typeIISeed k).quadForm y : ZMod (primePowModulus 2 3 : ℕ)) =
        ((typeIISeed k).quadForm x : ZMod (primePowModulus 2 3 : ℕ)) := by
    exact (mem_localDualQuotientSolutionFamilies_iff.mp X.2) x y hq
  have hxv : (fun i : Fin (8 * k) => (x i : ZMod 4)) = v := by
    funext i
    dsimp [x]
    exact ZMod.natCast_zmod_val (v i)
  have hvec :
      (fun i : Fin (8 * k) => (y i : ZMod (primePowModulus 2 2 : ℕ))) =
        X.1.mulVec v := by
    have hmat := localDualQuotientFamilyMatrix_mulVec_eq (n := 8 * k) 2 2 Y x
    have hqcoord :
        primePowQuotientVector (n := 8 * k) 2 2
            (quotientBasisFamilyMap D Y x) =
          fun i : Fin (8 * k) => (y i : ZMod (primePowModulus 2 2 : ℕ)) := by
      rw [hq]
      exact primePowQuotientVector_mkQ (n := 8 * k) 2 2 y
    have hm : localDualQuotientFamilyMatrix (n := 8 * k) 2 2 Y = X.1 := by
      exact localDualQuotientFamilyMatrix_liftFamily (n := 8 * k) 2 2 X.1
    calc
      (fun i : Fin (8 * k) => (y i : ZMod (primePowModulus 2 2 : ℕ))) =
          (localDualQuotientFamilyMatrix (n := 8 * k) 2 2 Y).mulVec
            (fun j : Fin (8 * k) => (x j : ZMod (primePowModulus 2 2 : ℕ))) := by
            exact (hmat.trans hqcoord).symm
      _ = X.1.mulVec v := by
            rw [hm]
            change X.1.mulVec (fun j : Fin (8 * k) => (x j : ZMod 4)) = X.1.mulVec v
            rw [hxv]
  calc
    seedNormModEight k (X.1.mulVec v) = seedNormModEight k (fun i => (y i : ZMod 4)) :=
      congrArg (seedNormModEight k) hvec.symm
    _ = ((typeIISeed k).quadForm y : ZMod 8) := seedNormModEight_intCast k y
    _ = ((typeIISeed k).quadForm x : ZMod 8) := by
      simpa [primePowModulus] using hquad
    _ = seedNormModEight k (fun i => (x i : ZMod 4)) := (seedNormModEight_intCast k x).symm
    _ = seedNormModEight k v := by rw [hxv]

/-- Native depth-three matrices map to the seed-norm isometry target. -/
def typeIISeedDepthThreeCoordinateSolutionMatrixToSeedNormIsometry
    (k : ℕ) (X : typeIISeedDepthThreeCoordinateSolutionMatrix k) : seedNormIsometryModFour k :=
  ⟨X.1, typeIISeedDepthThreeCoordinateSolutionMatrix_to_seedNormIsometry_mem k X⟩

/-- A seed-norm isometry supplies a native depth-three solution matrix for
`typeIISeed k`. -/
theorem seedNormIsometry_to_typeIISeedDepthThreeCoordinateSolutionMatrix_mem
    (k : ℕ) (X : seedNormIsometryModFour k) :
    localDualQuotientLiftFamily (n := 8 * k) 2 2 X.1 ∈
      localDualQuotientSolutionFamilies (typeIISeed k) 2 3
        (primePowCoordinateSubmodule (n := 8 * k) 2 2)
        (primePowCoordinateSubmodule_rank (n := 8 * k) 2 2) := by
  rw [mem_localDualQuotientSolutionFamilies_iff]
  intro x y hxy
  let D : Submodule ℤ (Fin (8 * k) → ℤ) := primePowCoordinateSubmodule (n := 8 * k) 2 2
  let Y : Fin (8 * k) → localDualQuotientTarget D :=
    localDualQuotientLiftFamily (n := 8 * k) 2 2 X.1
  have hvec :
      (fun i : Fin (8 * k) => (y i : ZMod 4)) =
        X.1.mulVec (fun j : Fin (8 * k) => (x j : ZMod 4)) := by
    have hmat := localDualQuotientFamilyMatrix_mulVec_eq (n := 8 * k) 2 2 Y x
    have hq := congrArg (primePowQuotientVector (n := 8 * k) 2 2) hxy
    have hm : localDualQuotientFamilyMatrix (n := 8 * k) 2 2 Y = X.1 := by
      exact localDualQuotientFamilyMatrix_liftFamily (n := 8 * k) 2 2 X.1
    exact (primePowQuotientVector_mkQ (n := 8 * k) 2 2 y).symm.trans
      (hq.symm.trans (hmat.symm.trans
        (congrArg (fun M : Matrix (Fin (8 * k)) (Fin (8 * k)) (ZMod 4) =>
          M.mulVec (fun j : Fin (8 * k) => (x j : ZMod 4))) hm)))
  change ((typeIISeed k).quadForm y : ZMod 8) = ((typeIISeed k).quadForm x : ZMod 8)
  exact (seedNormModEight_intCast k y).symm.trans
    ((congrArg (seedNormModEight k) hvec).trans
      ((X.2 _).trans (seedNormModEight_intCast k x)))

/-- Seed-norm isometries map back to native depth-three matrices. -/
def seedNormIsometryToTypeIISeedDepthThreeCoordinateSolutionMatrix
    (k : ℕ) (X : seedNormIsometryModFour k) : typeIISeedDepthThreeCoordinateSolutionMatrix k :=
  ⟨X.1, seedNormIsometry_to_typeIISeedDepthThreeCoordinateSolutionMatrix_mem k X⟩

/-- The native matrix target is exactly the stored seed-norm isometry target. -/
def typeIISeedDepthThreeCoordinateSolutionMatrixEquivSeedNormIsometry (k : ℕ) :
    typeIISeedDepthThreeCoordinateSolutionMatrix k ≃ seedNormIsometryModFour k where
  toFun := typeIISeedDepthThreeCoordinateSolutionMatrixToSeedNormIsometry k
  invFun := seedNormIsometryToTypeIISeedDepthThreeCoordinateSolutionMatrix k
  left_inv X := by
    apply Subtype.ext
    rfl
  right_inv X := by
    apply Subtype.ext
    rfl

/-- Cardinality form of the native matrix/seed-norm equivalence. -/
theorem typeIISeedDepthThreeCoordinateSolutionMatrix_natCard_eq_seedNorm (k : ℕ) :
    Nat.card (typeIISeedDepthThreeCoordinateSolutionMatrix k) =
      Nat.card (seedNormIsometryModFour k) :=
  Nat.card_congr (typeIISeedDepthThreeCoordinateSolutionMatrixEquivSeedNormIsometry k)

abbrev typeIISeedDepthThreeCoordinateSolutionFamily (k : ℕ) :=
  {Y : Fin (8 * k) → localDualQuotientTarget
      (primePowCoordinateSubmodule (n := 8 * k) 2 2) //
    Y ∈ localDualQuotientSolutionFamilies (typeIISeed k) 2 3
      (primePowCoordinateSubmodule (n := 8 * k) 2 2)
      (primePowCoordinateSubmodule_rank (n := 8 * k) 2 2)}

/-- The matrix and quotient-family presentations of the native coordinate
target are equivalent. -/
noncomputable def typeIISeedDepthThreeCoordinateSolutionMatrixEquivFamily (k : ℕ) :
    typeIISeedDepthThreeCoordinateSolutionMatrix k ≃
      typeIISeedDepthThreeCoordinateSolutionFamily k where
  toFun X := ⟨localDualQuotientLiftFamily (n := 8 * k) 2 2 X.1, X.2⟩
  invFun Y :=
    ⟨localDualQuotientFamilyMatrix (n := 8 * k) 2 2 Y.1, by
      rw [localDualQuotientLiftFamily_familyMatrix]
      simp⟩
  left_inv X := by
    apply Subtype.ext
    exact localDualQuotientFamilyMatrix_liftFamily (n := 8 * k) 2 2 X.1
  right_inv Y := by
    apply Subtype.ext
    exact localDualQuotientLiftFamily_familyMatrix (n := 8 * k) 2 2 Y.1

/-- The quotient-family presentation computes the native coordinate count. -/
theorem typeIISeedDepthThreeCoordinateSolutionFamily_natCard (k : ℕ) :
    Nat.card (typeIISeedDepthThreeCoordinateSolutionFamily k) =
      coordinateLocalDualQuotientCount (typeIISeed k) 2 3
        (primePowCoordinateSubmodule (n := 8 * k) 2 2)
        (primePowCoordinateSubmodule_rank (n := 8 * k) 2 2) := by
  unfold typeIISeedDepthThreeCoordinateSolutionFamily coordinateLocalDualQuotientCount
  rw [Nat.card_eq_fintype_card, Fintype.card_coe]

/-- The seed-norm target computes the native associated-bilinear quotient count
for every stored Type II seed. -/
theorem seedNormIsometryModFour_natCard_eq_native_count (k : ℕ) :
    Nat.card (seedNormIsometryModFour k) =
      associatedBilinearDualQuotientCount (typeIISeed k) 2 3 := by
  rw [associatedBilinearDualQuotientCount_two_three_eq_primePowCoordinateSubmodule
    (n := 8 * k) (L := typeIISeed k) (typeIISeed_isUnimodular k)]
  rw [← typeIISeedDepthThreeCoordinateSolutionFamily_natCard k]
  rw [← Nat.card_congr (typeIISeedDepthThreeCoordinateSolutionMatrixEquivFamily k)]
  rw [typeIISeedDepthThreeCoordinateSolutionMatrix_natCard_eq_seedNorm]

/-- A pointed stable coordinate certificate for `typeIISeed k` gives the exact
native-count premise needed by the Voskresenskii mass assembly. -/
theorem identity_native_count_eq_two_pow_mul_typeIISeed_of_stable (k : ℕ)
    (U V : Matrix (Fin (8 * k + 1)) (Fin (8 * k + 1)) (ZMod 4))
    (hUV : U * V = 1) (hVU : V * U = 1)
    (hQ : ∀ x : Fin (8 * k + 1) → ZMod 4,
      identityQuadraticModEight (U.mulVec x) =
        StableIdentityFixedLine.lineNorm (seedNormModEight k) x)
    (hw : U.mulVec (StableIdentityFixedLine.e (8 * k)) =
      StableIdentityComparison.characteristic (8 * k + 1)) :
    StableIdentityNativeAssembly.C (identityLattice (8 * k + 1)) =
      2 ^ (8 * k + 1) * StableIdentityNativeAssembly.C (typeIISeed k) := by
  dsimp [StableIdentityNativeAssembly.C]
  rw [identity_native_count_eq_two_pow_mul_seedNorm_of_stable k U V hUV hVU hQ hw]
  rw [seedNormIsometryModFour_natCard_eq_native_count k]

/-- Conditional ordinary mass endpoint from a pointed stable coordinate
certificate, with no separate native-count hypothesis. -/
theorem seed_mass_of_stable_count (k : ℕ) (hk : 0 < k)
    (U V : Matrix (Fin (8 * k + 1)) (Fin (8 * k + 1)) (ZMod 4))
    (hUV : U * V = 1) (hVU : V * U = 1)
    (hQ : ∀ x : Fin (8 * k + 1) → ZMod 4,
      identityQuadraticModEight (U.mulVec x) =
        StableIdentityFixedLine.lineNorm (seedNormModEight k) x)
    (hw : U.mulVec (StableIdentityFixedLine.e (8 * k)) =
      StableIdentityComparison.characteristic (8 * k + 1)) :
    (typeIISeed k).ordinaryGenusMass = typeIIConstant (8 * k) :=
  StableIdentityNativeAssembly.seed_mass_of_native_count k hk
    (identity_native_count_eq_two_pow_mul_typeIISeed_of_stable k U V hUV hVU hQ hw)

/-- Literal genus-sum version of `seed_mass_of_stable_count`. -/
theorem seed_literal_sum_of_stable_count (k : ℕ) (hk : 0 < k)
    (U V : Matrix (Fin (8 * k + 1)) (Fin (8 * k + 1)) (ZMod 4))
    (hUV : U * V = 1) (hVU : V * U = 1)
    (hQ : ∀ x : Fin (8 * k + 1) → ZMod 4,
      identityQuadraticModEight (U.mulVec x) =
        StableIdentityFixedLine.lineNorm (seedNormModEight k) x)
    (hw : U.mulVec (StableIdentityFixedLine.e (8 * k)) =
      StableIdentityComparison.characteristic (8 * k + 1)) :
    (∑ A : (typeIISeed k).genus,
      ((Fintype.card (genusClassRepresentative (typeIISeed k) A).IsometryGroup : ℚ)⁻¹)) =
        typeIIConstant (8 * k) :=
  StableIdentityNativeAssembly.seed_literal_sum_of_native_count k hk
    (identity_native_count_eq_two_pow_mul_typeIISeed_of_stable k U V hUV hVU hQ hw)

#assert_standard_axioms StableIdentityComparisonSeedNativeAdapter.zmodQuadForm_lift_intCast_eq
#assert_standard_axioms StableIdentityComparisonSeedNativeAdapter.seedNormModEight_intCast
#assert_standard_axioms StableIdentityComparisonSeedNativeAdapter.typeIISeedDepthThreeCoordinateSolutionMatrix_to_seedNormIsometry_mem
#assert_standard_axioms StableIdentityComparisonSeedNativeAdapter.seedNormIsometry_to_typeIISeedDepthThreeCoordinateSolutionMatrix_mem
#assert_standard_axioms StableIdentityComparisonSeedNativeAdapter.typeIISeedDepthThreeCoordinateSolutionMatrixEquivSeedNormIsometry
#assert_standard_axioms StableIdentityComparisonSeedNativeAdapter.seedNormIsometryModFour_natCard_eq_native_count
#assert_standard_axioms StableIdentityComparisonSeedNativeAdapter.identity_native_count_eq_two_pow_mul_typeIISeed_of_stable
#assert_standard_axioms StableIdentityComparisonSeedNativeAdapter.seed_mass_of_stable_count
#assert_standard_axioms StableIdentityComparisonSeedNativeAdapter.seed_literal_sum_of_stable_count

end StableIdentityComparisonSeedNativeAdapter
