import SMSFormula.RationalQuadraticKummerSurjectivity
import Mathlib.FieldTheory.AlgebraicClosure

/-!
# Global/local compatibility for continuous quadratic Kummer theory

Mathlib's chosen absolute Galois groups are not directly functorial in a
field embedding.  For an extension `L / Q`, this file instead takes the
relative algebraic closure of `Q` inside `AlgebraicClosure L`, chooses its
canonical noncomputable comparison with `AlgebraicClosure Q`, and restricts
local automorphisms to that relative closure.  Conjugation gives the required
homomorphism

```text
G_L -> G_Q.
```

The homomorphism is continuous for the Krull topologies.  The proof pulls a
finite-dimensional global intermediate-field neighborhood back to the local
stabilizer of the images of a finite basis.  The resulting pullback on
continuous `ZMod 2` characters is therefore genuine continuous cohomology,
not an abstract replacement.

The second half proves that this pullback commutes with the quadratic Kummer
maps and scalar extension on square classes.  Specializing to `R` and all
`Q_p` transports the rational square-class local-global theorem to the
continuous order-two cohomology localization kernel.
-/

noncomputable section

namespace RationalTamagawa

variable (L : Type) [Field L] [CharZero L] [Algebra ℚ L]

/-- The relative algebraic closure of `Q` in a chosen algebraic closure of
`L`. -/
abbrev RationalRelativeAlgebraicClosure :=
  algebraicClosure ℚ (AlgebraicClosure L)

set_option backward.isDefEq.respectTransparency false in
/-- A chosen comparison of the two algebraic closures of `Q`. -/
noncomputable def rationalClosureEquivRelativeClosure :
    AlgebraicClosure ℚ ≃ₐ[ℚ] RationalRelativeAlgebraicClosure L :=
  IsAlgClosure.equiv ℚ _ _

/-- Regard a local absolute Galois automorphism as a `Q`-algebra
automorphism. -/
abbrev localAbsoluteGaloisAsRationalAlgEquiv
    (σ : Field.absoluteGaloisGroup L) :
    AlgebraicClosure L ≃ₐ[ℚ] AlgebraicClosure L :=
  (absoluteGaloisAlgEquiv L σ).restrictScalars ℚ

/-- Restrict a local automorphism to the relative algebraic closure of `Q`. -/
noncomputable def localAbsoluteGaloisOnRelativeClosure
    (σ : Field.absoluteGaloisGroup L) :
    RationalRelativeAlgebraicClosure L ≃ₐ[ℚ]
      RationalRelativeAlgebraicClosure L :=
  (localAbsoluteGaloisAsRationalAlgEquiv L σ).algebraicClosure

@[simp]
theorem localAbsoluteGaloisOnRelativeClosure_val
    (σ : Field.absoluteGaloisGroup L)
    (x : RationalRelativeAlgebraicClosure L) :
    ((localAbsoluteGaloisOnRelativeClosure L σ x :
        RationalRelativeAlgebraicClosure L) : AlgebraicClosure L) =
      absoluteGaloisAlgEquiv L σ x := by
  rfl

/-- The value of the global restriction map on a local absolute Galois
automorphism. -/
noncomputable def localToRationalAbsoluteGaloisValue
    (σ : Field.absoluteGaloisGroup L) : Field.absoluteGaloisGroup ℚ :=
  (rationalClosureEquivRelativeClosure L).trans
    ((localAbsoluteGaloisOnRelativeClosure L σ).trans
      (rationalClosureEquivRelativeClosure L).symm)

/-- Restriction from the local absolute Galois group to the rational one,
constructed through the relative algebraic closure. -/
noncomputable def localToRationalAbsoluteGaloisHom :
    Field.absoluteGaloisGroup L →* Field.absoluteGaloisGroup ℚ where
  toFun := localToRationalAbsoluteGaloisValue L
  map_one' := by
    apply AlgEquiv.ext
    intro x
    change (rationalClosureEquivRelativeClosure L).symm
        (localAbsoluteGaloisOnRelativeClosure L 1
          (rationalClosureEquivRelativeClosure L x)) = x
    apply (rationalClosureEquivRelativeClosure L).injective
    simp only [AlgEquiv.apply_symm_apply]
    apply Subtype.ext
    rfl
  map_mul' σ τ := by
    apply AlgEquiv.ext
    intro x
    change (rationalClosureEquivRelativeClosure L).symm
        (localAbsoluteGaloisOnRelativeClosure L (σ * τ)
          (rationalClosureEquivRelativeClosure L x)) =
      (rationalClosureEquivRelativeClosure L).symm
        (localAbsoluteGaloisOnRelativeClosure L σ
          (rationalClosureEquivRelativeClosure L
            ((rationalClosureEquivRelativeClosure L).symm
              (localAbsoluteGaloisOnRelativeClosure L τ
                (rationalClosureEquivRelativeClosure L x)))))
    rw [AlgEquiv.apply_symm_apply]
    apply congrArg (rationalClosureEquivRelativeClosure L).symm
    apply Subtype.ext
    rfl

set_option backward.isDefEq.respectTransparency false in
/-- The relative-closure restriction homomorphism is continuous for the two
Krull topologies. -/
theorem localToRationalAbsoluteGaloisHom_continuous :
    Continuous (localToRationalAbsoluteGaloisHom L) := by
  apply continuous_of_continuousAt_one (localToRationalAbsoluteGaloisHom L)
  rw [continuousAt_def]
  intro N hN
  rw [map_one] at hN
  change (N : Set (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) ∈
    nhds (1 : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) at hN
  obtain ⟨E, hEfin, hEN⟩ :=
    (krullTopology_mem_nhds_one_iff ℚ (AlgebraicClosure ℚ) N).mp hN
  let b := Module.finBasis ℚ E
  let S : Set (AlgebraicClosure L) :=
    Set.range fun i : Fin (Module.finrank ℚ E) =>
      ((rationalClosureEquivRelativeClosure L (b i) :
        RationalRelativeAlgebraicClosure L) : AlgebraicClosure L)
  let ELocal : IntermediateField L (AlgebraicClosure L) :=
    IntermediateField.adjoin L S
  have hSIntegral : ∀ x ∈ S, IsIntegral L x := by
    intro x hx
    exact Algebra.IsIntegral.isIntegral x
  letI : FiniteDimensional L ELocal :=
    IntermediateField.finiteDimensional_adjoin hSIntegral
  apply mem_nhds_iff.mpr
  let U : Set (Field.absoluteGaloisGroup L) :=
    {σ | absoluteGaloisAlgEquiv L σ ∈ ELocal.fixingSubgroup}
  have hUOpen : IsOpen U := by
    have hopen := IntermediateField.fixingSubgroup_isOpen ELocal
    change IsOpen {σ : Field.absoluteGaloisGroup L |
      absoluteGaloisAlgEquiv L σ ∈ ELocal.fixingSubgroup}
    exact hopen
  refine ⟨U, ?_, hUOpen, ?_⟩
  · intro σ hσ
    apply hEN
    change absoluteGaloisAlgEquiv ℚ
      ((localToRationalAbsoluteGaloisHom L) σ) ∈ E.fixingSubgroup
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    let f : E →ₗ[ℚ] AlgebraicClosure ℚ :=
      (absoluteGaloisAlgEquiv ℚ
        ((localToRationalAbsoluteGaloisHom L) σ)).toLinearMap.comp
          E.val.toLinearMap
    have hf : f = E.val.toLinearMap := by
      apply b.ext
      intro i
      have hfix : absoluteGaloisAlgEquiv L σ
          ((rationalClosureEquivRelativeClosure L (b i) :
            RationalRelativeAlgebraicClosure L) : AlgebraicClosure L) =
          ((rationalClosureEquivRelativeClosure L (b i) :
            RationalRelativeAlgebraicClosure L) : AlgebraicClosure L) := by
        have hmemS : ((rationalClosureEquivRelativeClosure L (b i) :
            RationalRelativeAlgebraicClosure L) : AlgebraicClosure L) ∈ S :=
          ⟨i, rfl⟩
        change absoluteGaloisAlgEquiv L σ ∈ ELocal.fixingSubgroup at hσ
        exact hσ ⟨_, IntermediateField.subset_adjoin L S hmemS⟩
      change (rationalClosureEquivRelativeClosure L).symm
          (localAbsoluteGaloisOnRelativeClosure L σ
            (rationalClosureEquivRelativeClosure L (b i))) = b i
      apply (rationalClosureEquivRelativeClosure L).injective
      simp only [AlgEquiv.apply_symm_apply]
      apply Subtype.ext
      exact hfix
    exact LinearMap.congr_fun hf (⟨x, hx⟩ : E)
  · exact one_mem ELocal.fixingSubgroup

/-- The continuous version of the absolute-Galois restriction map. -/
noncomputable def localToRationalAbsoluteGaloisContinuousHom :
    Field.absoluteGaloisGroup L →ₜ* Field.absoluteGaloisGroup ℚ :=
  ⟨localToRationalAbsoluteGaloisHom L,
    localToRationalAbsoluteGaloisHom_continuous L⟩

/-- The additive-tagged restriction map used to precompose continuous
order-two characters. -/
noncomputable def additiveLocalToRationalAbsoluteGaloisContinuousHom :
    Additive (Field.absoluteGaloisGroup L) →ₜ+
      Additive (Field.absoluteGaloisGroup ℚ) where
  toFun σ := Additive.ofMul
    (localToRationalAbsoluteGaloisHom L σ.toMul)
  map_zero' := congrArg Additive.ofMul
    (map_one (localToRationalAbsoluteGaloisHom L))
  map_add' σ τ := congrArg Additive.ofMul
    (map_mul (localToRationalAbsoluteGaloisHom L) σ.toMul τ.toMul)
  continuous_toFun := localToRationalAbsoluteGaloisHom_continuous L

/-- Pullback of continuous order-two rational characters to `L`. -/
noncomputable def muTwoContinuousH1Restriction :
    MuTwoContinuousH1 ℚ →+ MuTwoContinuousH1 L where
  toFun χ := χ.comp (additiveLocalToRationalAbsoluteGaloisContinuousHom L)
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp]
theorem muTwoContinuousH1Restriction_apply
    (χ : MuTwoContinuousH1 ℚ)
    (σ : Additive (Field.absoluteGaloisGroup L)) :
    muTwoContinuousH1Restriction L χ σ =
      χ (Additive.ofMul
        (localToRationalAbsoluteGaloisHom L σ.toMul)) :=
  rfl

/-- The chosen embedding of the rational algebraic closure into the local
algebraic closure. -/
noncomputable def rationalClosureEmbeddingInLocalClosure :
    AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure L :=
  (algebraicClosure ℚ (AlgebraicClosure L)).val.comp
    (rationalClosureEquivRelativeClosure L).toAlgHom

/-- The chosen rational-closure embedding intertwines a local automorphism
with its restriction to the rational absolute Galois group. -/
theorem rationalClosureEmbeddingInLocalClosure_equivariant
    (σ : Field.absoluteGaloisGroup L) (x : AlgebraicClosure ℚ) :
    absoluteGaloisAlgEquiv L σ (rationalClosureEmbeddingInLocalClosure L x) =
      rationalClosureEmbeddingInLocalClosure L
        (absoluteGaloisAlgEquiv ℚ
          (localToRationalAbsoluteGaloisHom L σ) x) := by
  change absoluteGaloisAlgEquiv L σ
      ((rationalClosureEquivRelativeClosure L x :
        RationalRelativeAlgebraicClosure L) : AlgebraicClosure L) =
    ((rationalClosureEquivRelativeClosure L
      ((rationalClosureEquivRelativeClosure L).symm
        (localAbsoluteGaloisOnRelativeClosure L σ
          (rationalClosureEquivRelativeClosure L x))) :
        RationalRelativeAlgebraicClosure L) : AlgebraicClosure L)
  rw [AlgEquiv.apply_symm_apply]
  rfl

/-- The chosen quadratic root is fixed or negated according to its own
quadratic character. -/
theorem rationalQuadraticRoot_action_eq_if (a : ℚˣ)
    (σ : Field.absoluteGaloisGroup ℚ) :
    absoluteGaloisAlgEquiv ℚ σ (quadraticRoot ℚ a) =
      if quadraticCharacter ℚ a (Additive.ofMul σ) = 0 then
        quadraticRoot ℚ a else -quadraticRoot ℚ a := by
  by_cases hσ : quadraticCharacter ℚ a (Additive.ofMul σ) = 0
  · rw [if_pos hσ]
    by_cases hfix : absoluteGaloisAlgEquiv ℚ σ (quadraticRoot ℚ a) =
        quadraticRoot ℚ a
    · exact hfix
    · change quadraticCharacterValue ℚ a σ = 0 at hσ
      simp [quadraticCharacterValue, hfix] at hσ
  · rw [if_neg hσ]
    rcases absoluteGalois_quadraticRoot_eq_or_eq_neg ℚ a σ with h | h
    · exfalso
      apply hσ
      change quadraticCharacterValue ℚ a σ = 0
      simp [quadraticCharacterValue, h]
    · exact h

/-- The continuous quadratic character commutes with scalar extension from
`Q` to `L` and pullback along the relative-closure restriction map. -/
theorem quadraticCharacter_scalarExtension (a : ℚˣ) :
    quadraticCharacter L (Units.map (algebraMap ℚ L) a) =
      muTwoContinuousH1Restriction L (quadraticCharacter ℚ a) := by
  let y : AlgebraicClosure L :=
    rationalClosureEmbeddingInLocalClosure L (quadraticRoot ℚ a)
  apply quadraticCharacter_eq_of_sq_eq_and_action L
    (muTwoContinuousH1Restriction L (quadraticCharacter ℚ a))
    (Units.map (algebraMap ℚ L) a) y
  · change rationalClosureEmbeddingInLocalClosure L (quadraticRoot ℚ a) ≠ 0
    intro h
    apply quadraticRoot_ne_zero ℚ a
    apply (rationalClosureEmbeddingInLocalClosure L).injective
    simpa using h
  · change (rationalClosureEmbeddingInLocalClosure L (quadraticRoot ℚ a)) ^ 2 =
      algebraMap L (AlgebraicClosure L) (algebraMap ℚ L (a : ℚ))
    calc
      _ = rationalClosureEmbeddingInLocalClosure L ((quadraticRoot ℚ a) ^ 2) :=
        (map_pow (rationalClosureEmbeddingInLocalClosure L) _ 2).symm
      _ = rationalClosureEmbeddingInLocalClosure L
          (algebraMap ℚ (AlgebraicClosure ℚ) (a : ℚ)) :=
        congrArg (rationalClosureEmbeddingInLocalClosure L) (quadraticRoot_sq ℚ a)
      _ = algebraMap ℚ (AlgebraicClosure L) (a : ℚ) := by simp
      _ = algebraMap L (AlgebraicClosure L) (algebraMap ℚ L (a : ℚ)) := by
        rw [IsScalarTower.algebraMap_apply ℚ L (AlgebraicClosure L)]
  · intro σ
    change absoluteGaloisAlgEquiv L σ
        (rationalClosureEmbeddingInLocalClosure L (quadraticRoot ℚ a)) = _
    rw [rationalClosureEmbeddingInLocalClosure_equivariant,
      rationalQuadraticRoot_action_eq_if]
    simp only [muTwoContinuousH1Restriction_apply]
    dsimp [y]
    split <;> simp_all

/-- Multiplicative packaging of pullback on continuous order-two
characters. -/
noncomputable def muTwoContinuousH1RestrictionMultiplicative :
    Multiplicative (MuTwoContinuousH1 ℚ) →*
      Multiplicative (MuTwoContinuousH1 L) where
  toFun χ := Multiplicative.ofAdd
    (muTwoContinuousH1Restriction L χ.toAdd)
  map_one' := congrArg Multiplicative.ofAdd
    (map_zero (muTwoContinuousH1Restriction L))
  map_mul' χ ψ := congrArg Multiplicative.ofAdd
    (map_add (muTwoContinuousH1Restriction L) χ.toAdd ψ.toAdd)

/-- Pointwise commutativity of scalar extension on square classes and
restriction on continuous quadratic characters. -/
theorem quadraticKummerHom_squareClassMap (c : Rat.SquareClass ℚ) :
    muTwoContinuousH1RestrictionMultiplicative L
        (quadraticKummerHom ℚ c) =
      quadraticKummerHom L
        (Rat.squareClassMap (algebraMap ℚ L) c) := by
  induction c using QuotientGroup.induction_on with
  | _ a =>
      change Multiplicative.ofAdd
          (muTwoContinuousH1Restriction L (quadraticCharacter ℚ a)) =
        Multiplicative.ofAdd
          (quadraticCharacter L (Units.map (algebraMap ℚ L) a))
      exact congrArg Multiplicative.ofAdd
        (quadraticCharacter_scalarExtension L a).symm

/-- The global/local quadratic Kummer square commutes as an equality of
homomorphisms. -/
theorem quadraticKummerHom_squareClassMap_commutes :
    (muTwoContinuousH1RestrictionMultiplicative L).comp
        (quadraticKummerHom ℚ) =
      (quadraticKummerHom L).comp
        (Rat.squareClassMap (algebraMap ℚ L)) := by
  apply DFunLike.ext _ _
  intro c
  exact quadraticKummerHom_squareClassMap L c

end RationalTamagawa

namespace RationalTamagawa

/-- Real restriction on continuous order-two characters. -/
noncomputable def rationalMuTwoContinuousH1ToReal :
    RationalMuTwoContinuousH1 →+ RealMuTwoContinuousH1 :=
  muTwoContinuousH1Restriction ℝ

/-- `p`-adic restriction on continuous order-two characters. -/
noncomputable def rationalMuTwoContinuousH1ToPadic
    (p : ℕ) [Fact p.Prime] :
    RationalMuTwoContinuousH1 →+ PadicMuTwoContinuousH1 p :=
  muTwoContinuousH1Restriction ℚ_[p]

/-- Continuous-cohomology localization kernel for the constant order-two
coefficient. -/
noncomputable def rationalMuTwoContinuousH1LocalGlobalKernel :
    AddSubgroup RationalMuTwoContinuousH1 where
  carrier := {χ | rationalMuTwoContinuousH1ToReal χ = 0 ∧
    ∀ (p : ℕ) [Fact p.Prime], rationalMuTwoContinuousH1ToPadic p χ = 0}
  zero_mem' := by simp
  add_mem' := by
    rintro χ ψ ⟨hχr, hχp⟩ ⟨hψr, hψp⟩
    constructor
    · simp [hχr, hψr]
    · intro p hp
      simp [hχp p, hψp p]
  neg_mem' := by
    rintro χ ⟨hχr, hχp⟩
    constructor
    · simp [hχr]
    · intro p hp
      simp [hχp p]

/-- A continuous rational order-two character trivial at the real place and
every `p`-adic place is globally trivial. -/
theorem rationalMuTwoContinuousH1_eq_zero_of_local_eq_zero
    (χ : RationalMuTwoContinuousH1)
    (hreal : rationalMuTwoContinuousH1ToReal χ = 0)
    (hpadic : ∀ (p : ℕ) [Fact p.Prime],
      rationalMuTwoContinuousH1ToPadic p χ = 0) :
    χ = 0 := by
  let c : Rat.SquareClass ℚ :=
    (quadraticKummerEquiv ℚ).symm (Multiplicative.ofAdd χ)
  have hc : quadraticKummerHom ℚ c = Multiplicative.ofAdd χ :=
    (quadraticKummerEquiv ℚ).apply_symm_apply (Multiplicative.ofAdd χ)
  have hcreal : Rat.rationalSquareClassToReal c = 1 := by
    change Rat.squareClassMap (algebraMap ℚ ℝ) c = 1
    apply quadraticKummerHom_injective ℝ
    change quadraticKummerHom ℝ (Rat.squareClassMap (algebraMap ℚ ℝ) c) =
      quadraticKummerHom ℝ 1
    rw [map_one, ← quadraticKummerHom_squareClassMap ℝ c, hc]
    change Multiplicative.ofAdd (rationalMuTwoContinuousH1ToReal χ) =
      Multiplicative.ofAdd 0
    rw [hreal]
  have hcpadic : ∀ (p : ℕ) [Fact p.Prime],
      Rat.rationalSquareClassToPadic p c = 1 := by
    intro p hp
    change Rat.squareClassMap (algebraMap ℚ ℚ_[p]) c = 1
    apply quadraticKummerHom_injective ℚ_[p]
    change quadraticKummerHom ℚ_[p]
        (Rat.squareClassMap (algebraMap ℚ ℚ_[p]) c) =
      quadraticKummerHom ℚ_[p] 1
    rw [map_one, ← quadraticKummerHom_squareClassMap ℚ_[p] c, hc]
    change Multiplicative.ofAdd (rationalMuTwoContinuousH1ToPadic p χ) =
      Multiplicative.ofAdd 0
    rw [hpadic p]
  have hc1 := Rat.rationalSquareClass_eq_one_of_local_eq_one c hcreal hcpadic
  rw [hc1, map_one] at hc
  exact congrArg Multiplicative.toAdd hc.symm

/-- The continuous `H1` localization kernel is literally bottom. -/
theorem rationalMuTwoContinuousH1LocalGlobalKernel_eq_bot :
    rationalMuTwoContinuousH1LocalGlobalKernel = ⊥ := by
  apply le_antisymm
  · intro χ hχ
    rw [AddSubgroup.mem_bot]
    exact rationalMuTwoContinuousH1_eq_zero_of_local_eq_zero χ hχ.1 hχ.2
  · exact bot_le

/-- Ono's continuous localization-kernel denominator `i^1` has order one in
the explicit constant order-two model. -/
theorem natCard_rationalMuTwoContinuousH1LocalGlobalKernel_eq_one :
    Nat.card rationalMuTwoContinuousH1LocalGlobalKernel = 1 := by
  rw [rationalMuTwoContinuousH1LocalGlobalKernel_eq_bot]
  simp

end RationalTamagawa
