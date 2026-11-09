import SMSFormula.SpecialOrthogonalFullAdelicProperDomainCover

/-!
# Strict uniqueness for the full-adelic proper transversal

The local stabilizer transversals make the rational factor in the finite
right-transversal decomposition unique.  This module exposes that pointwise
uniqueness for rational matrices and then lifts it through the concrete
real/finite splitting.
-/

noncomputable section

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

/-- Two rational special-orthogonal diagonal translates of the same
finite-adelic point cannot both lie in the proper transversal unless their
rational matrices agree. -/
theorem concreteProperFiniteTransversalFundamentalDomain_rationalDiagonal_unique
    (L : PositiveDefiniteIntegralLattice n) [Nonempty (Fin n)]
    (g : L.ConcreteFiniteAdelicSpecialOrthogonalGroup)
    (q₁ q₂ : L.rationalSpecialOrthogonalMatrixSubgroup)
    (hq₁ : L.rationalSpecialOrthogonalDiagonalHom q₁ * g ∈
      L.concreteProperFiniteTransversalFundamentalDomain)
    (hq₂ : L.rationalSpecialOrthogonalDiagonalHom q₂ * g ∈
      L.concreteProperFiniteTransversalFundamentalDomain) :
    q₁ = q₂ := by
  let slice : L.ConcreteProperRationalDoubleCosetSet →
      Set L.finiteSpecialOrthogonalLatticeStabilizerSubgroup := fun C =>
    L.concreteProperLocalRightStabilizerEmbeddingRealSlice (Quot.out C)
  have htrans : ∀ C : L.ConcreteProperRationalDoubleCosetSet,
      IsLeftCosetTransversal
        (L.concreteProperLocalRightStabilizerInFiniteSpecialOrthogonalLatticeStabilizer
          (Quot.out C))
        (slice C) := fun C =>
    L.concreteProperLocalRightStabilizerEmbeddingRealSlice_isLeftCosetTransversal
      (Quot.out C)
  have hlocal_unique : ∀ (C : L.ConcreteProperRationalDoubleCosetSet)
      (h₁ h₂ : L.finiteSpecialOrthogonalLatticeStabilizerSubgroup),
      h₁ ∈ slice C → h₂ ∈ slice C →
      (∃ gamma : L.rationalSpecialOrthogonalDiagonalSubgroup,
        (((h₂ * h₁⁻¹ : L.finiteSpecialOrthogonalLatticeStabilizerSubgroup) :
            L.ConcreteFiniteAdelicSpecialOrthogonalGroup) =
          (Quot.out C)⁻¹ *
            (gamma : L.ConcreteFiniteAdelicSpecialOrthogonalGroup) * Quot.out C)) →
      h₂ = h₁ := by
    intro C h₁ h₂ hh₁ hh₂ hstab
    apply (htrans C).unique h₁ h₂ hh₁ hh₂
    rw [L.mem_concreteProperLocalRightStabilizerInFiniteSpecialOrthogonalLatticeStabilizer_iff]
    apply (L.mem_concreteProperLocalRightStabilizerSubgroup_iff
      (Quot.out C)
      ((h₂ * h₁⁻¹ : L.finiteSpecialOrthogonalLatticeStabilizerSubgroup) :
        L.ConcreteFiniteAdelicSpecialOrthogonalGroup)).2
    refine ⟨(h₂ * h₁⁻¹).property, ?_⟩
    rcases hstab with ⟨gamma, hgamma⟩
    rcases gamma.2 with ⟨q, hq⟩
    refine ⟨q, ?_⟩
    rw [hq]
    exact hgamma
  have hgamma_unique :=
    finiteRightTransversalFundamentalDomain_gamma_unique_of_local_stabilizer_unique
      L.rationalSpecialOrthogonalDiagonalSubgroup
      L.finiteSpecialOrthogonalLatticeStabilizerSubgroup
      (fun C : L.ConcreteProperRationalDoubleCosetSet => Quot.out C)
      (fun C => Quot.out_eq C) slice hlocal_unique
  change L.rationalSpecialOrthogonalDiagonalHom q₁ * g ∈
      finiteRightTransversalFundamentalDomain
        L.finiteSpecialOrthogonalLatticeStabilizerSubgroup
        (fun C : L.ConcreteProperRationalDoubleCosetSet => Quot.out C)
        slice at hq₁
  change L.rationalSpecialOrthogonalDiagonalHom q₂ * g ∈
      finiteRightTransversalFundamentalDomain
        L.finiteSpecialOrthogonalLatticeStabilizerSubgroup
        (fun C : L.ConcreteProperRationalDoubleCosetSet => Quot.out C)
        slice at hq₂
  rcases (mem_finiteRightTransversalFundamentalDomain
      L.finiteSpecialOrthogonalLatticeStabilizerSubgroup
      (fun C : L.ConcreteProperRationalDoubleCosetSet => Quot.out C)
      slice _).1 hq₁ with
    ⟨C₁, h₁, hh₁, heq₁⟩
  rcases (mem_finiteRightTransversalFundamentalDomain
      L.finiteSpecialOrthogonalLatticeStabilizerSubgroup
      (fun C : L.ConcreteProperRationalDoubleCosetSet => Quot.out C)
      slice _).1 hq₂ with
    ⟨C₂, h₂, hh₂, heq₂⟩
  let gamma₁ : L.rationalSpecialOrthogonalDiagonalSubgroup :=
    ⟨L.rationalSpecialOrthogonalDiagonalHom q₁, ⟨q₁, rfl⟩⟩
  let gamma₂ : L.rationalSpecialOrthogonalDiagonalSubgroup :=
    ⟨L.rationalSpecialOrthogonalDiagonalHom q₂, ⟨q₂, rfl⟩⟩
  have hgamma : gamma₁ = gamma₂ := hgamma_unique
    g gamma₁ gamma₂ C₁ C₂ h₁ h₂ hh₁ hh₂
    (by simpa [gamma₁] using heq₁)
    (by simpa [gamma₂] using heq₂)
  have hdiag :
      L.rationalSpecialOrthogonalDiagonalHom q₁ =
        L.rationalSpecialOrthogonalDiagonalHom q₂ :=
    congrArg Subtype.val hgamma
  apply Subtype.ext
  apply L.rationalOrthogonalDiagonalHom_injective
  exact congrArg Subtype.val hdiag

/-- Two rational full-adelic diagonal translates of the same point cannot
both lie in the lifted proper domain unless their rational matrices
agree. -/
theorem concreteFullAdelicProperTransversal_rationalDiagonal_unique
    (L : PositiveDefiniteIntegralLattice n) [Nonempty (Fin n)]
    (g : L.ConcreteFullAdelicSpecialOrthogonalGroup)
    (q₁ q₂ : L.rationalSpecialOrthogonalMatrixSubgroup)
    (hq₁ : L.rationalSpecialOrthogonalFullAdelicDiagonalHom q₁ * g ∈
      L.concreteFullAdelicProperTransversal)
    (hq₂ : L.rationalSpecialOrthogonalFullAdelicDiagonalHom q₂ * g ∈
      L.concreteFullAdelicProperTransversal) :
    q₁ = q₂ := by
  apply L.concreteProperFiniteTransversalFundamentalDomain_rationalDiagonal_unique
    (g := (L.fullAdelicSpecialOrthogonalGroupRealFiniteContinuousEquiv g).2)
  · have hfinite :=
      (L.mem_concreteFullAdelicProperTransversal_iff
        (L.rationalSpecialOrthogonalFullAdelicDiagonalHom q₁ * g)).1 hq₁
    simpa using hfinite
  · have hfinite :=
      (L.mem_concreteFullAdelicProperTransversal_iff
        (L.rationalSpecialOrthogonalFullAdelicDiagonalHom q₂ * g)).1 hq₂
    simpa using hfinite

end PositiveDefiniteIntegralLattice
