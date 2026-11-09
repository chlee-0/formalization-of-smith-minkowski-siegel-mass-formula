import SMSFormula.SpecialOrthogonalRealCongruencePointCenteredDensity

/-!
# Generic ambient comparison of two transported charts

This file isolates the set-theoretic and topological algebra of two partial
homeomorphisms related by equivalences of their source and target carriers.
It prevents concrete dependent chart proofs from being re-expanded in every
inverse and image argument.
-/

noncomputable section

open MeasureTheory

namespace PositiveDefiniteIntegralLattice

variable {G H E E' : Type*}
  [TopologicalSpace G] [TopologicalSpace H]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E']

/-- Source coordinates where both transported charts are defined. -/
def realCrossChartAmbientSource
    (I : OpenPartialHomeomorph G E) (J : OpenPartialHomeomorph H E')
    (C : G ≃ₜ H) : Set E :=
  I.target ∩ (fun x => C (I.symm x)) ⁻¹' J.source

/-- Target coordinates, pulled back to the first tangent carrier. -/
def realCrossChartAmbientTarget
    (I : OpenPartialHomeomorph G E) (J : OpenPartialHomeomorph H E')
    (C : G ≃ₜ H) (e : E ≃L[ℝ] E') : Set E :=
  e ⁻¹' (J.target ∩ (fun z => C.symm (J.symm z)) ⁻¹' I.source)

/-- The common group points represented by both charts. -/
def realCrossChartAmbientGroupOverlap
    (I : OpenPartialHomeomorph G E) (J : OpenPartialHomeomorph H E')
    (C : G ≃ₜ H) : Set H :=
  C.symm ⁻¹' I.source ∩ J.source

/-- The explicit second-chart coordinate range of the ambient target. -/
def realCrossChartAmbientTargetRange
    (I : OpenPartialHomeomorph G E) (J : OpenPartialHomeomorph H E')
    (C : G ≃ₜ H) : Set E' :=
  J.target ∩ (fun z => C.symm (J.symm z)) ⁻¹' I.source

/-- The coordinate transition, kept on the first tangent carrier. -/
def realCrossChartAmbientTransition
    (I : OpenPartialHomeomorph G E) (J : OpenPartialHomeomorph H E')
    (C : G ≃ₜ H) (e : E ≃L[ℝ] E') (x : E) : E :=
  e.symm (J (C (I.symm x)))

theorem realCrossChartAmbientTransition_apply
    (I : OpenPartialHomeomorph G E) (J : OpenPartialHomeomorph H E')
    (C : G ≃ₜ H) (e : E ≃L[ℝ] E') (x : E) :
    e (realCrossChartAmbientTransition I J C e x) = J (C (I.symm x)) :=
  e.apply_symm_apply _

/-- The pointwise inverse coordinate transition. -/
def realCrossChartAmbientTransitionInv
    (I : OpenPartialHomeomorph G E) (J : OpenPartialHomeomorph H E')
    (C : G ≃ₜ H) (e : E ≃L[ℝ] E') (z : E) : E :=
  I (C.symm (J.symm (e z)))

omit [NormedSpace ℝ E] [NormedSpace ℝ E'] in
/-- The generic ambient source is open. -/
theorem isOpen_realCrossChartAmbientSource
    (I : OpenPartialHomeomorph G E) (J : OpenPartialHomeomorph H E')
    (C : G ≃ₜ H) :
    IsOpen (realCrossChartAmbientSource I J C) := by
  change IsOpen (I.target ∩ (fun x => C (I.symm x)) ⁻¹' J.source)
  exact
    (C.continuous.comp_continuousOn I.symm.continuousOn).isOpen_inter_preimage
      I.open_target J.open_source

/-- The generic ambient target is open. -/
theorem isOpen_realCrossChartAmbientTarget
    (I : OpenPartialHomeomorph G E) (J : OpenPartialHomeomorph H E')
    (C : G ≃ₜ H) (e : E ≃L[ℝ] E') :
    IsOpen (realCrossChartAmbientTarget I J C e) := by
  change IsOpen
    (e ⁻¹' (J.target ∩ (fun z => C.symm (J.symm z)) ⁻¹' I.source))
  have hopen :
      IsOpen (J.target ∩ (fun z => C.symm (J.symm z)) ⁻¹' I.source) :=
    (C.symm.continuous.comp_continuousOn
      J.symm.continuousOn).isOpen_inter_preimage
        J.open_target I.open_source
  exact hopen.preimage e.continuous

omit [NormedSpace ℝ E] [NormedSpace ℝ E'] in
/-- The generic common group overlap is open. -/
theorem isOpen_realCrossChartAmbientGroupOverlap
    (I : OpenPartialHomeomorph G E) (J : OpenPartialHomeomorph H E')
    (C : G ≃ₜ H) :
    IsOpen (realCrossChartAmbientGroupOverlap I J C) :=
  (I.open_source.preimage C.symm.continuous).inter J.open_source

omit [NormedSpace ℝ E] [NormedSpace ℝ E'] in
/-- The explicit second-chart coordinate range is open. -/
theorem isOpen_realCrossChartAmbientTargetRange
    (I : OpenPartialHomeomorph G E) (J : OpenPartialHomeomorph H E')
    (C : G ≃ₜ H) :
    IsOpen (realCrossChartAmbientTargetRange I J C) :=
  (C.symm.continuous.comp_continuousOn
    J.symm.continuousOn).isOpen_inter_preimage
      J.open_target I.open_source

/-- Source ambient coordinates are homeomorphic to the common group overlap. -/
def realCrossChartAmbientSourceToGroup
    (I : OpenPartialHomeomorph G E) (J : OpenPartialHomeomorph H E')
    (C : G ≃ₜ H) :
    realCrossChartAmbientSource I J C ≃ₜ
      realCrossChartAmbientGroupOverlap I J C where
  toFun x := ⟨C (I.symm x.1), by
    change C.symm (C (I.symm x.1)) ∈ I.source ∧
      C (I.symm x.1) ∈ J.source
    exact ⟨by simpa using I.symm.map_source x.2.1, x.2.2⟩⟩
  invFun q := ⟨I (C.symm q.1), by
    change I (C.symm q.1) ∈ I.target ∧
      C (I.symm (I (C.symm q.1))) ∈ J.source
    exact ⟨I.map_source q.2.1, by
      rw [I.left_inv q.2.1, C.apply_symm_apply]
      exact q.2.2⟩⟩
  left_inv x := by
    apply Subtype.ext
    change I (C.symm (C (I.symm x.1))) = x.1
    rw [C.symm_apply_apply, I.right_inv x.2.1]
  right_inv q := by
    apply Subtype.ext
    change C (I.symm (I (C.symm q.1))) = q.1
    rw [I.left_inv q.2.1, C.apply_symm_apply]
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact C.continuous.comp
      (I.symm.continuousOn.comp_continuous continuous_subtype_val
        (fun x => x.2.1))
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact I.continuousOn.comp_continuous
      (C.symm.continuous.comp continuous_subtype_val)
      (fun q => q.2.1)

/-- Explicit second-chart coordinates are homeomorphic to the common group
overlap. -/
def realCrossChartAmbientTargetRangeToGroup
    (I : OpenPartialHomeomorph G E) (J : OpenPartialHomeomorph H E')
    (C : G ≃ₜ H) :
    realCrossChartAmbientTargetRange I J C ≃ₜ
      realCrossChartAmbientGroupOverlap I J C where
  toFun z := ⟨J.symm z.1, by
    change C.symm (J.symm z.1) ∈ I.source ∧ J.symm z.1 ∈ J.source
    exact ⟨z.2.2, J.symm.map_source z.2.1⟩⟩
  invFun q := ⟨J q.1, by
    change J q.1 ∈ J.target ∧ C.symm (J.symm (J q.1)) ∈ I.source
    exact ⟨J.map_source q.2.2, by
      rw [J.left_inv q.2.2]
      exact q.2.1⟩⟩
  left_inv z := by
    apply Subtype.ext
    exact J.right_inv z.2.1
  right_inv q := by
    apply Subtype.ext
    exact J.left_inv q.2.2
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact J.symm.continuousOn.comp_continuous continuous_subtype_val
      (fun z => z.2.1)
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact J.continuousOn.comp_continuous continuous_subtype_val
      (fun q => q.2.2)

/-- Tangent equivalence identifies the pulled-back target with its explicit
second-chart coordinate range. -/
def realCrossChartAmbientTargetToRange
    (I : OpenPartialHomeomorph G E) (J : OpenPartialHomeomorph H E')
    (C : G ≃ₜ H) (e : E ≃L[ℝ] E') :
    realCrossChartAmbientTarget I J C e ≃ₜ
      realCrossChartAmbientTargetRange I J C where
  toFun z := ⟨e z.1, z.2⟩
  invFun w := ⟨e.symm w.1, by
    change e (e.symm w.1) ∈ realCrossChartAmbientTargetRange I J C
    simpa using w.2⟩
  left_inv z := by
    apply Subtype.ext
    exact e.symm_apply_apply z.1
  right_inv w := by
    apply Subtype.ext
    exact e.apply_symm_apply w.1
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact e.continuous.comp continuous_subtype_val
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact e.symm.continuous.comp continuous_subtype_val

/-- The common-group identification gives the coordinate transition directly
between the two ambient overlap subtypes. -/
def realCrossChartAmbientSourceToTargetRange
    (I : OpenPartialHomeomorph G E) (J : OpenPartialHomeomorph H E')
    (C : G ≃ₜ H) :
    realCrossChartAmbientSource I J C ≃ₜ
      realCrossChartAmbientTargetRange I J C :=
  (realCrossChartAmbientSourceToGroup I J C).trans
    (realCrossChartAmbientTargetRangeToGroup I J C).symm

/-- The source-to-range homeomorphism is tangent congruence after the
fixed-carrier transition. -/
theorem coe_realCrossChartAmbientSourceToTargetRange
    (I : OpenPartialHomeomorph G E) (J : OpenPartialHomeomorph H E')
    (C : G ≃ₜ H) (e : E ≃L[ℝ] E')
    (x : realCrossChartAmbientSource I J C) :
    (realCrossChartAmbientSourceToTargetRange I J C x).1 =
      e (realCrossChartAmbientTransition I J C e x.1) := by
  change J (C (I.symm x.1)) =
    e (e.symm (J (C (I.symm x.1))))
  rw [e.apply_symm_apply]

omit [NormedSpace ℝ E] [NormedSpace ℝ E'] in
/-- Both coordinate overlap homeomorphisms represent the same common group
point. -/
theorem realCrossChartAmbientTargetRangeToGroup_sourceToTargetRange
    (I : OpenPartialHomeomorph G E) (J : OpenPartialHomeomorph H E')
    (C : G ≃ₜ H)
    (x : realCrossChartAmbientSource I J C) :
    realCrossChartAmbientTargetRangeToGroup I J C
        (realCrossChartAmbientSourceToTargetRange I J C x) =
      realCrossChartAmbientSourceToGroup I J C x := by
  change
    realCrossChartAmbientTargetRangeToGroup I J C
        ((realCrossChartAmbientTargetRangeToGroup I J C).symm
          (realCrossChartAmbientSourceToGroup I J C x)) =
      realCrossChartAmbientSourceToGroup I J C x
  exact (realCrossChartAmbientTargetRangeToGroup I J C).apply_symm_apply _

/-- The generic transition maps source to target. -/
theorem mapsTo_realCrossChartAmbientTransition
    (I : OpenPartialHomeomorph G E) (J : OpenPartialHomeomorph H E')
    (C : G ≃ₜ H) (e : E ≃L[ℝ] E') :
    Set.MapsTo
      (realCrossChartAmbientTransition I J C e)
      (realCrossChartAmbientSource I J C)
      (realCrossChartAmbientTarget I J C e) := by
  intro x hx
  change x ∈ I.target ∩ (fun x => C (I.symm x)) ⁻¹' J.source at hx
  change
    e (e.symm (J (C (I.symm x)))) ∈
      J.target ∩ (fun z => C.symm (J.symm z)) ⁻¹' I.source
  rw [e.apply_symm_apply]
  constructor
  · exact J.map_source hx.2
  · change C.symm (J.symm (J (C (I.symm x)))) ∈ I.source
    rw [J.left_inv hx.2, C.symm_apply_apply]
    exact I.symm.map_source hx.1

/-- Membership in the generic ambient target includes membership in the
second chart target after applying the tangent equivalence. -/
theorem mem_target_of_mem_realCrossChartAmbientTarget
    (I : OpenPartialHomeomorph G E) (J : OpenPartialHomeomorph H E')
    (C : G ≃ₜ H) (e : E ≃L[ℝ] E') {z : E}
    (hz : z ∈ realCrossChartAmbientTarget I J C e) :
    e z ∈ J.target := by
  change e z ∈ J.target ∩
    (fun w => C.symm (J.symm w)) ⁻¹' I.source at hz
  exact hz.1

/-- Applying the tangent equivalence to the generic ambient target gives the
explicit second-chart target intersection. -/
theorem image_realCrossChartAmbientTarget
    (I : OpenPartialHomeomorph G E) (J : OpenPartialHomeomorph H E')
    (C : G ≃ₜ H) (e : E ≃L[ℝ] E') :
    e '' realCrossChartAmbientTarget I J C e =
      J.target ∩ (fun w => C.symm (J.symm w)) ⁻¹' I.source := by
  apply Set.Subset.antisymm
  · rintro w ⟨z, hz, rfl⟩
    exact hz
  · intro w hw
    refine ⟨e.symm w, ?_, e.apply_symm_apply w⟩
    simpa only [realCrossChartAmbientTarget, Set.mem_preimage,
      e.apply_symm_apply] using hw

/-- The generic inverse maps target to source. -/
theorem mapsTo_realCrossChartAmbientTransitionInv
    (I : OpenPartialHomeomorph G E) (J : OpenPartialHomeomorph H E')
    (C : G ≃ₜ H) (e : E ≃L[ℝ] E') :
    Set.MapsTo
      (realCrossChartAmbientTransitionInv I J C e)
      (realCrossChartAmbientTarget I J C e)
      (realCrossChartAmbientSource I J C) := by
  intro z hz
  change e z ∈ J.target ∩ (fun z => C.symm (J.symm z)) ⁻¹' I.source at hz
  change
    I (C.symm (J.symm (e z))) ∈ I.target ∩
      (fun x => C (I.symm x)) ⁻¹' J.source
  constructor
  · exact I.map_source hz.2
  · change C (I.symm (I (C.symm (J.symm (e z))))) ∈ J.source
    rw [I.left_inv hz.2, C.apply_symm_apply]
    exact J.symm.map_source hz.1

/-- The generic inverse is a left inverse on the source. -/
theorem leftInverseOn_realCrossChartAmbientTransition
    (I : OpenPartialHomeomorph G E) (J : OpenPartialHomeomorph H E')
    (C : G ≃ₜ H) (e : E ≃L[ℝ] E') :
    Set.LeftInvOn
      (realCrossChartAmbientTransitionInv I J C e)
      (realCrossChartAmbientTransition I J C e)
      (realCrossChartAmbientSource I J C) := by
  intro x hx
  change x ∈ I.target ∩ (fun x => C (I.symm x)) ⁻¹' J.source at hx
  change
    I (C.symm (J.symm (e (e.symm (J (C (I.symm x))))))) = x
  rw [e.apply_symm_apply, J.left_inv hx.2, C.symm_apply_apply,
    I.right_inv hx.1]

/-- The generic inverse is a right inverse on the target. -/
theorem rightInverseOn_realCrossChartAmbientTransition
    (I : OpenPartialHomeomorph G E) (J : OpenPartialHomeomorph H E')
    (C : G ≃ₜ H) (e : E ≃L[ℝ] E') :
    Set.RightInvOn
      (realCrossChartAmbientTransitionInv I J C e)
      (realCrossChartAmbientTransition I J C e)
      (realCrossChartAmbientTarget I J C e) := by
  intro z hz
  change e z ∈ J.target ∩ (fun z => C.symm (J.symm z)) ⁻¹' I.source at hz
  change
    e.symm
      (J (C (I.symm (I (C.symm (J.symm (e z))))))) = z
  apply e.injective
  rw [e.apply_symm_apply, I.left_inv hz.2, C.apply_symm_apply,
    J.right_inv hz.1]

/-- The generic transition is injective on its source. -/
theorem injOn_realCrossChartAmbientTransition
    (I : OpenPartialHomeomorph G E) (J : OpenPartialHomeomorph H E')
    (C : G ≃ₜ H) (e : E ≃L[ℝ] E') :
    Set.InjOn
      (realCrossChartAmbientTransition I J C e)
      (realCrossChartAmbientSource I J C) :=
  (leftInverseOn_realCrossChartAmbientTransition I J C e).injOn

/-- The image of the generic source is exactly the generic target. -/
theorem image_realCrossChartAmbientSource
    (I : OpenPartialHomeomorph G E) (J : OpenPartialHomeomorph H E')
    (C : G ≃ₜ H) (e : E ≃L[ℝ] E') :
    realCrossChartAmbientTransition I J C e ''
        realCrossChartAmbientSource I J C =
      realCrossChartAmbientTarget I J C e := by
  apply Set.Subset.antisymm
  · rintro z ⟨x, hx, rfl⟩
    exact mapsTo_realCrossChartAmbientTransition I J C e hx
  · intro z hz
    exact ⟨realCrossChartAmbientTransitionInv I J C e z,
      mapsTo_realCrossChartAmbientTransitionInv I J C e hz,
      rightInverseOn_realCrossChartAmbientTransition I J C e hz⟩

end PositiveDefiniteIntegralLattice
