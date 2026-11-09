import SMSFormula.AdelicFinitePresentation
import SMSFormula.LocalOrientationSource

/-!
# Oriented local comparisons

This module corrects the determinant of an ordinary local genus comparison
matrix using the integral local reflection theorem.
-/

noncomputable section

namespace PositiveDefiniteIntegralLattice

variable {n : ℕ}

open scoped Matrix

/-- A local integral comparison can be chosen so that, after a fixed rational
comparison, its determinant over `ℚ_p` is one.

The required determinant-`-1` integral symmetry is constructed internally in
`LocalOrthogonalHaar.lean`. -/
theorem exists_orientedPadicIntegralMatrixUnit_of_isLocallyIsometricAt
    (L M : PositiveDefiniteIntegralLattice n) [Nonempty (Fin n)]
    (p : ℕ) [Fact (Nat.Prime p)]
    (h : L.IsLocallyIsometricAt M p)
    (P : GL (Fin n) ℚ)
    (hP : P.1ᵀ * L.rationalFormMatrix * P.1 = M.rationalFormMatrix) :
    ∃ U : GL (Fin n) ℤ_[p],
      U.1ᵀ * M.pairingMatrix_padic p * U.1 = L.pairingMatrix_padic p ∧
      (let Pp : GL (Fin n) ℚ_[p] :=
        Matrix.GeneralLinearGroup.map (algebraMap ℚ ℚ_[p]) P
       let Up : GL (Fin n) ℚ_[p] :=
        Matrix.GeneralLinearGroup.map PadicInt.Coe.ringHom U
       (Pp * Up).1.det = 1) := by
  classical
  rcases h with ⟨A, hAunit, hAform⟩
  let U₀ : GL (Fin n) ℤ_[p] := hAunit.unit
  have hU₀form : U₀.1ᵀ * M.pairingMatrix_padic p * U₀.1 =
      L.pairingMatrix_padic p := by
    simpa [U₀, IsUnit.unit_spec] using hAform
  obtain ⟨R, hRform, hRdet⟩ :=
    L.exists_padicIntegralOrthogonal_det_neg_one_of_nonempty p
  let Pp : GL (Fin n) ℚ_[p] :=
    Matrix.GeneralLinearGroup.map (algebraMap ℚ ℚ_[p]) P
  let U₀p : GL (Fin n) ℚ_[p] :=
    Matrix.GeneralLinearGroup.map PadicInt.Coe.ringHom U₀
  let Rp : GL (Fin n) ℚ_[p] :=
    Matrix.GeneralLinearGroup.map PadicInt.Coe.ringHom R
  by_cases hdet : (Pp * U₀p).1.det = 1
  · exact ⟨U₀, hU₀form, hdet⟩
  · refine ⟨U₀ * R, ?_, ?_⟩
    · change (U₀.1 * R.1)ᵀ * M.pairingMatrix_padic p * (U₀.1 * R.1) =
        L.pairingMatrix_padic p
      rw [Matrix.transpose_mul]
      calc
        (R.1ᵀ * U₀.1ᵀ) * M.pairingMatrix_padic p * (U₀.1 * R.1) =
            R.1ᵀ * (U₀.1ᵀ * M.pairingMatrix_padic p * U₀.1) * R.1 := by
          noncomm_ring
        _ = R.1ᵀ * L.pairingMatrix_padic p * R.1 := by rw [hU₀form]
        _ = L.pairingMatrix_padic p := hRform
    · have hPfield :
          Pp.1ᵀ * L.pairingMatrix_padicField p * Pp.1 =
            M.pairingMatrix_padicField p := by
        have hmap := congrArg
          (fun B : Matrix (Fin n) (Fin n) ℚ ↦
            B.map (algebraMap ℚ ℚ_[p])) hP
        simpa [Pp, pairingMatrix_padicField, pairingMatrix_padic,
          rationalFormMatrix, Matrix.map_mul, Matrix.transpose_map] using hmap
      have hU₀field :
          U₀p.1ᵀ * M.pairingMatrix_padicField p * U₀p.1 =
            L.pairingMatrix_padicField p := by
        have hmap := congrArg
          (fun B : Matrix (Fin n) (Fin n) ℤ_[p] ↦
            B.map PadicInt.Coe.ringHom) hU₀form
        simpa [U₀p, pairingMatrix_padicField, Matrix.map_mul,
          Matrix.transpose_map] using hmap
      have hgform :
          (Pp.1 * U₀p.1)ᵀ * L.pairingMatrix_padicField p *
              (Pp.1 * U₀p.1) = L.pairingMatrix_padicField p := by
        rw [Matrix.transpose_mul]
        calc
          (U₀p.1ᵀ * Pp.1ᵀ) * L.pairingMatrix_padicField p *
                (Pp.1 * U₀p.1) =
              U₀p.1ᵀ *
                (Pp.1ᵀ * L.pairingMatrix_padicField p * Pp.1) * U₀p.1 := by
            noncomm_ring
          _ = L.pairingMatrix_padicField p := by rw [hPfield, hU₀field]
      have hLdet : (L.pairingMatrix_padicField p).det ≠ 0 := by
        rw [L.pairingMatrix_padicField_det p]
        exact_mod_cast (ne_of_gt L.pairingDeterminant_pos)
      have hdetEq := congrArg Matrix.det hgform
      simp only [Matrix.det_mul, Matrix.det_transpose] at hdetEq
      have hsq : (Pp.1.det * U₀p.1.det) * (Pp.1.det * U₀p.1.det) = 1 := by
        apply mul_right_cancel₀ hLdet
        calc
          ((Pp.1.det * U₀p.1.det) * (Pp.1.det * U₀p.1.det)) *
                (L.pairingMatrix_padicField p).det =
              (Pp.1.det * U₀p.1.det) * (L.pairingMatrix_padicField p).det *
                (Pp.1.det * U₀p.1.det) := by ring
          _ = (L.pairingMatrix_padicField p).det := hdetEq
          _ = 1 * (L.pairingMatrix_padicField p).det := by ring
      have hfactor :
          (Pp.1.det * U₀p.1.det - 1) *
              (Pp.1.det * U₀p.1.det + 1) = 0 := by
        linear_combination hsq
      have hsign : Pp.1.det * U₀p.1.det = 1 ∨
          Pp.1.det * U₀p.1.det = -1 := by
        rcases mul_eq_zero.mp hfactor with hneg | hpos
        · left
          linear_combination hneg
        · right
          linear_combination hpos
      have hdet' : Pp.1.det * U₀p.1.det ≠ 1 := by
        simpa [Matrix.det_mul] using hdet
      have hgneg : Pp.1.det * U₀p.1.det = -1 :=
        hsign.resolve_left hdet'
      change
        (Pp * Matrix.GeneralLinearGroup.map PadicInt.Coe.ringHom (U₀ * R)).1.det = 1
      rw [map_mul]
      change (Pp.1 * (U₀p.1 * Rp.1)).det = 1
      rw [Matrix.det_mul, Matrix.det_mul]
      have hRpdet : Rp.1.det = -1 := by
        simpa [Rp, hRdet] using
          (RingHom.map_det PadicInt.Coe.ringHom R.1).symm
      rw [← mul_assoc, hgneg, hRpdet]
      ring

/-- Reindex a chosen determinant-corrected `p`-adic integral comparison by a
height-one prime of `ℤ`. -/
noncomputable def orientedSameGenusHeightOneLocalIntegralMatrixUnit
    (L M : PositiveDefiniteIntegralLattice n) [Nonempty (Fin n)]
    (h : L.IsSameGenus M)
    (P : GL (Fin n) ℚ)
    (hP : P.1ᵀ * L.rationalFormMatrix * P.1 = M.rationalFormMatrix)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    GL (Fin n) (v.adicCompletionIntegers ℚ) := by
  let p := (Rat.HeightOneSpectrum.primesEquiv v : ℕ)
  letI : Fact (Nat.Prime p) :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv v).property⟩
  let A := Classical.choose
    (L.exists_orientedPadicIntegralMatrixUnit_of_isLocallyIsometricAt
      M p (h.1 p) P hP)
  let algA : Algebra ℤ (v.adicCompletionIntegers ℚ) :=
    Ring.toIntAlgebra (v.adicCompletionIntegers ℚ)
  let algB : Algebra ℤ ℤ_[p] := Ring.toIntAlgebra ℤ_[p]
  let e : @ContinuousAlgEquiv ℤ (v.adicCompletionIntegers ℚ) ℤ_[p]
      _ _ _ _ _ algA algB :=
    Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv v
  let ae := @ContinuousAlgEquiv.toAlgEquiv ℤ
    (v.adicCompletionIntegers ℚ) ℤ_[p] _ _ _ _ _ algA algB e
  let er := @AlgEquiv.toRingEquiv ℤ (v.adicCompletionIntegers ℚ) ℤ_[p]
    _ _ _ algA algB ae
  exact (Units.mapEquiv er.mapMatrix.toMulEquiv).symm A

theorem orientedSameGenusHeightOneLocalIntegralMatrixUnit_form_eq
    (L M : PositiveDefiniteIntegralLattice n) [Nonempty (Fin n)]
    (h : L.IsSameGenus M)
    (P : GL (Fin n) ℚ)
    (hP : P.1ᵀ * L.rationalFormMatrix * P.1 = M.rationalFormMatrix)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    let Uv : GL (Fin n) (v.adicCompletion ℚ) :=
      Matrix.GeneralLinearGroup.map
        (v.adicCompletionIntegers ℚ).subtype
        (orientedSameGenusHeightOneLocalIntegralMatrixUnit L M h P hP v)
    Uv.1ᵀ * M.pairingMatrix.map (algebraMap ℤ (v.adicCompletion ℚ)) * Uv.1 =
      L.pairingMatrix.map (algebraMap ℤ (v.adicCompletion ℚ)) := by
  let p := (Rat.HeightOneSpectrum.primesEquiv v : ℕ)
  letI : Fact (Nat.Prime p) :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv v).property⟩
  let A := Classical.choose
    (L.exists_orientedPadicIntegralMatrixUnit_of_isLocallyIsometricAt
      M p (h.1 p) P hP)
  have hAform : A.1ᵀ * M.pairingMatrix_padic p * A.1 = L.pairingMatrix_padic p :=
    (Classical.choose_spec
      (L.exists_orientedPadicIntegralMatrixUnit_of_isLocallyIsometricAt
        M p (h.1 p) P hP)).1
  let algA : Algebra ℤ (v.adicCompletionIntegers ℚ) :=
    Ring.toIntAlgebra (v.adicCompletionIntegers ℚ)
  let algB : Algebra ℤ ℤ_[p] := Ring.toIntAlgebra ℤ_[p]
  let e : @ContinuousAlgEquiv ℤ (v.adicCompletionIntegers ℚ) ℤ_[p]
      _ _ _ _ _ algA algB :=
    Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv v
  let ae := @ContinuousAlgEquiv.toAlgEquiv ℤ
    (v.adicCompletionIntegers ℚ) ℤ_[p] _ _ _ _ _ algA algB e
  let er := @AlgEquiv.toRingEquiv ℤ (v.adicCompletionIntegers ℚ) ℤ_[p]
    _ _ _ algA algB ae
  have hUe :
      (orientedSameGenusHeightOneLocalIntegralMatrixUnit L M h P hP v).1.map
          (Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv v) = A := by
    change er.mapMatrix
      ((Units.mapEquiv er.mapMatrix.toMulEquiv).symm A).1 = A.1
    exact congrArg Units.val
      ((Units.mapEquiv er.mapMatrix.toMulEquiv).apply_symm_apply A)
  let ev := Rat.HeightOneSpectrum.adicCompletion.padicEquiv v
  have hUv :
      (Matrix.GeneralLinearGroup.map
          (v.adicCompletionIntegers ℚ).subtype
          (orientedSameGenusHeightOneLocalIntegralMatrixUnit
            L M h P hP v)).1.map ev.toRingEquiv.toRingHom =
        A.1.map PadicInt.Coe.ringHom := by
    ext i j
    have hij := congr_fun (congr_fun hUe i) j
    exact congrArg Subtype.val hij
  have hMmap :
      (M.pairingMatrix.map (algebraMap ℤ (v.adicCompletion ℚ))).map
          ev.toRingEquiv.toRingHom =
        (M.pairingMatrix_padic p).map PadicInt.Coe.ringHom := by
    ext i j
    simp [pairingMatrix_padic, p, ev]
  have hLmap :
      (L.pairingMatrix.map (algebraMap ℤ (v.adicCompletion ℚ))).map
          ev.toRingEquiv.toRingHom =
        (L.pairingMatrix_padic p).map PadicInt.Coe.ringHom := by
    ext i j
    simp [pairingMatrix_padic, p, ev]
  apply Matrix.map_injective (f := ev.toRingEquiv.toRingHom) ev.injective
  change
    (((Matrix.GeneralLinearGroup.map
        (v.adicCompletionIntegers ℚ).subtype
        (orientedSameGenusHeightOneLocalIntegralMatrixUnit
          L M h P hP v)).1ᵀ *
          M.pairingMatrix.map (algebraMap ℤ (v.adicCompletion ℚ)) *
        (Matrix.GeneralLinearGroup.map
          (v.adicCompletionIntegers ℚ).subtype
          (orientedSameGenusHeightOneLocalIntegralMatrixUnit
            L M h P hP v)).1).map ev.toRingEquiv.toRingHom) =
      (L.pairingMatrix.map (algebraMap ℤ (v.adicCompletion ℚ))).map
        ev.toRingEquiv.toRingHom
  rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, hUv, hMmap, hLmap]
  have hmap := congrArg
    (fun X : Matrix (Fin n) (Fin n) ℤ_[p] ↦ X.map PadicInt.Coe.ringHom)
    hAform
  simpa [Matrix.map_mul, Matrix.transpose_map] using hmap

theorem orientedSameGenusHeightOneLocalIntegralMatrixUnit_det_eq_one
    (L M : PositiveDefiniteIntegralLattice n) [Nonempty (Fin n)]
    (h : L.IsSameGenus M)
    (P : GL (Fin n) ℚ)
    (hP : P.1ᵀ * L.rationalFormMatrix * P.1 = M.rationalFormMatrix)
    (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    let Pv : GL (Fin n) (v.adicCompletion ℚ) :=
      Matrix.GeneralLinearGroup.map (algebraMap ℚ (v.adicCompletion ℚ)) P
    let Uv : GL (Fin n) (v.adicCompletion ℚ) :=
      Matrix.GeneralLinearGroup.map
        (v.adicCompletionIntegers ℚ).subtype
        (orientedSameGenusHeightOneLocalIntegralMatrixUnit L M h P hP v)
    (Pv * Uv).1.det = 1 := by
  let p := (Rat.HeightOneSpectrum.primesEquiv v : ℕ)
  letI : Fact (Nat.Prime p) :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv v).property⟩
  let A := Classical.choose
    (L.exists_orientedPadicIntegralMatrixUnit_of_isLocallyIsometricAt
      M p (h.1 p) P hP)
  have hAdet :
      (let Pp : GL (Fin n) ℚ_[p] :=
        Matrix.GeneralLinearGroup.map (algebraMap ℚ ℚ_[p]) P
       let Ap : GL (Fin n) ℚ_[p] :=
        Matrix.GeneralLinearGroup.map PadicInt.Coe.ringHom A
       (Pp * Ap).1.det = 1) :=
    (Classical.choose_spec
      (L.exists_orientedPadicIntegralMatrixUnit_of_isLocallyIsometricAt
        M p (h.1 p) P hP)).2
  let algA : Algebra ℤ (v.adicCompletionIntegers ℚ) :=
    Ring.toIntAlgebra (v.adicCompletionIntegers ℚ)
  let algB : Algebra ℤ ℤ_[p] := Ring.toIntAlgebra ℤ_[p]
  let e : @ContinuousAlgEquiv ℤ (v.adicCompletionIntegers ℚ) ℤ_[p]
      _ _ _ _ _ algA algB :=
    Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv v
  let ae := @ContinuousAlgEquiv.toAlgEquiv ℤ
    (v.adicCompletionIntegers ℚ) ℤ_[p] _ _ _ _ _ algA algB e
  let er := @AlgEquiv.toRingEquiv ℤ (v.adicCompletionIntegers ℚ) ℤ_[p]
    _ _ _ algA algB ae
  have hUe :
      (orientedSameGenusHeightOneLocalIntegralMatrixUnit L M h P hP v).1.map
          (Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv v) = A := by
    change er.mapMatrix
      ((Units.mapEquiv er.mapMatrix.toMulEquiv).symm A).1 = A.1
    exact congrArg Units.val
      ((Units.mapEquiv er.mapMatrix.toMulEquiv).apply_symm_apply A)
  let ev := Rat.HeightOneSpectrum.adicCompletion.padicEquiv v
  have hUv :
      (Matrix.GeneralLinearGroup.map
          (v.adicCompletionIntegers ℚ).subtype
          (orientedSameGenusHeightOneLocalIntegralMatrixUnit
            L M h P hP v)).1.map ev.toRingEquiv.toRingHom =
        A.1.map PadicInt.Coe.ringHom := by
    ext i j
    have hij := congr_fun (congr_fun hUe i) j
    exact congrArg Subtype.val hij
  have hPv :
      (Matrix.GeneralLinearGroup.map
          (algebraMap ℚ (v.adicCompletion ℚ)) P).1.map
            ev.toRingEquiv.toRingHom =
        (Matrix.GeneralLinearGroup.map (algebraMap ℚ ℚ_[p]) P).1 := by
    ext i j
    simp [p, ev]
  have hPvdet :
      ev.toRingEquiv.toRingHom
          (Matrix.GeneralLinearGroup.map
            (algebraMap ℚ (v.adicCompletion ℚ)) P).1.det =
        (Matrix.GeneralLinearGroup.map (algebraMap ℚ ℚ_[p]) P).1.det :=
    (RingHom.map_det ev.toRingEquiv.toRingHom _).trans
      (congrArg Matrix.det hPv)
  have hUvdet :
      ev.toRingEquiv.toRingHom
          (Matrix.GeneralLinearGroup.map
            (v.adicCompletionIntegers ℚ).subtype
            (orientedSameGenusHeightOneLocalIntegralMatrixUnit
              L M h P hP v)).1.det =
        (A.1.map PadicInt.Coe.ringHom).det :=
    (RingHom.map_det ev.toRingEquiv.toRingHom _).trans
      (congrArg Matrix.det hUv)
  change ((Matrix.GeneralLinearGroup.map
      (algebraMap ℚ (v.adicCompletion ℚ)) P).1 *
    (Matrix.GeneralLinearGroup.map
      (v.adicCompletionIntegers ℚ).subtype
      (orientedSameGenusHeightOneLocalIntegralMatrixUnit
        L M h P hP v)).1).det = 1
  rw [Matrix.det_mul]
  apply ev.injective
  rw [map_one]
  calc
    ev.toRingEquiv.toRingHom
          ((Matrix.GeneralLinearGroup.map
              (algebraMap ℚ (v.adicCompletion ℚ)) P).1.det *
            (Matrix.GeneralLinearGroup.map
              (v.adicCompletionIntegers ℚ).subtype
              (orientedSameGenusHeightOneLocalIntegralMatrixUnit
                L M h P hP v)).1.det) =
        (Matrix.GeneralLinearGroup.map
            (algebraMap ℚ ℚ_[p]) P).1.det *
          (A.1.map PadicInt.Coe.ringHom).det := by
      rw [map_mul, hPvdet, hUvdet]
    _ = ((Matrix.GeneralLinearGroup.map (algebraMap ℚ ℚ_[p]) P).1 *
          A.1.map PadicInt.Coe.ringHom).det := by
      rw [Matrix.det_mul]
    _ = 1 := hAdet

/-- A same-genus comparison admits height-one integral units whose local form
equations hold and whose composition with a fixed rational comparison has
determinant one at every finite place. -/
theorem exists_orientedHeightOneLocalIntegralMatrixUnits_of_isSameGenus
    (L M : PositiveDefiniteIntegralLattice n) [Nonempty (Fin n)]
    (h : L.IsSameGenus M)
    (P : GL (Fin n) ℚ)
    (hP : P.1ᵀ * L.rationalFormMatrix * P.1 = M.rationalFormMatrix) :
    ∃ U : (v : IsDedekindDomain.HeightOneSpectrum ℤ) →
        GL (Fin n) (v.adicCompletionIntegers ℚ),
      (∀ v : IsDedekindDomain.HeightOneSpectrum ℤ,
        let Uv : GL (Fin n) (v.adicCompletion ℚ) :=
          Matrix.GeneralLinearGroup.map
            (v.adicCompletionIntegers ℚ).subtype (U v)
        Uv.1ᵀ * M.pairingMatrix.map (algebraMap ℤ (v.adicCompletion ℚ)) * Uv.1 =
          L.pairingMatrix.map (algebraMap ℤ (v.adicCompletion ℚ))) ∧
      (∀ v : IsDedekindDomain.HeightOneSpectrum ℤ,
        let Pv : GL (Fin n) (v.adicCompletion ℚ) :=
          Matrix.GeneralLinearGroup.map (algebraMap ℚ (v.adicCompletion ℚ)) P
        let Uv : GL (Fin n) (v.adicCompletion ℚ) :=
          Matrix.GeneralLinearGroup.map
            (v.adicCompletionIntegers ℚ).subtype (U v)
        (Pv * Uv).1.det = 1) := by
  exact ⟨orientedSameGenusHeightOneLocalIntegralMatrixUnit L M h P hP,
    orientedSameGenusHeightOneLocalIntegralMatrixUnit_form_eq L M h P hP,
    orientedSameGenusHeightOneLocalIntegralMatrixUnit_det_eq_one L M h P hP⟩

end PositiveDefiniteIntegralLattice

end
