import SMSFormula.RationalSpecialOrthogonalSpinorNorm
import SMSFormula.RationalCliffordSpinCandidateScalarCentralizer
import SMSFormula.RationalCliffordSpinCandidateAdelicCarrier

/-!
# The Spin-candidate image is the spinor-norm kernel

For every characteristic-zero rational field, this file compares the concrete
Spin-candidate point map with the determinant-one spinor norm.  A reflection-
pair presentation is transported into the finite rational Clifford-coordinate
base change.  Its reverse norm is the product of the represented quadratic
values, while its conjugation is the represented special-orthogonal action.

Comparing this element with an arbitrary candidate point proves that every
candidate image has trivial spinor norm.  Conversely, triviality of the
spinor norm supplies a square root of the reverse norm; scalar normalization
then gives a candidate point above the original special-orthogonal element.

No continuity, local measure, adelic normalization, condition (K), or
Tamagawa-volume statement is made here.
-/

noncomputable section

open CliffordAlgebra
open QuadraticMap.ReflectionWord
open scoped Matrix

namespace RationalQuadraticSpaceMatrix

variable {n : ℕ} (V : RationalQuadraticSpaceMatrix n)

section Field

variable (K : Type*) [Field K] [Algebra ℚ K]

local notation "QK" => V.commutativeScalarExtensionQuadraticForm K

/-- The Clifford unit of a reflection-pair word, transported to the literal
finite rational-coordinate base change used by candidate points. -/
noncomputable def reflectionPairsCoordinateCliffordUnit
    (ps : List (QuadraticMap.ReflectionWord.ReflectionPair QK)) :
    (V.cliffordCoordinateBaseChangeAlgebra K)ˣ :=
  Units.map (V.commutativeTensorCliffordEquiv K).symm.toMonoidHom
    (reflectionPairsCliffordUnit QK ps)

@[simp]
theorem commutativeTensorCliffordEquiv_reflectionPairsCoordinateCliffordUnit
    (ps : List (QuadraticMap.ReflectionWord.ReflectionPair QK)) :
    V.commutativeTensorCliffordEquiv K
        (V.reflectionPairsCoordinateCliffordUnit K ps :
          V.cliffordCoordinateBaseChangeAlgebra K) =
      (reflectionPairsCliffordUnit QK ps : CliffordAlgebra QK) := by
  simp [reflectionPairsCoordinateCliffordUnit]

@[simp]
theorem commutativeTensorCliffordEquiv_reflectionPairsCoordinateCliffordUnit_inv
    (ps : List (QuadraticMap.ReflectionWord.ReflectionPair QK)) :
    V.commutativeTensorCliffordEquiv K
        (↑((V.reflectionPairsCoordinateCliffordUnit K ps)⁻¹) :
          V.cliffordCoordinateBaseChangeAlgebra K) =
      (↑((reflectionPairsCliffordUnit QK ps)⁻¹) :
        CliffordAlgebra QK) := by
  simp [reflectionPairsCoordinateCliffordUnit]

/-- The transported reflection-pair unit acts by the literal evaluated word
on every coordinate vector. -/
theorem reflectionPairsCoordinateCliffordUnit_conjugation
    (ps : List (QuadraticMap.ReflectionWord.ReflectionPair QK))
    (m : Fin n → K) :
    (V.reflectionPairsCoordinateCliffordUnit K ps :
        V.cliffordCoordinateBaseChangeAlgebra K) *
          V.cliffordCoordinateBaseChangeVectorOfCoordinates K m *
        (↑((V.reflectionPairsCoordinateCliffordUnit K ps)⁻¹) :
          V.cliffordCoordinateBaseChangeAlgebra K) =
      V.cliffordCoordinateBaseChangeVectorOfCoordinates K
        (eval QK (flattenPairs QK ps) m) := by
  apply (V.commutativeTensorCliffordEquiv K).injective
  simp only [map_mul,
    V.commutativeTensorCliffordEquiv_reflectionPairsCoordinateCliffordUnit,
    V.commutativeTensorCliffordEquiv_reflectionPairsCoordinateCliffordUnit_inv,
    V.commutativeTensorCliffordEquiv_vectorOfCoordinates]
  exact reflectionPairsCliffordUnit_conjugation QK ps m

theorem isometryEquiv_single_eq_sum_toMatrix'
    (e : (V.commutativeScalarExtensionQuadraticForm K).IsometryEquiv
      (V.commutativeScalarExtensionQuadraticForm K)) (i : Fin n) :
    e (Pi.single i 1) =
      ∑ j, LinearMap.toMatrix' e.toLinearEquiv.toLinearMap j i •
        (Pi.single j 1 : Fin n → K) := by
  have h := LinearMap.congr_fun
    (Matrix.toLin'_toMatrix' e.toLinearEquiv.toLinearMap) (Pi.single i 1)
  ext k
  have hk := congrFun h k
  convert hk.symm using 1
  simp [Pi.single_apply]

theorem cliffordCoordinateBaseChangeVector_eq_vectorOfCoordinates
    (i : Fin n) :
    V.cliffordCoordinateBaseChangeVector K i =
      V.cliffordCoordinateBaseChangeVectorOfCoordinates K
        (Pi.single i 1 : Fin n → K) := by
  apply (V.commutativeTensorCliffordEquiv K).injective
  simp

/-- If a reflection-pair word presents a concrete special-orthogonal
element, its transported Clifford unit has exactly that matrix action on the
standard coordinate vectors. -/
theorem reflectionPairsCoordinateCliffordUnit_vectorGraph
    (g : V.specialOrthogonalMatrixGroup K)
    (ps : List (QuadraticMap.ReflectionWord.ReflectionPair QK))
    (hps : eval QK (flattenPairs QK ps) =
      V.specialOrthogonalMatrixGroupIsometryEquiv K g)
    (i : Fin n) :
    (V.reflectionPairsCoordinateCliffordUnit K ps :
        V.cliffordCoordinateBaseChangeAlgebra K) *
          V.cliffordCoordinateBaseChangeVector K i *
        (↑((V.reflectionPairsCoordinateCliffordUnit K ps)⁻¹) :
          V.cliffordCoordinateBaseChangeAlgebra K) =
      ∑ j, g.1.1.1 j i • V.cliffordCoordinateBaseChangeVector K j := by
  rw [V.cliffordCoordinateBaseChangeVector_eq_vectorOfCoordinates]
  rw [V.reflectionPairsCoordinateCliffordUnit_conjugation, hps]
  rw [V.isometryEquiv_single_eq_sum_toMatrix']
  rw [V.specialOrthogonalMatrixGroupIsometryEquiv_toMatrix']
  simp [Pi.single_apply,
    cliffordCoordinateBaseChangeVectorOfCoordinates]

@[simp]
theorem coe_reflectionPairsCoordinateCliffordUnit_nil :
    (V.reflectionPairsCoordinateCliffordUnit K [] :
      V.cliffordCoordinateBaseChangeAlgebra K) = 1 := by
  apply (V.commutativeTensorCliffordEquiv K).injective
  simp

@[simp]
theorem coe_reflectionPairsCoordinateCliffordUnit_cons
    (p : QuadraticMap.ReflectionWord.ReflectionPair QK)
    (ps : List (QuadraticMap.ReflectionWord.ReflectionPair QK)) :
    (V.reflectionPairsCoordinateCliffordUnit K (p :: ps) :
        V.cliffordCoordinateBaseChangeAlgebra K) =
      (V.reflectionPairsCoordinateCliffordUnit K ps :
          V.cliffordCoordinateBaseChangeAlgebra K) *
        (V.cliffordCoordinateBaseChangeVectorOfCoordinates K p.2 *
          V.cliffordCoordinateBaseChangeVectorOfCoordinates K p.1) := by
  apply (V.commutativeTensorCliffordEquiv K).injective
  simp [reflectionPairsCliffordUnit, reflectionPairCliffordUnit]

/-- A standard-coordinate vector squares to its quadratic value inside the
literal Clifford-coordinate base change. -/
theorem cliffordCoordinateBaseChangeVectorOfCoordinates_sq
    (m : Fin n → K) :
    V.cliffordCoordinateBaseChangeVectorOfCoordinates K m *
        V.cliffordCoordinateBaseChangeVectorOfCoordinates K m =
      algebraMap K (V.cliffordCoordinateBaseChangeAlgebra K) (QK m) := by
  apply (V.commutativeTensorCliffordEquiv K).injective
  simp [CliffordAlgebra.ι_sq_scalar]

/-- Reflection-pair coordinate products are fixed by the grade involution. -/
theorem reflectionPairsCoordinateCliffordUnit_involute
    (ps : List (QuadraticMap.ReflectionWord.ReflectionPair QK)) :
    V.cliffordCoordinateBaseChangeInvolute K
        (V.reflectionPairsCoordinateCliffordUnit K ps :
          V.cliffordCoordinateBaseChangeAlgebra K) =
      (V.reflectionPairsCoordinateCliffordUnit K ps :
        V.cliffordCoordinateBaseChangeAlgebra K) := by
  induction ps with
  | nil => simp
  | cons p ps ih =>
      rw [V.coe_reflectionPairsCoordinateCliffordUnit_cons,
        map_mul, ih, map_mul]
      simp only [V.cliffordCoordinateBaseChangeInvolute_vectorOfCoordinates]
      let a : V.cliffordCoordinateBaseChangeAlgebra K :=
        V.cliffordCoordinateBaseChangeVectorOfCoordinates K p.2
      let b : V.cliffordCoordinateBaseChangeAlgebra K :=
        V.cliffordCoordinateBaseChangeVectorOfCoordinates K p.1
      rw [neg_mul_neg a b]

/-- The reverse norm of the transported reflection-pair word is the scalar
product of its represented quadratic values. -/
theorem reflectionPairsCoordinateCliffordUnit_mul_reverse
    (ps : List (QuadraticMap.ReflectionWord.ReflectionPair QK)) :
    (V.reflectionPairsCoordinateCliffordUnit K ps :
        V.cliffordCoordinateBaseChangeAlgebra K) *
        V.cliffordCoordinateBaseChangeReverse K
          (V.reflectionPairsCoordinateCliffordUnit K ps :
            V.cliffordCoordinateBaseChangeAlgebra K) =
      algebraMap K (V.cliffordCoordinateBaseChangeAlgebra K)
        (reflectionPairsQuadraticUnit QK ps : K) := by
  induction ps with
  | nil =>
      simp only [V.coe_reflectionPairsCoordinateCliffordUnit_nil,
        reflectionPairsQuadraticUnit_nil]
      rw [V.cliffordCoordinateBaseChangeReverse_one, mul_one]
      exact (map_one (algebraMap K
        (V.cliffordCoordinateBaseChangeAlgebra K))).symm
  | cons p ps ih =>
      rw [V.coe_reflectionPairsCoordinateCliffordUnit_cons,
        V.cliffordCoordinateBaseChangeReverse_mul,
        V.cliffordCoordinateBaseChangeReverse_mul]
      simp only [V.cliffordCoordinateBaseChangeReverse_vectorOfCoordinates]
      rw [show
          ((V.reflectionPairsCoordinateCliffordUnit K ps :
              V.cliffordCoordinateBaseChangeAlgebra K) *
            (V.cliffordCoordinateBaseChangeVectorOfCoordinates K p.2 *
              V.cliffordCoordinateBaseChangeVectorOfCoordinates K p.1)) *
            ((V.cliffordCoordinateBaseChangeVectorOfCoordinates K p.1 *
              V.cliffordCoordinateBaseChangeVectorOfCoordinates K p.2) *
              V.cliffordCoordinateBaseChangeReverse K
                (V.reflectionPairsCoordinateCliffordUnit K ps :
                  V.cliffordCoordinateBaseChangeAlgebra K)) =
          (V.reflectionPairsCoordinateCliffordUnit K ps :
              V.cliffordCoordinateBaseChangeAlgebra K) *
            ((V.cliffordCoordinateBaseChangeVectorOfCoordinates K p.2 *
                V.cliffordCoordinateBaseChangeVectorOfCoordinates K p.1) *
              (V.cliffordCoordinateBaseChangeVectorOfCoordinates K p.1 *
                V.cliffordCoordinateBaseChangeVectorOfCoordinates K p.2)) *
            V.cliffordCoordinateBaseChangeReverse K
              (V.reflectionPairsCoordinateCliffordUnit K ps :
                V.cliffordCoordinateBaseChangeAlgebra K) by
              noncomm_ring]
      rw [show
          (V.cliffordCoordinateBaseChangeVectorOfCoordinates K p.2 *
              V.cliffordCoordinateBaseChangeVectorOfCoordinates K p.1) *
            (V.cliffordCoordinateBaseChangeVectorOfCoordinates K p.1 *
              V.cliffordCoordinateBaseChangeVectorOfCoordinates K p.2) =
            algebraMap K (V.cliffordCoordinateBaseChangeAlgebra K)
              (QK p.1 * QK p.2) by
        let a := V.cliffordCoordinateBaseChangeVectorOfCoordinates K p.2
        let b := V.cliffordCoordinateBaseChangeVectorOfCoordinates K p.1
        calc
          a * b * (b * a) = a * (b * b) * a := by noncomm_ring
          _ = a * algebraMap K (V.cliffordCoordinateBaseChangeAlgebra K)
                (QK p.1) * a := by
              rw [V.cliffordCoordinateBaseChangeVectorOfCoordinates_sq]
          _ = algebraMap K (V.cliffordCoordinateBaseChangeAlgebra K)
                (QK p.1) * (a * a) := by
              rw [← Algebra.commutes (QK p.1) a]
              noncomm_ring
          _ = algebraMap K (V.cliffordCoordinateBaseChangeAlgebra K)
                (QK p.1) *
              algebraMap K (V.cliffordCoordinateBaseChangeAlgebra K)
                (QK p.2) := by
              rw [V.cliffordCoordinateBaseChangeVectorOfCoordinates_sq]
          _ = _ := by rw [← map_mul]]
      rw [← Algebra.commutes (QK p.1 * QK p.2), mul_assoc, ih,
        ← map_mul]
      congr 1

theorem cliffordCoordinateBaseChangeInvolute_coe_inv_of_coe
    (u : (V.cliffordCoordinateBaseChangeAlgebra K)ˣ)
    (hu : V.cliffordCoordinateBaseChangeInvolute K
      (u : V.cliffordCoordinateBaseChangeAlgebra K) = u) :
    V.cliffordCoordinateBaseChangeInvolute K
        (↑(u⁻¹) : V.cliffordCoordinateBaseChangeAlgebra K) =
      (↑(u⁻¹) : V.cliffordCoordinateBaseChangeAlgebra K) := by
  have huUnits : Units.map
      (V.cliffordCoordinateBaseChangeInvolute K).toMonoidHom u = u := by
    apply Units.ext
    exact hu
  have hinvUnits := congrArg Inv.inv huUnits
  have hcoe := congrArg
    (fun z : (V.cliffordCoordinateBaseChangeAlgebra K)ˣ =>
      (z : V.cliffordCoordinateBaseChangeAlgebra K)) hinvUnits
  simpa using hcoe

/-- A scalar unit inside the literal Clifford-coordinate base change. -/
def cliffordCoordinateBaseChangeScalarUnit (r : Kˣ) :
    (V.cliffordCoordinateBaseChangeAlgebra K)ˣ :=
  Units.map (algebraMap K
    (V.cliffordCoordinateBaseChangeAlgebra K)) r

@[simp]
theorem coe_cliffordCoordinateBaseChangeScalarUnit (r : Kˣ) :
    (V.cliffordCoordinateBaseChangeScalarUnit K r :
      V.cliffordCoordinateBaseChangeAlgebra K) =
      algebraMap K (V.cliffordCoordinateBaseChangeAlgebra K) (r : K) :=
  rfl

section CharZero

variable [CharZero K]

set_option maxHeartbeats 800000 in
/-- Every field-valued candidate Clifford point is a scalar multiple of the
Clifford unit attached to a determinant-one reflection-pair presentation of
its matrix component.  The final equation records the normalization forced
by the candidate's reverse norm. -/
theorem CliffordSpinCandidatePointData.exists_reflectionPairs_scalar_factorization
    (d : V.CliffordSpinCandidatePointData K) :
    ∃ ps : List (QuadraticMap.ReflectionWord.ReflectionPair
        (V.commutativeScalarExtensionQuadraticForm K)),
      ∃ r : K,
        eval (V.commutativeScalarExtensionQuadraticForm K)
            (flattenPairs (V.commutativeScalarExtensionQuadraticForm K) ps) =
          V.specialOrthogonalMatrixGroupIsometryEquiv K d.matrixGroup ∧
        d.clifford =
          (V.reflectionPairsCoordinateCliffordUnit K ps :
            V.cliffordCoordinateBaseChangeAlgebra K) *
            algebraMap K (V.cliffordCoordinateBaseChangeAlgebra K) r ∧
        (reflectionPairsQuadraticUnit
            (V.commutativeScalarExtensionQuadraticForm K) ps : K) * r ^ 2 = 1 := by
  let Q := V.commutativeScalarExtensionQuadraticForm K
  have hQ : Q.associated.Nondegenerate :=
    V.commutativeScalarExtensionQuadraticForm_associated_nondegenerate K
  let gd : DetOneIsometryGroup Q :=
    V.specialOrthogonalMatrixGroupDetOneIsometryHom K d.matrixGroup
  let ps : List (QuadraticMap.ReflectionWord.ReflectionPair Q) :=
    chosenDetOneReflectionPairs Q hQ gd
  have hps : eval Q (flattenPairs Q ps) =
      V.specialOrthogonalMatrixGroupIsometryEquiv K d.matrixGroup := by
    exact eval_chosenDetOneReflectionPairs Q hQ gd
  let u := V.reflectionPairsCoordinateCliffordUnit K ps
  let x := d.cliffordUnit
  have huInvolute : V.cliffordCoordinateBaseChangeInvolute K
      (u : V.cliffordCoordinateBaseChangeAlgebra K) = u :=
    V.reflectionPairsCoordinateCliffordUnit_involute K ps
  have huInvInvolute : V.cliffordCoordinateBaseChangeInvolute K
      (↑(u⁻¹) : V.cliffordCoordinateBaseChangeAlgebra K) =
        (↑(u⁻¹) : V.cliffordCoordinateBaseChangeAlgebra K) :=
    V.cliffordCoordinateBaseChangeInvolute_coe_inv_of_coe K u huInvolute
  have hxInvolute : V.cliffordCoordinateBaseChangeInvolute K
      (x : V.cliffordCoordinateBaseChangeAlgebra K) = x := by
    exact d.involute_eq
  have huAction (i : Fin n) :
      (u : V.cliffordCoordinateBaseChangeAlgebra K) *
            V.cliffordCoordinateBaseChangeVector K i *
          (↑(u⁻¹) : V.cliffordCoordinateBaseChangeAlgebra K) =
        ∑ j, d.matrixPoint.1 j i •
          V.cliffordCoordinateBaseChangeVector K j := by
    simpa [u, CliffordSpinCandidatePointData.matrixGroup_coe] using
      V.reflectionPairsCoordinateCliffordUnit_vectorGraph K
        d.matrixGroup ps hps i
  have hxAction (i : Fin n) :
      (x : V.cliffordCoordinateBaseChangeAlgebra K) *
            V.cliffordCoordinateBaseChangeVector K i *
          (↑(x⁻¹) : V.cliffordCoordinateBaseChangeAlgebra K) =
        ∑ j, d.matrixPoint.1 j i •
          V.cliffordCoordinateBaseChangeVector K j := by
    change d.clifford * V.cliffordCoordinateBaseChangeVector K i *
        V.cliffordCoordinateBaseChangeReverse K d.clifford = _
    exact d.vectorGraph i
  have hxMove (i : Fin n) :
      (x : V.cliffordCoordinateBaseChangeAlgebra K) *
          V.cliffordCoordinateBaseChangeVector K i =
        (∑ j, d.matrixPoint.1 j i •
          V.cliffordCoordinateBaseChangeVector K j) * x := by
    calc
      (x : V.cliffordCoordinateBaseChangeAlgebra K) *
          V.cliffordCoordinateBaseChangeVector K i =
        (((x : V.cliffordCoordinateBaseChangeAlgebra K) *
            V.cliffordCoordinateBaseChangeVector K i) *
          (↑(x⁻¹) : V.cliffordCoordinateBaseChangeAlgebra K)) * x := by
            rw [mul_assoc, x.inv_mul, mul_one]
      _ = _ := by rw [hxAction]
  have huInvMove (i : Fin n) :
      V.cliffordCoordinateBaseChangeVector K i *
          (↑(u⁻¹) : V.cliffordCoordinateBaseChangeAlgebra K) =
        (↑(u⁻¹) : V.cliffordCoordinateBaseChangeAlgebra K) *
          (∑ j, d.matrixPoint.1 j i •
            V.cliffordCoordinateBaseChangeVector K j) := by
    calc
      V.cliffordCoordinateBaseChangeVector K i *
          (↑(u⁻¹) : V.cliffordCoordinateBaseChangeAlgebra K) =
        ((↑(u⁻¹) : V.cliffordCoordinateBaseChangeAlgebra K) *
          (u : V.cliffordCoordinateBaseChangeAlgebra K)) *
          (V.cliffordCoordinateBaseChangeVector K i *
            (↑(u⁻¹) : V.cliffordCoordinateBaseChangeAlgebra K)) := by
              rw [u.inv_mul, one_mul]
      _ = (↑(u⁻¹) : V.cliffordCoordinateBaseChangeAlgebra K) *
          (((u : V.cliffordCoordinateBaseChangeAlgebra K) *
            V.cliffordCoordinateBaseChangeVector K i) *
              (↑(u⁻¹) : V.cliffordCoordinateBaseChangeAlgebra K)) := by
            noncomm_ring
      _ = _ := by rw [huAction]
  have hcomm (i : Fin n) :
      V.cliffordCoordinateBaseChangeVector K i *
          ((↑(u⁻¹) : V.cliffordCoordinateBaseChangeAlgebra K) *
            (x : V.cliffordCoordinateBaseChangeAlgebra K)) =
        ((↑(u⁻¹) : V.cliffordCoordinateBaseChangeAlgebra K) *
            (x : V.cliffordCoordinateBaseChangeAlgebra K)) *
          V.cliffordCoordinateBaseChangeVector K i := by
    rw [← mul_assoc, huInvMove, mul_assoc, ← hxMove, mul_assoc]
  have hinvolute : V.cliffordCoordinateBaseChangeInvolute K
      ((↑(u⁻¹) : V.cliffordCoordinateBaseChangeAlgebra K) *
        (x : V.cliffordCoordinateBaseChangeAlgebra K)) =
      ((↑(u⁻¹) : V.cliffordCoordinateBaseChangeAlgebra K) *
        (x : V.cliffordCoordinateBaseChangeAlgebra K)) := by
    rw [map_mul, huInvInvolute, hxInvolute]
  obtain ⟨r, hr⟩ :=
    V.exists_eq_algebraMap_of_baseChangeInvolute_eq_of_commute_vectors K
      ((↑(u⁻¹) : V.cliffordCoordinateBaseChangeAlgebra K) *
        (x : V.cliffordCoordinateBaseChangeAlgebra K)) hinvolute hcomm
  have hx_eq : d.clifford =
      (u : V.cliffordCoordinateBaseChangeAlgebra K) *
        algebraMap K (V.cliffordCoordinateBaseChangeAlgebra K) r := by
    change (x : V.cliffordCoordinateBaseChangeAlgebra K) = _
    calc
      (x : V.cliffordCoordinateBaseChangeAlgebra K) =
          ((u : V.cliffordCoordinateBaseChangeAlgebra K) *
            (↑(u⁻¹) : V.cliffordCoordinateBaseChangeAlgebra K)) * x := by
              rw [u.mul_inv, one_mul]
      _ = (u : V.cliffordCoordinateBaseChangeAlgebra K) *
          ((↑(u⁻¹) : V.cliffordCoordinateBaseChangeAlgebra K) * x) := by
            rw [mul_assoc]
      _ = _ := by rw [hr]
  have hnorm :
      (reflectionPairsQuadraticUnit Q ps : K) * r ^ 2 = 1 := by
    apply V.cliffordCoordinateBaseChange_algebraMap_injective K
    calc
      algebraMap K (V.cliffordCoordinateBaseChangeAlgebra K)
          ((reflectionPairsQuadraticUnit Q ps : K) * r ^ 2) =
        ((u : V.cliffordCoordinateBaseChangeAlgebra K) *
          V.cliffordCoordinateBaseChangeReverse K
            (u : V.cliffordCoordinateBaseChangeAlgebra K)) *
          (algebraMap K (V.cliffordCoordinateBaseChangeAlgebra K) r *
            algebraMap K (V.cliffordCoordinateBaseChangeAlgebra K) r) := by
              rw [map_mul, map_pow, pow_two,
                V.reflectionPairsCoordinateCliffordUnit_mul_reverse]
      _ = ((u : V.cliffordCoordinateBaseChangeAlgebra K) *
            algebraMap K (V.cliffordCoordinateBaseChangeAlgebra K) r) *
          V.cliffordCoordinateBaseChangeReverse K
            ((u : V.cliffordCoordinateBaseChangeAlgebra K) *
              algebraMap K (V.cliffordCoordinateBaseChangeAlgebra K) r) := by
            rw [V.cliffordCoordinateBaseChangeReverse_mul,
              V.cliffordCoordinateBaseChangeReverse_algebraMap]
            let U : V.cliffordCoordinateBaseChangeAlgebra K := u
            let T : V.cliffordCoordinateBaseChangeAlgebra K :=
              V.cliffordCoordinateBaseChangeReverse K u
            let R : V.cliffordCoordinateBaseChangeAlgebra K :=
              algebraMap K (V.cliffordCoordinateBaseChangeAlgebra K) r
            change (U * T) * (R * R) = (U * R) * (R * T)
            calc
              (U * T) * (R * R) = U * (T * (R * R)) := by
                simp only [mul_assoc]
              _ = U * ((R * R) * T) := by
                congr 1
                dsimp only [R]
                rw [← map_mul]
                exact (Algebra.commutes (r * r) T).symm
              _ = (U * R) * (R * T) := by noncomm_ring
      _ = d.clifford *
          V.cliffordCoordinateBaseChangeReverse K d.clifford := by
            rw [hx_eq]
      _ = 1 := d.mul_reverse_eq_one
      _ = algebraMap K (V.cliffordCoordinateBaseChangeAlgebra K) 1 := by
            symm
            exact map_one _
  exact ⟨ps, r, hps, hx_eq, hnorm⟩

set_option maxHeartbeats 800000 in
/-- The special-orthogonal matrix of every field-valued candidate point has
trivial spinor norm. -/
theorem CliffordSpinCandidatePointData.specialOrthogonalSpinorNorm_matrixGroup_eq_one
    (d : V.CliffordSpinCandidatePointData K) :
    V.specialOrthogonalSpinorNormHom K d.matrixGroup = 1 := by
  let Q := V.commutativeScalarExtensionQuadraticForm K
  obtain ⟨ps, r, hps, _hx_eq, hnorm⟩ :=
    d.exists_reflectionPairs_scalar_factorization
  have hr0 : r ≠ 0 := by
    intro hrzero
    rw [hrzero] at hnorm
    norm_num at hnorm
  let ur : Kˣ := Units.mk0 r hr0
  have hunit : reflectionPairsQuadraticUnit Q ps * ur ^ 2 = 1 := by
    apply Units.ext
    simpa [ur] using hnorm
  have hquadraticUnit : reflectionPairsQuadraticUnit Q ps = (ur⁻¹) ^ 2 := by
    calc
      reflectionPairsQuadraticUnit Q ps =
          reflectionPairsQuadraticUnit Q ps * 1 := by rw [mul_one]
      _ = reflectionPairsQuadraticUnit Q ps *
          (ur ^ 2 * (ur⁻¹) ^ 2) := by simp
      _ = (reflectionPairsQuadraticUnit Q ps * ur ^ 2) *
          (ur⁻¹) ^ 2 := by rw [mul_assoc]
      _ = (ur⁻¹) ^ 2 := by rw [hunit, one_mul]
  have hclass :
      ((reflectionPairsQuadraticUnit Q ps : Kˣ) : Rat.SquareClass K) = 1 := by
    rw [hquadraticUnit]
    apply (QuotientGroup.eq_one_iff ((ur⁻¹) ^ 2)).mpr
    exact ⟨ur⁻¹, pow_two (ur⁻¹)⟩
  rw [V.specialOrthogonalSpinorNormHom_eq_reflectionPairSquareClassProduct
    K d.matrixGroup ps hps]
  rw [← reflectionPairsQuadraticUnit_squareClass]
  exact hclass

/-- The image of a candidate coordinate point lies in the spinor-norm
kernel. -/
theorem specialOrthogonalSpinorNorm_candidateToSpecialOrthogonal_eq_one
    (F : V.CliffordSpinCandidateGroup K) :
    V.specialOrthogonalSpinorNormHom K
        (V.cliffordSpinCandidateGroupToSpecialOrthogonal K F) = 1 := by
  let d := V.cliffordSpinCandidatePointDataOfCoordinateAlgHom K F
  change V.specialOrthogonalSpinorNormHom K d.matrixGroup = 1
  exact d.specialOrthogonalSpinorNorm_matrixGroup_eq_one

set_option maxHeartbeats 800000 in
/-- Trivial spinor norm supplies a normalized reflection-pair candidate
point above the given special-orthogonal matrix. -/
theorem exists_cliffordSpinCandidate_of_specialOrthogonalSpinorNorm_eq_one
    (g : V.specialOrthogonalMatrixGroup K)
    (hg : V.specialOrthogonalSpinorNormHom K g = 1) :
    ∃ F : V.CliffordSpinCandidateGroup K,
      V.cliffordSpinCandidateGroupToSpecialOrthogonal K F = g := by
  let Q := V.commutativeScalarExtensionQuadraticForm K
  have hQ : Q.associated.Nondegenerate :=
    V.commutativeScalarExtensionQuadraticForm_associated_nondegenerate K
  let gd : DetOneIsometryGroup Q :=
    V.specialOrthogonalMatrixGroupDetOneIsometryHom K g
  let ps : List (QuadraticMap.ReflectionWord.ReflectionPair Q) :=
    chosenDetOneReflectionPairs Q hQ gd
  have hps : eval Q (flattenPairs Q ps) =
      V.specialOrthogonalMatrixGroupIsometryEquiv K g := by
    exact eval_chosenDetOneReflectionPairs Q hQ gd
  have hpairs : reflectionPairSquareClassProduct Q ps = 1 := by
    rw [← V.specialOrthogonalSpinorNormHom_eq_reflectionPairSquareClassProduct
      K g ps hps]
    exact hg
  have hquadraticClass :
      ((reflectionPairsQuadraticUnit Q ps : Kˣ) : Rat.SquareClass K) = 1 := by
    rwa [reflectionPairsQuadraticUnit_squareClass]
  have hsquare : IsSquare (reflectionPairsQuadraticUnit Q ps) := by
    exact (QuotientGroup.eq_one_iff
      (reflectionPairsQuadraticUnit Q ps)).mp hquadraticClass
  obtain ⟨r, hr⟩ := hsquare
  let u := V.reflectionPairsCoordinateCliffordUnit K ps
  let a := V.cliffordCoordinateBaseChangeScalarUnit K r⁻¹
  let z : (V.cliffordCoordinateBaseChangeAlgebra K)ˣ := a * u
  have huInvolute : V.cliffordCoordinateBaseChangeInvolute K
      (u : V.cliffordCoordinateBaseChangeAlgebra K) = u :=
    V.reflectionPairsCoordinateCliffordUnit_involute K ps
  have hzInvolute : V.cliffordCoordinateBaseChangeInvolute K
      (z : V.cliffordCoordinateBaseChangeAlgebra K) = z := by
    change V.cliffordCoordinateBaseChangeInvolute K
        ((a : V.cliffordCoordinateBaseChangeAlgebra K) *
          (u : V.cliffordCoordinateBaseChangeAlgebra K)) =
      (a : V.cliffordCoordinateBaseChangeAlgebra K) *
        (u : V.cliffordCoordinateBaseChangeAlgebra K)
    rw [map_mul, huInvolute]
    change V.cliffordCoordinateBaseChangeInvolute K
          (algebraMap K (V.cliffordCoordinateBaseChangeAlgebra K)
            ((r⁻¹ : Kˣ) : K)) *
        (u : V.cliffordCoordinateBaseChangeAlgebra K) =
      algebraMap K (V.cliffordCoordinateBaseChangeAlgebra K)
          ((r⁻¹ : Kˣ) : K) *
        (u : V.cliffordCoordinateBaseChangeAlgebra K)
    rw [V.cliffordCoordinateBaseChangeInvolute_algebraMap]
  have haReverse : V.cliffordCoordinateBaseChangeReverse K
      (a : V.cliffordCoordinateBaseChangeAlgebra K) = a := by
    change V.cliffordCoordinateBaseChangeReverse K
        (algebraMap K (V.cliffordCoordinateBaseChangeAlgebra K)
          ((r⁻¹ : Kˣ) : K)) =
      algebraMap K (V.cliffordCoordinateBaseChangeAlgebra K)
        ((r⁻¹ : Kˣ) : K)
    rw [V.cliffordCoordinateBaseChangeReverse_algebraMap]
  have hzNorm :
      (z : V.cliffordCoordinateBaseChangeAlgebra K) *
        V.cliffordCoordinateBaseChangeReverse K
          (z : V.cliffordCoordinateBaseChangeAlgebra K) = 1 := by
    change ((a : V.cliffordCoordinateBaseChangeAlgebra K) *
        (u : V.cliffordCoordinateBaseChangeAlgebra K)) *
      V.cliffordCoordinateBaseChangeReverse K
        ((a : V.cliffordCoordinateBaseChangeAlgebra K) *
          (u : V.cliffordCoordinateBaseChangeAlgebra K)) = 1
    rw [V.cliffordCoordinateBaseChangeReverse_mul, haReverse]
    rw [show
      ((a : V.cliffordCoordinateBaseChangeAlgebra K) *
          (u : V.cliffordCoordinateBaseChangeAlgebra K)) *
        (V.cliffordCoordinateBaseChangeReverse K
            (u : V.cliffordCoordinateBaseChangeAlgebra K) *
          (a : V.cliffordCoordinateBaseChangeAlgebra K)) =
        ((a : V.cliffordCoordinateBaseChangeAlgebra K) *
          (a : V.cliffordCoordinateBaseChangeAlgebra K)) *
          ((u : V.cliffordCoordinateBaseChangeAlgebra K) *
            V.cliffordCoordinateBaseChangeReverse K
              (u : V.cliffordCoordinateBaseChangeAlgebra K)) by
        let A : V.cliffordCoordinateBaseChangeAlgebra K := a
        let U : V.cliffordCoordinateBaseChangeAlgebra K := u
        let T : V.cliffordCoordinateBaseChangeAlgebra K :=
          V.cliffordCoordinateBaseChangeReverse K u
        change (A * U) * (T * A) = (A * A) * (U * T)
        calc
          (A * U) * (T * A) = A * ((U * T) * A) := by noncomm_ring
          _ = A * (A * (U * T)) := by
            congr 1
            change (U * T) * algebraMap K
                (V.cliffordCoordinateBaseChangeAlgebra K) ((r⁻¹ : Kˣ) : K) =
              algebraMap K (V.cliffordCoordinateBaseChangeAlgebra K)
                  ((r⁻¹ : Kˣ) : K) * (U * T)
            exact (Algebra.commutes (((r⁻¹ : Kˣ) : K)) (U * T)).symm
          _ = (A * A) * (U * T) := by noncomm_ring]
    rw [V.reflectionPairsCoordinateCliffordUnit_mul_reverse]
    change
      (algebraMap K (V.cliffordCoordinateBaseChangeAlgebra K)
          ((r⁻¹ : Kˣ) : K) *
        algebraMap K (V.cliffordCoordinateBaseChangeAlgebra K)
          ((r⁻¹ : Kˣ) : K)) *
        algebraMap K (V.cliffordCoordinateBaseChangeAlgebra K)
          (reflectionPairsQuadraticUnit Q ps : K) = 1
    rw [← map_mul, ← map_mul,
      ← map_one (algebraMap K (V.cliffordCoordinateBaseChangeAlgebra K))]
    congr 1
    have hrUnits : reflectionPairsQuadraticUnit Q ps = r ^ 2 := by
      simpa [pow_two] using hr
    rw [hrUnits]
    have hu : (r⁻¹) ^ 2 * r ^ 2 = (1 : Kˣ) := by simp
    simpa only [Units.val_mul, Units.val_pow_eq_pow_val,
      Units.val_inv_eq_inv_val, Units.val_one, pow_two] using congrArg Units.val hu
  have hzReverse :
      V.cliffordCoordinateBaseChangeReverse K
          (z : V.cliffordCoordinateBaseChangeAlgebra K) =
        (↑(z⁻¹) : V.cliffordCoordinateBaseChangeAlgebra K) :=
    Units.eq_inv_of_mul_eq_one_left hzNorm
  have huAction (i : Fin n) :
      (u : V.cliffordCoordinateBaseChangeAlgebra K) *
            V.cliffordCoordinateBaseChangeVector K i *
          (↑(u⁻¹) : V.cliffordCoordinateBaseChangeAlgebra K) =
        ∑ j, g.1.1.1 j i •
          V.cliffordCoordinateBaseChangeVector K j :=
    V.reflectionPairsCoordinateCliffordUnit_vectorGraph K g ps hps i
  let d : V.CliffordSpinCandidatePointData K :=
    { clifford := z
      matrixPoint := V.specialOrthogonalMatrixPointOfGroup K g
      involute_eq := hzInvolute
      mul_reverse_eq_one := hzNorm
      vectorGraph := by
        intro i
        rw [hzReverse]
        change ((a : V.cliffordCoordinateBaseChangeAlgebra K) *
              (u : V.cliffordCoordinateBaseChangeAlgebra K)) *
            V.cliffordCoordinateBaseChangeVector K i *
              (↑((a * u)⁻¹) : V.cliffordCoordinateBaseChangeAlgebra K) = _
        rw [mul_inv_rev]
        change ((a : V.cliffordCoordinateBaseChangeAlgebra K) *
              (u : V.cliffordCoordinateBaseChangeAlgebra K)) *
            V.cliffordCoordinateBaseChangeVector K i *
              ((↑(u⁻¹) : V.cliffordCoordinateBaseChangeAlgebra K) *
                (↑(a⁻¹) : V.cliffordCoordinateBaseChangeAlgebra K)) = _
        rw [show
          ((a : V.cliffordCoordinateBaseChangeAlgebra K) *
                (u : V.cliffordCoordinateBaseChangeAlgebra K)) *
              V.cliffordCoordinateBaseChangeVector K i *
                ((↑(u⁻¹) : V.cliffordCoordinateBaseChangeAlgebra K) *
                  (↑(a⁻¹) : V.cliffordCoordinateBaseChangeAlgebra K)) =
            (a : V.cliffordCoordinateBaseChangeAlgebra K) *
              (((u : V.cliffordCoordinateBaseChangeAlgebra K) *
                V.cliffordCoordinateBaseChangeVector K i) *
                  (↑(u⁻¹) : V.cliffordCoordinateBaseChangeAlgebra K)) *
              (↑(a⁻¹) : V.cliffordCoordinateBaseChangeAlgebra K) by
                noncomm_ring]
        rw [huAction]
        have haComm :
            (a : V.cliffordCoordinateBaseChangeAlgebra K) *
                (∑ j, g.1.1.1 j i •
                  V.cliffordCoordinateBaseChangeVector K j) =
              (∑ j, g.1.1.1 j i •
                  V.cliffordCoordinateBaseChangeVector K j) * a := by
          exact Algebra.commutes _ _
        rw [haComm, mul_assoc, a.mul_inv, mul_one]
        rfl }
  let F : V.CliffordSpinCandidateGroup K :=
    V.cliffordSpinCandidateCoordinateAlgHomOfPointData K d
  refine ⟨F, ?_⟩
  change (V.cliffordSpinCandidatePointDataOfCoordinateAlgHom K F).matrixGroup = g
  have hd : V.cliffordSpinCandidatePointDataOfCoordinateAlgHom K F = d :=
    (V.cliffordSpinCandidateCoordinateAlgHomEquivPointData K).apply_symm_apply d
  rw [hd]
  exact (V.specialOrthogonalMatrixPointEquivGroup K).apply_symm_apply g

/-- Over every characteristic-zero rational field, the Spin-candidate image
is exactly the kernel of the concrete spinor norm. -/
theorem specialOrthogonalSpinorNorm_ker_eq_cliffordSpinCandidate_range :
    (V.specialOrthogonalSpinorNormHom K).ker =
      (V.cliffordSpinCandidateGroupToSpecialOrthogonal K).range := by
  ext g
  constructor
  · intro hg
    change V.specialOrthogonalSpinorNormHom K g = 1 at hg
    obtain ⟨F, hF⟩ :=
      V.exists_cliffordSpinCandidate_of_specialOrthogonalSpinorNorm_eq_one
        K g hg
    exact ⟨F, hF⟩
  · rintro ⟨F, rfl⟩
    change V.specialOrthogonalSpinorNormHom K
      (V.cliffordSpinCandidateGroupToSpecialOrthogonal K F) = 1
    exact V.specialOrthogonalSpinorNorm_candidateToSpecialOrthogonal_eq_one K F

/-- The real Spin-candidate image is the kernel of the real spinor norm. -/
theorem realSpecialOrthogonalSpinorNorm_ker_eq_cliffordSpinCandidate_range :
    V.realSpecialOrthogonalSpinorNormHom.ker =
      V.realCliffordSpinCandidateToSpecialOrthogonalHom.range := by
  exact V.specialOrthogonalSpinorNorm_ker_eq_cliffordSpinCandidate_range ℝ

/-- The p-adic Spin-candidate image is the kernel of the p-adic spinor norm. -/
theorem padicSpecialOrthogonalSpinorNorm_ker_eq_cliffordSpinCandidate_range
    (p : ℕ) [Fact p.Prime] :
    (V.padicSpecialOrthogonalSpinorNormHom p).ker =
      (V.cliffordSpinCandidateGroupToSpecialOrthogonal ℚ_[p]).range := by
  exact V.specialOrthogonalSpinorNorm_ker_eq_cliffordSpinCandidate_range ℚ_[p]

end CharZero

end Field

end RationalQuadraticSpaceMatrix
