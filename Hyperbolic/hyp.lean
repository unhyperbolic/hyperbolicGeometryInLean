import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Vector
import Mathlib.Data.Fin.VecNotation
import Mathlib.LinearAlgebra.BilinearForm
import Mathlib.Algebra.BigOperators.Basic
import Hyperbolic.Arcosh

import Mathlib.Data.Vector

open Real BigOperators

def Sign := {r : ℝ // r = 1 ∨ r = -1}
instance : Coe Sign ℝ := ⟨ fun r => r.val ⟩

structure PseudoEuclideanSpace where
  dim : Nat
  signature : Fin dim → Sign
  form : BilinForm ℝ (Fin dim → ℝ) := {
    bilin := fun v w => ∑ i, (v i) * (w i) * (signature i)
    bilin_add_left := sorry
    bilin_smul_left := sorry
    bilin_add_right := sorry
    bilin_smul_right := sorry
  }

namespace Minkowski

@[reducible]
def MinkowskiSpace : PseudoEuclideanSpace where
  dim := 4
  signature := ![⟨-1, by right; rfl⟩, ⟨1, by left; rfl⟩, ⟨1, by left; rfl⟩, ⟨1, by left; rfl⟩]

@[reducible]
def MVector := Fin 4 → ℝ
deriving AddCommGroup
noncomputable instance : Module ℝ MVector := by delta MVector; infer_instance
def MForm := MinkowskiSpace.form

theorem MForm_eval (v : MVector) (w : MVector) : 
  MForm v w = ∑ i, (v i) * (w i) * (MinkowskiSpace.signature i) := by rfl

theorem MForm_sym (v w : MVector) : MForm v w = MForm w v := by
  rw [MForm_eval, MForm_eval, Fin.sum_univ_four, Fin.sum_univ_four]
  ring

def TimeLike (v : MVector) : Prop := MForm v v < 0
def UnitTimeLike (v : MVector) : Prop := MForm v v = -1
def LightLike (v : MVector) : Prop := MForm v v = 0
def SpaceLike (v : MVector) : Prop := MForm v v > 0
def UnitSpaceLike (v : MVector) : Prop := MForm v v =1

def Future (v : MVector) : Prop := v 0 > 0

theorem UTL_TL (v : MVector) : UnitTimeLike v → TimeLike v := by
  rw [TimeLike, UnitTimeLike]
  intro h
  rw [h]
  linarith

theorem USL_SL (v : MVector) : UnitSpaceLike v → SpaceLike v := by
  rw [SpaceLike, UnitSpaceLike] 
  intro h
  rw [h]
  linarith

@[reducible]
def origin : MVector := ![1,0,0,0]
theorem origin0 : origin 0 = 1 := by rfl
theorem origin1 : origin 1 = 0 := by rfl
theorem origin2 : origin 2 = 0 := by rfl
theorem origin3 : origin 3 = 0 := by rfl

theorem origin_UTL : UnitTimeLike origin := by
  rw [UnitTimeLike, MForm_eval origin origin, Fin.sum_univ_four]
  rw [origin0, origin1, origin2, origin3]
  simp

theorem origin_Future : Future origin := by
  rw [Future, origin0]
  exact one_pos

noncomputable def normalize_TL (v : MVector) :=
  (sqrt (- MForm v v))⁻¹ • v 

theorem normalize_TL_UTL (v : MVector) (hv : TimeLike v) : UnitTimeLike (normalize_TL v) := by
  rw [TimeLike] at hv
  rw [UnitTimeLike, normalize_TL]
  rw [BilinForm.smul_left, BilinForm.smul_right]
  rw [← mul_assoc, ← mul_inv, mul_self_sqrt (by linarith)]
  rw [neg_eq_neg_one_mul, mul_inv, mul_assoc]
  rw [inv_mul_cancel (by linarith)]
  norm_num

theorem smul_MVector {r : Real} {v : MVector} : ∀ i, (r • v) i = r * (v i) := by intro i; rfl
theorem add_MVector {v w : MVector} : ∀ i, (v + w) i = v i + w i := by intro i; rfl

theorem scale_Future {r : Real} (hr : r > 0) (hv : Future v) : Future (r • v) := by
  rw [Future] at hv
  rw [Future]
  rw [smul_MVector 0]
  exact Real.mul_pos hr hv

theorem normalize_TL_Future (v : MVector) (hvf : Future v) (hvt : TimeLike v) :
  Future (normalize_TL v) := by
    apply scale_Future _ hvf
    apply inv_pos_of_pos
    apply sqrt_pos_of_pos
    rw [TimeLike] at hvt
    linarith

@[reducible]
def MPoint := { v : MVector // UnitTimeLike v ∧ Future v}
instance : Coe MPoint MVector := ⟨ fun v => v.val ⟩
@[reducible]
def LightPoint := { v : MVector // LightLike v ∧ Future v}
instance : Coe LightPoint MVector := ⟨ fun v => v.val ⟩  

noncomputable def normalized_TL (v : MVector) (hvt : TimeLike v) (hvf : Future v) : MPoint := 
  ⟨ normalize_TL v, by
    constructor
    . exact normalize_TL_UTL v hvt
    . exact normalize_TL_Future v hvf hvt ⟩

noncomputable def Distance (v w : MPoint) : ℝ := Real.arcosh (- MForm v w)

def Origin : MPoint := ⟨ origin, ⟨origin_UTL, origin_Future⟩ ⟩

theorem self_dist (v : MPoint) : Distance v v = 0 := by
  rw [Distance, Real.arcosh, v.prop.1]
  simp

@[reducible]
structure Line where
  endpoints : Fin 2 → LightPoint
  neg_prod : MForm (endpoints 0) (endpoints 1) < 0

noncomputable def PointOnLine (l : Line) (t : Fin 2 → PReal) : MVector :=
  (t 0 : Real) • (l.endpoints 0 : MVector) +
  (t 1 : Real) • (l.endpoints 1 : MVector)

lemma endpoint_form (l : Line) (i : Fin 2) :
  MForm (l.endpoints i) (l.endpoints i) = 0 := by
  have h := (l.endpoints i).prop
  rw [LightLike, Future] at h
  exact h.1

theorem lines_timelike (l : Line) (t : Fin 2 → PReal) :
  TimeLike (PointOnLine l t) := by
  rw [TimeLike, PointOnLine]
  simp; rw [endpoint_form, endpoint_form, MForm_sym]; simp 
  have _ := l.neg_prod
  ring_nf
  apply mul_neg_of_neg_of_pos _ (by linarith)
  rw [mul_assoc]
  apply mul_neg_of_pos_of_neg (t 0).prop
  exact mul_neg_of_pos_of_neg (t 1).prop l.neg_prod

lemma lines_future (l : Line) (t : Fin 2 → PReal) : Future (PointOnLine l t) := by
  rw [Future, PointOnLine, add_MVector, smul_MVector, smul_MVector]
  apply add_pos <;> apply mul_pos
  exact (t 0).prop
  exact (l.endpoints 0).prop.2
  exact (t 1).prop
  exact (l.endpoints 1).prop.2

noncomputable def MPoint_on_line (l : Line) (t : Fin 2 → PReal) : MPoint :=
  ⟨normalize_TL (PointOnLine l t), by
    constructor
    . exact normalize_TL_UTL (PointOnLine l t) (lines_timelike l t)
    . exact normalize_TL_Future (PointOnLine l t) (lines_future l t) (lines_timelike l t)
  ⟩

def HPoint (v : MPoint) (w : LightPoint) : Prop := MForm v w = -1

noncomputable def RayVector (t : ℝ) : MVector := ![cosh t, sinh t, 0, 0]
lemma RayVector0 (t : ℝ) : RayVector t 0 = cosh t := rfl
lemma RayVector1 (t : ℝ) : RayVector t 1 = sinh t := rfl
lemma RayVector2 (t : ℝ) : RayVector t 2 = 0 := rfl
lemma RayVector3 (t : ℝ) : RayVector t 3 = 0 := rfl

end Minkowski
#exit

noncomputable def standard_ray_vector (t : ℝ) : vector := ![cosh t, sinh t, 0, 0]

theorem standard_ray_vector0 (t : ℝ) : standard_ray_vector t 0 = cosh t := rfl
theorem standard_ray_vector1 (t : ℝ) : standard_ray_vector t 1 = sinh t := rfl
theorem standard_ray_vector2 (t : ℝ) : standard_ray_vector t 2 = 0 := rfl
theorem standard_ray_vector3 (t : ℝ) : standard_ray_vector t 3 = 0 := rfl

noncomputable def standard_ray (t : ℝ) : point :=
  ⟨standard_ray_vector t,
   by 
      rw [isFutureUnitTimeLike, isUnitTimeLike, isFuture]
      constructor
      · rw [inner_product]
        rw [standard_ray_vector0, standard_ray_vector1, standard_ray_vector2, standard_ray_vector3]
        simp
        rw [← sq, ← sq]
        rw [Real.cosh_sq]
        simp
      · rw [standard_ray_vector0]
        exact cosh_pos t⟩

def standard_horosphere1_vector (t : ℝ) (s : ℝ) : vector := ![t,s * t,0,0]

theorem standard_horosphere1_vector0 (t : ℝ) (s : ℝ) : standard_horosphere1_vector t s 0 = t := rfl
theorem standard_horosphere1_vector1 (t : ℝ) (s : ℝ) : standard_horosphere1_vector t s 1 = s * t := rfl
theorem standard_horosphere1_vector2 (t : ℝ) (s : ℝ) : standard_horosphere1_vector t s 2 = 0 := rfl
theorem standard_horosphere1_vector3 (t : ℝ) (s : ℝ) : standard_horosphere1_vector t s 3 = 0 := rfl

@[reducible]
def direction := { r : ℝ // r^2 = 1 }

instance : Neg direction := ⟨ fun r => ⟨-↑r, by 
  cases' r with rr rrr
  dsimp
  rw [neg_sq]
  exact rrr
  ⟩⟩

-- instance : Coe direction ℝ := ⟨ fun p => p.val ⟩


def standard_horosphere1 (t : PReal) (s : direction) : lightPoint :=
  ⟨standard_horosphere1_vector t s,
   by
      rw [isFutureLightLike, isLightLike, isFuture]
      constructor
      · rw [inner_product]
        rw [standard_horosphere1_vector0,standard_horosphere1_vector1,standard_horosphere1_vector2,standard_horosphere1_vector3]
        simp only [neg_mul, mul_zero, add_zero]
        cases' t with tt
        cases' s with ss sss
        dsimp
        have g : -(tt * tt) + ss * tt * (ss * tt) = -tt ^ 2 + ss ^ 2 * tt ^2 := by
           linarith
        rw [g]
        rw [sss]
        linarith
      · rw [standard_horosphere1_vector0]
        cases' t with tt ttt
        dsimp
        exact ttt
     ⟩

theorem point_on_standard_horosphere1 :
    is_point_on_horosphere (standard_ray 0) (standard_horosphere1 ⟨1, by linarith⟩ ⟨ 1, by linarith⟩) := by
  rw [is_point_on_horosphere]
  rw [inner_product]
  rw [standard_ray]
  rw [standard_horosphere1]
  dsimp
  rw [standard_ray_vector0, standard_ray_vector1, standard_ray_vector2, standard_ray_vector3]
  rw [standard_horosphere1_vector0,standard_horosphere1_vector1,standard_horosphere1_vector2,standard_horosphere1_vector3]
  simp only [cosh_zero, mul_one, sinh_zero, add_zero, mul_zero]

set_option maxHeartbeats 0

def mirror_x (v : vector) := ![v 0, -(v 1), v 2, v 3]

theorem mirror_x0 (v : vector) : (mirror_x v) 0 = v 0 := rfl
theorem mirror_x1 (v : vector) : (mirror_x v) 1 = -(v 1) := rfl
theorem mirror_x2 (v : vector) : (mirror_x v) 2 = v 2 := rfl
theorem mirror_x3 (v : vector) : (mirror_x v) 3 = v 3 := rfl

theorem mirror_x_inner_product (u v : vector) : inner_product u v = inner_product (mirror_x u) (mirror_x v) := by
  rw [inner_product]
  rw [inner_product]
  rw [mirror_x0, mirror_x0, mirror_x1, mirror_x1, mirror_x2, mirror_x2, mirror_x3, mirror_x3]
  linarith

theorem mirror_x_standard_ray (t : ℝ) : mirror_x ↑(standard_ray t) = (↑(standard_ray (-t)) : vector) := by
  rw [mirror_x]
  rw [standard_ray]
  rw [standard_ray]
  dsimp
  rw [standard_ray_vector0, standard_ray_vector1, standard_ray_vector2, standard_ray_vector3]
  rw [standard_ray_vector]
  rw [sinh_neg]
  rw [cosh_neg]

theorem mirror_x_standard_horosphere (t : PReal) (d : direction) : mirror_x ↑(standard_horosphere1 t d) = (↑(standard_horosphere1 t (-d)) : vector) := by
  rw [mirror_x]
  rw [standard_horosphere1]
  rw [standard_horosphere1]
  dsimp
  rw [standard_horosphere1_vector0, standard_horosphere1_vector1, standard_horosphere1_vector2, standard_horosphere1_vector3]
  rw [standard_horosphere1_vector]
  cases' d with dd ddd
  cases' t with tt ttt
  dsimp
  rw [← neg_mul]
  rfl

theorem exp_neg_log (t : PReal) : exp (-log t) = 1/t := by
  cases' t with tt ttt
  have a : exp (-log tt) * exp (log tt) = 1 := by
    rw [← exp_add]
    simp only [add_left_neg, exp_zero]
  rw [exp_log ttt] at a
  symm
  rw [div_eq_iff (ne_of_gt ttt)]
  symm
  exact a

theorem point_on_standard_horosphere1_general (t : PReal):
    is_point_on_horosphere (standard_ray (log ↑t)) (standard_horosphere1 t ⟨1, by linarith⟩) := by
  rw [is_point_on_horosphere]
  rw [inner_product]
  rw [standard_ray]
  rw [standard_horosphere1]
  dsimp
  rw [standard_ray_vector0, standard_ray_vector1, standard_ray_vector2, standard_ray_vector3]
  rw [standard_horosphere1_vector0,standard_horosphere1_vector1,standard_horosphere1_vector2,standard_horosphere1_vector3]
  simp only [neg_mul, one_mul, mul_zero, add_zero] 
  cases' t with tt ttt
  dsimp
  rw [cosh_eq, sinh_eq]
  rw [exp_log ttt]
  rw [exp_neg_log ⟨tt, ttt⟩]
  simp only [one_div]
  rw [mul_comm]
  rw [mul_div]
  rw [mul_add]
  rw [mul_comm ((tt - tt⁻¹) / 2) tt]
  rw [mul_div]
  rw [mul_sub]
  rw [mul_inv_cancel (ne_of_gt ttt)]
  linarith

theorem point_on_standard_horosphere1_general2 (t : PReal):
     is_point_on_horosphere (standard_ray (-log ↑t)) (standard_horosphere1 t ⟨-1, by linarith⟩) := by sorry

theorem d1 (t0 : PReal) (t1 : PReal) :
  let horosphere1 := (standard_horosphere1 t0 ⟨ 1, by linarith⟩)
  let horosphere2 := (standard_horosphere1 t1 ⟨ -1, by linarith⟩)
  let pt0 := (standard_ray (log ↑t0))
  let pt1 := (standard_ray (-(log ↑t1)))
  distance pt0 pt1 = log (inner_product ↑horosphere1 ↑horosphere2) := by sorry