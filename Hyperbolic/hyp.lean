import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Vector
import Mathlib.Data.Fin.VecNotation
import Hyperbolic.Arcosh

import Mathlib.Data.Vector

open Real

namespace R13

--def vector := Fin 4 → ℝ

def vector := Fin 4 → ℝ
deriving AddCommGroup

noncomputable instance : Module ℝ vector := by delta vector; infer_instance

--instance : Zero vector := ⟨ fun _ => 0⟩
--instance : Add vector := ⟨ fun a b => fun i => (a i) + (b i) ⟩
--instance : Neg vector := ⟨ fun a => fun i => -(a i)⟩
--instance : HMul ℝ vector vector := ⟨fun r v => fun i => r * (v i)⟩

def inner_product (a b : vector) : ℝ := -(a 0) * (b 0) + (a 1) * (b 1) + (a 2) * (b 2) + (a 3) * (b 3)

theorem v_addd (a b : vector) (i : Fin 4) : (a + b) i = (a i) + (b i) := rfl
theorem v_hmull (r : ℝ) (a : vector) (i : Fin 4) : (r • a) i = r •(a i) := rfl 


theorem inner_product_lin0 (a b c : vector) : 
    inner_product (a + b) c = inner_product a c + inner_product b c := by  
  rw [inner_product]
  rw [inner_product]
  rw [inner_product]
  rw [v_addd]
  rw [v_addd]
  rw [v_addd]
  rw [v_addd]
  linarith

theorem inner_product_lina0 (a : ℝ) (b c : vector) :
    inner_product (a • b) c = a • inner_product b c := by
  rw [inner_product]
  rw [inner_product]
  rw [v_hmull]
  rw [v_hmull]
  rw [v_hmull]
  rw [v_hmull]
  dsimp
  linarith

theorem inner_product_lin1 (a b c : vector) : 
    inner_product a (b + c) = inner_product a b + inner_product a c := by
  rw [inner_product]
  rw [inner_product]
  rw [inner_product]
  rw [v_addd]
  rw [v_addd]
  rw [v_addd]
  rw [v_addd]
  dsimp
  linarith

theorem inner_product_lina1 (a : ℝ) (b c : vector) :
    inner_product b (a • c) = a • inner_product b c := by
  rw [inner_product]
  rw [inner_product]
  rw [v_hmull]
  rw [v_hmull]
  rw [v_hmull]
  rw [v_hmull]
  dsimp
  linarith

theorem inner_product_sym (a b : vector) :
    inner_product a b = inner_product b a := by
  rw [inner_product]
  rw [inner_product]
  linarith

def isUnitTimeLike (v : vector) : Prop := (inner_product v v) = -1
def isTimeLike (v : vector) : Prop := (inner_product v v) < 0

def isLightLike (v : vector) : Prop := (inner_product v v) = 0

def isUnitSpaceLike (v : vector) : Prop := (inner_product v v) = 1
def isSpaceLike (v : vector) : Prop := (inner_product v v) > 0

def isFuture (v : vector) : Prop := (v 0) > 0

def isFutureTimeLike (v : vector) : Prop := isTimeLike v ∧ isFuture v
def isFutureUnitTimeLike (v : vector) : Prop := isUnitTimeLike v ∧ isFuture v
def isFutureLightLike (v : vector) : Prop := isLightLike v ∧ isFuture v

theorem unitTimeLikeTimeLike (v : vector) : isUnitTimeLike v → isTimeLike v := by
  rw [isTimeLike, isUnitTimeLike]
  intro h
  rw [h]
  linarith

theorem unitSpaceLikeSpaceLike (v : vector) : isUnitSpaceLike v →isSpaceLike v := by
  rw [isSpaceLike, isUnitSpaceLike] 
  intro h
  rw [h]
  linarith

def timeBasisVector : vector := ![1,0,0,0]

theorem timeBasisVector0 : timeBasisVector 0 = 1 := rfl
theorem timeBasisVector1 : timeBasisVector 1 = 0 := rfl
theorem timeBasisVector2 : timeBasisVector 2 = 0 := rfl
theorem timeBasisVector3 : timeBasisVector 3 = 0 := rfl

theorem originUnitTimeLike : isUnitTimeLike timeBasisVector := by
  rw [isUnitTimeLike, inner_product,
      timeBasisVector0, timeBasisVector1, timeBasisVector2, timeBasisVector3]
  simp

theorem originFuture : isFuture timeBasisVector := by
  rw [isFuture, timeBasisVector0]
  linarith

theorem originFutureUnitTimeLike : isFutureUnitTimeLike timeBasisVector := by
  rw [isFutureUnitTimeLike]
  exact ⟨ originUnitTimeLike, originFuture ⟩

noncomputable def normalized_time_like_vector (v : vector) :=
  (1 / sqrt (-(inner_product v v))) • v

theorem normalized_time_like_vector_unit_time_like (v : vector) (p : isFutureTimeLike v) : 
       isFutureUnitTimeLike (normalized_time_like_vector v) := by
  rw [normalized_time_like_vector, isFutureUnitTimeLike, isUnitTimeLike, isFuture]
  rw [isFutureTimeLike, isTimeLike, isFuture] at p
  cases' p with timeLike future
  rw [← neg_pos] at timeLike
  constructor
  · rw [inner_product_lina0, inner_product_lina1]
    simp only [one_div, smul_eq_mul]
    have p3 := inv_pos.mpr timeLike
    have p4 := LT.lt.le p3
    have p5 := ne_of_gt timeLike
    have p6 := neg_ne_zero.mp p5
    rw [← sqrt_inv]
    rw [← mul_assoc]
    rw [mul_self_sqrt p4]
    rw [neg_eq_neg_one_mul]
    rw [mul_inv]
    rw [mul_assoc]
    rw [inv_mul_cancel p6]
    simp only [mul_one]
    exact inv_neg_one
  · rw [v_hmull]
    dsimp
    have p3 := sqrt_pos.mpr timeLike
    have p4 := one_div_pos.mpr p3
    exact Real.mul_pos p4 future

end R13

open R13

@[reducible]
def point := { v : vector // isFutureUnitTimeLike v }

@[reducible]
def lightPoint := { v : vector // isFutureLightLike v}

-- instance : Coe point vector := ⟨ fun p => p.val ⟩
-- instance : Coe lightPoint vector := ⟨ fun p => p.val ⟩

noncomputable def normalized_time_like (v : vector) (p : isFutureTimeLike v) : point :=
    ⟨ normalized_time_like_vector v, normalized_time_like_vector_unit_time_like v p⟩

noncomputable def distance (a b : point) : ℝ  :=
    Real.arcosh (-(inner_product a b))

def origin : point := ⟨ timeBasisVector, originFutureUnitTimeLike ⟩

theorem zero_dis (a : point) : distance a a = 0 := by
  rw [distance]
  have h := a.prop
  rw [isFutureUnitTimeLike, isUnitTimeLike] at h
  rw [h.1]
  rw [arcosh]
  simp

theorem zero_dis_origin : distance origin origin = 0 := zero_dis origin

structure Line where
  endpoints : Fin 2 → lightPoint
  neg_prod : inner_product (endpoints 0) (endpoints 1) < 0

noncomputable def sample_on_line (l : Line) (t : Fin 2 → PReal) : vector :=
  (↑(t 0) : ℝ) • (↑(l.endpoints 0) : vector) +
  (↑(t 1) : ℝ) • (↑(l.endpoints 1) : vector)

theorem sample_on_line_future_time_like (l : Line) (t : Fin 2 → PReal) :
            isFutureTimeLike (sample_on_line l t) := by
  rw [isFutureTimeLike, isTimeLike, isFuture, sample_on_line]
  constructor
  · rw [inner_product_lin0, inner_product_lina0, inner_product_lin1, inner_product_lina1]
    rw [inner_product_lina0, inner_product_lin1, inner_product_lina1]
    rw [inner_product_lina1]
    rw [inner_product_lina1]
    have z (i : Fin 2) : inner_product ↑(l.endpoints i) ↑(l.endpoints i) = 0 := by
      have p := (l.endpoints i).prop
      rw [isFutureLightLike, isLightLike] at p
      exact p.1      
    rw [z]
    rw [z]
    simp only [smul_eq_mul, mul_zero, zero_add, add_zero]
    have e := l.neg_prod
    rw [inner_product_sym]
    rw [inner_product_sym] at e
    have aa := mul_neg_of_neg_of_pos e (t 0).prop
    have ab := mul_neg_of_neg_of_pos aa (t 1).prop
    linarith
  · rw [v_addd, v_hmull]
    dsimp
    have e0 (i : Fin 2) : (↑(l.endpoints i) : vector) 0 > 0 := by
      have p := (l.endpoints i).prop
      rw [isFutureLightLike, isFuture] at p
      exact p.2
    dsimp
    exact add_pos (Real.mul_pos (t 0).prop (e0 0)) (Real.mul_pos (t 1).prop (e0 1))

noncomputable def normalized_sample_on_line_vector (l : Line) (t : Fin 2 → PReal) : vector :=
  normalized_time_like_vector (sample_on_line l t)

noncomputable def point_on_line (l : Line) (t : Fin 2 → PReal) : point :=
  ⟨ normalized_sample_on_line_vector l t,
    by
      apply normalized_time_like_vector_unit_time_like
      apply sample_on_line_future_time_like
  ⟩

def is_point_on_horosphere (p : point) (h : lightPoint) :=
  inner_product (↑p : vector) (↑h : vector) = -1

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
     is_point_on_horosphere (standard_ray (-log ↑t)) (standard_horosphere1 t ⟨-1, by linarith⟩) := by
  have p := point_on_standard_horosphere1_general t
  rw [is_point_on_horosphere]
  rw [is_point_on_horosphere] at p
  have dd : (⟨-1, by linarith⟩ : direction) = -(⟨1, by linarith⟩ : direction) := rfl
  have s := mirror_x_standard_horosphere t ⟨1, by linarith⟩
  rw [← dd] at s
  rw [← s]
  have ra := mirror_x_standard_ray (log t)
  rw [← ra]
  rw [← mirror_x_inner_product]
  exact p

theorem d1 (t0 : PReal) (t1 : PReal) :
  let horosphere1 := (standard_horosphere1 t0 ⟨ 1, by linarith⟩)
  let horosphere2 := (standard_horosphere1 t1 ⟨ -1, by linarith⟩)
  let pt0 := (standard_ray (log ↑t0))
  let pt1 := (standard_ray (-(log ↑t1)))
  distance pt0 pt1 = log (inner_product ↑horosphere1 ↑horosphere2) := by
    dsimp
    rw [distance]
    rw [standard_ray, standard_ray]
    rw [inner_product]
    simp only [neg_mul, neg_add_rev, neg_neg]
    rw [standard_ray_vector0, standard_ray_vector0,
        standard_ray_vector1, standard_ray_vector1,
        standard_ray_vector2, standard_ray_vector2,
        standard_ray_vector3, standard_ray_vector3]
    simp only [mul_zero, neg_zero, sinh_neg, mul_neg, neg_neg, cosh_neg, zero_add]
    rw [inner_product]
    rw [standard_horosphere1, standard_horosphere1]
    simp only [neg_mul]
    rw [standard_horosphere1_vector0, standard_horosphere1_vector0,
        standard_horosphere1_vector1, standard_horosphere1_vector1,
        standard_horosphere1_vector2, standard_horosphere1_vector2,
        standard_horosphere1_vector3, standard_horosphere1_vector3]
    cases' t0 with tt0 ttt0
    cases' t1 with tt1 ttt1
    dsimp
    simp only [one_mul, neg_mul, mul_neg, mul_zero, add_zero]
    rw [sinh_eq, sinh_eq, cosh_eq, cosh_eq]
    rw [arcosh]
    rw [exp_log ttt0]
    rw [exp_log ttt1]
    rw [exp_neg_log ⟨tt0,ttt0⟩]
    rw [exp_neg_log ⟨tt1,ttt1⟩]
    dsimp
    simp
    have a : ((tt0 - tt0⁻¹) / 2 * ((tt1 - tt1⁻¹) / 2) + (tt0 + tt0⁻¹) / 2 * ((tt1 + tt1⁻¹) / 2) +
      sqrt (1 - ((tt0 - tt0⁻¹) / 2 * ((tt1 - tt1⁻¹) / 2) + (tt0 + tt0⁻¹) / 2 * ((tt1 + tt1⁻¹) / 2)) ^ 2)) = (-(tt0 * tt1) + -(tt0 * tt1)) := by
      rw [sub_div]
      rw [sub_div]
      rw [sub_mul]
      rw [mul_sub]
      
    rw [a]

    






#check Real.cosh_sq
#check Real.sinh_arsinh
