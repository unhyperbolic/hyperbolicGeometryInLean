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

def vector := Fin 4 → ℝ

instance : Zero vector := ⟨ fun _ => 0⟩
instance : Add vector := ⟨ fun a b => fun i => (a i) + (b i) ⟩
instance : Neg vector := ⟨ fun a => fun i => -(a i)⟩
instance : HMul ℝ vector vector := ⟨fun r v => fun i => r * (v i)⟩

def inner_product (a b : vector) : ℝ := -(a 0) * (b 0) + (a 1) * (b 1) + (a 2) * (b 2) + (a 3) * (b 3)

theorem v_add (a b : vector) : a + b = fun i => (a i) + (b i) := rfl
theorem v_hmul (r : ℝ) (a : vector) : r * a = fun i => r * (a i) := rfl

set_option maxHeartbeats 0

theorem inner_product_lin0 (a b c : vector) : 
    inner_product (a + b) c = inner_product a c + inner_product b c := by
  rw [inner_product]
  rw [inner_product]
  rw [inner_product]
  rw [v_add]
  dsimp
  linarith

theorem inner_product_lina0 (a : ℝ) (b c : vector) :
    inner_product (a * b) c = a * inner_product b c := by
  rw [inner_product]
  rw [inner_product]
  rw [v_hmul]
  dsimp
  linarith

theorem inner_product_lin1 (a b c : vector) : 
    inner_product a (b + c) = inner_product a b + inner_product a c := by
  rw [inner_product]
  rw [inner_product]
  rw [inner_product]
  rw [v_add]
  dsimp
  linarith

theorem inner_product_lina1 (a : ℝ) (b c : vector) :
    inner_product b (a * c) = a * inner_product b c := by
  rw [inner_product]
  rw [inner_product]
  rw [v_hmul]
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
  (1 / sqrt (-(inner_product v v))) * v

theorem aaa (a : ℝ) (p: 0 < a) :  a⁻¹    * a = 1  := by
  refine inv_mul_cancel ?h
  exact ne_of_gt p

theorem aa (a b : ℝ) (p : a > 0) (q : b > 0) : a * b > 0 := by
  exact Real.mul_pos p q


theorem normalized_time_like_vector_unit_time_like (v : vector) (p : isFutureTimeLike v) : 
       isFutureUnitTimeLike (normalized_time_like_vector v) := by
  rw [normalized_time_like_vector, isFutureUnitTimeLike]
  constructor
  · rw [isFutureTimeLike] at p
    rw [isUnitTimeLike]
    rw [inner_product_lina0, inner_product_lina1]
    simp
    have p1 := p.1
    rw [isTimeLike] at p1
    have p2 := neg_pos.mpr p1
    have p3 := inv_pos.mpr p2
    have p4 := LT.lt.le p3
    have p5 := ne_of_gt p2
    have p6 : inner_product v v ≠ 0 := by exact Iff.mp neg_ne_zero p5
    rw [← sqrt_inv]
    rw [← mul_assoc]
    rw [mul_self_sqrt p4]
    rw [neg_eq_neg_one_mul]
    rw [mul_inv]
    rw [mul_assoc]
    rw [inv_mul_cancel p6]
    simp
    exact inv_neg_one
  · rw [isFuture]
    rw [isFutureTimeLike, isTimeLike, isFuture] at p
    rw [v_hmul]
    dsimp
    have p1 := neg_pos.mpr p.1
    have p2 := p.2
    have p3 := sqrt_pos.mpr p1
    have p4 := one_div_pos.mpr p3
    exact Real.mul_pos p4 p2

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
  (↑(t 0) : ℝ) * (↑(l.endpoints 0) : vector) +
  (↑(t 1) : ℝ) * (↑(l.endpoints 1) : vector)

theorem aaa (a: ℝ) (b:ℝ) (c : a < 0) (d : b > 0) : a * b < 0 := by
  exact mul_neg_of_neg_of_pos c d

theorem sample_on_line_future_time_like (l : Line) (t : Fin 2 → PReal) :
            isFutureTimeLike (sample_on_line l t) := by
  rw [isFutureTimeLike, isTimeLike, isFuture, sample_on_line]
  constructor
  · rw [inner_product_lin0, inner_product_lina0, inner_product_lin1, inner_product_lina1]
    rw [inner_product_lina0, inner_product_lin1, inner_product_lina1]
    rw [inner_product_lina1]
    rw [inner_product_lina1]
    have a := (l.endpoints 0).prop
    rw [isFutureLightLike] at a
    have b := a.1
    rw [isLightLike] at b
    rw [b]
    have a1 := (l.endpoints 1).prop
    rw [isFutureLightLike] at a1
    have b1 := a1.1
    rw [isLightLike] at b1
    rw [b1]
    simp
    have e := l.neg_prod
    rw [inner_product_sym]
    rw [inner_product_sym] at e
    have aa := mul_neg_of_neg_of_pos e (t 0).prop
    have ab := mul_neg_of_neg_of_pos aa (t 1).prop
    linarith
  · rw [v_add, v_hmul]
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


#check Real.cosh_sq
#check Real.sinh_arsinh
