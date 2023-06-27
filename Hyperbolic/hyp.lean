import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Vector
import Mathlib.Data.Fin.VecNotation
import Hyperbolic.Arcosh

import Mathlib.Data.Vector

open Real

set_option maxHeartbeats 0

#check Real.cosh_sq
#check Real.sinh_arsinh

namespace R13

def vector := Fin 4 → ℝ
def inner_product (a b : vector) : ℝ := -(a 0) * (b 0) + (a 1) * (b 1) + (a 2) * (b 2) + (a 3) * (b 3)

instance : Zero vector := ⟨ fun _ => 0⟩
instance : Add vector := ⟨ fun a b => fun i => (a i) + (b i)⟩
instance : Neg vector := ⟨ fun a => fun i => -(a i)⟩
instance : HMul ℝ vector vector := ⟨fun r v => fun i => r * (v i)⟩

class timeLikeVector (vec : vector) where
  timeLike : (inner_product vec vec) < 0

class lightLikeVector (vec : vector) where
  lightLike : (inner_product vec vec) = 0

class spaceLikeVector (vec : vector) where
  spaceLike : (inner_product vec vec) > 0

class futureVector (vec : vector) where
  future : (vec 0) > 0

class unitTimeLikeVector (vec : vector) where
  unitTimeLike : (inner_product vec vec) = -1

class unitSpaceLikeVector (vec : vector) where
  unitSpaceLike : (inner_product vec vec) = 1

instance {vec : vector} [u : unitTimeLikeVector vec] : timeLikeVector vec where
  timeLike := by
    rw [u.unitTimeLike]
    linarith

instance {vec : vector} [u : unitSpaceLikeVector vec] : spaceLikeVector vec where
  spaceLike := by
    rw [u.unitSpaceLike]
    linarith

def origin : vector := ![1,0,0,0]

instance : unitTimeLikeVector origin where
  unitTimeLike := by
    rw [inner_product]
    have v0 : origin 0 = 1 := rfl
    have v1 : origin 1 = 0 := rfl
    have v2 : origin 2 = 0 := rfl
    have v3 : origin 3 = 0 := rfl
    rw [v0, v1, v2, v3]
    simp

instance : futureVector origin where
  future := by
    have v0 : origin 0 = 1 := rfl
    rw [v0]
    linarith

noncomputable def normalized_time_like (v : vector) [timeLikeVector v] : vector :=
  (1 / sqrt (-(inner_product v v))) * v

--instance (v : vector) : unitTimeLikeVector (normalized_time_like v) where
--  unitTimeLike := by
    

end R13

open R13

noncomputable def distance (a b : vector) [unitTimeLikeVector a] [unitTimeLikeVector b] : ℝ  :=
    Real.arcosh (-(inner_product a b))

theorem zero_dis (a : vector) [u : unitTimeLikeVector a] : distance a a = 0 := by
  rw [distance]
  rw [u.unitTimeLike]
  simp
  rw [arcosh]
  simp

theorem zero_dis_origin : distance origin origin = 0 := zero_dis origin

structure Line where
  endpoints : Fin 2 → vector
  neg_prod : inner_product (endpoints 0).point (endpoints 1).point) < 0

def PReal := { r : ℝ // 0 < r }

def point_on_line (l : Line) (t : Fin 2 -> PReal) : FinitePoint :=
  ⟨by sorry, by sorry, by sorry⟩

noncomputable def standard_ray (t:ℝ) : FinitePoint := 
  let pt := ![cosh t, sinh t, 0, 0];
  ⟨
  pt,
  by 
     unfold [pt]
     rw [r13_product,
         pt,
         (rfl : (pt 0) = cosh t),
         (rfl : (pt 1) = sinh t),
         (rfl : (pt 2) = 0),
         (rfl : (pt 3) = 0)]
     simp only [neg_mul, mul_zero, add_zero]
     rw [← sq]
     rw [cosh_sq]
     rw [sq]
     simp,
  by 
    have e0 : (![cosh t, sinh t, 0, 0] 0) = cosh t := rfl
    rw [e0]
    exact cosh_pos t⟩




noncomputable def xx : Vec4 := ![cosh 1, sinh 1, 0, sin 4]

noncomputable def ddf := xx 2

theorem xxx : xx (Fin.succ (Fin.succ (Fin.succ 0))) = sin 4 := by
  rw [xx]
  rw [Matrix.vecCons]
  rw [Fin.cons]
  rw [Fin.cases_succ]
  rw [Matrix.vecCons]
  rw [Fin.cons]
  rw [Fin.cases_succ]
  rw [Matrix.vecCons]
  rw [Fin.cons]
  rw [Fin.cases_succ]
  rw [Matrix.vecCons]
  simp only [Fin.cons_zero]

theorem xxx2 : xx 3 = sin (2+2) := by
  rw [xx]
  rw [Matrix.vecCons, Fin.cons]
  have j : (3 : Fin 4) = Fin.succ (Fin.succ (Fin.succ 0)) := by simp
  rw [j]
  rw [Fin.cases_succ]
  rw [Matrix.vecCons]
  rw [Fin.cons]
  rw [Fin.cases_succ]
  rw [Matrix.vecCons]
  rw [Fin.cons]
  rw [Fin.cases_succ]
  rw [Matrix.vecCons]
  simp only [Fin.cons_zero]

  have h : (4 : ℝ)  = 2 + 2 := by
    linarith
  rw [h]

def c0 : Vec4 := ![1,0,0,0]

noncomputable def c1 : Vec4 := ![Real.cosh 1,Real.sinh 1,0,0]

def sub1 : Vec4
| 0     => 1
| 1     => 0
| 2     => 0
| 3     => 0

theorem foe : sub1 2 = 0 := rfl

theorem aabbba : (r13_product c1 c1) = -1 := by
  rw [r13_product]
  have a : (c1 0 = Real.cosh 1) := rfl
  have b : (c1 1 = Real.sinh 1) := rfl
  have c : (c1 2 = 0) := rfl
  have d : (c1 3 = 0) := rfl
  rw [a, b, c, d]

theorem aaa : (r13_product sub1 sub1) = -1 := by
  rw [r13_product]
  have a : (sub1 0 = 1) := rfl
  have b : (sub1 1 = 0) := rfl
  have c : (sub1 2 = 0) := rfl
  have d : (sub1 3 = 0) := rfl
  rw [a, b, c, d]
  simp




def j : FinitePoint := ⟨c0,
  by 
    rw [r13_product]
    rw [c0]
    simp only [Matrix.cons_val_zero, 
               Matrix.cons_val_one,
               Matrix.head_cons,
               Matrix.vecCons,
               Fin.cons,
               Fin.cases,
               Fin.induction,
               Nat.rec]
    simp
    rfl,
  by
    rw [c0]
    simp⟩

noncomputable def j2 : FinitePoint := ⟨c1,
  by 
    rw [r13_product]
    rw [c1]
    simp only [Matrix.cons_val_zero, 
               Matrix.cons_val_one,
               Matrix.head_cons,
               Matrix.vecCons,
               Fin.cons,
               Fin.cases,
               Fin.induction,
               Nat.rec]
    simp
    have helper : - (Real.cosh 1 * Real.cosh 1) + Real.sinh 1 * Real.sinh 1 = -1 := by
       library_search
    rw [helper]
    simp
    rfl,
  by
    rw [c1]
    have helper : Real.cosh 1 > 0 := by
       sorry
    rw [helper]
    simp,
    rfl⟩

