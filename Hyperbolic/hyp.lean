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

-- IS THIS A GOOD IDEA?
class futureUnitTimeLikeVector (vec : vector) extends futureVector vec, unitTimeLikeVector vec

noncomputable def normalized_time_like (v : vector) [timeLikeVector v] [futureVector v] : vector :=
  (1 / sqrt (-(inner_product v v))) * v
  
-- THE FOLLOWING DOESN"T SEEM TO WORK?
-- instance (v : vector) : unitTimeLikeVector (normalized_time_like v) where
--  unitTimeLike := by sorry

-- noncomputable def normalized_time_like2 (v : vector) 
--    [t: timeLikeVector v] [f: futureVector v] : futureUnitTimeLikeVector := 
-- WHAT DO I WRITE HERE?   

end R13

open R13

noncomputable def distance (a b : vector) [unitTimeLikeVector a] [futureVector a] [unitTimeLikeVector b] [futureVector b] : ℝ  :=
    Real.arcosh (-(inner_product a b))

theorem zero_dis (a : vector) [u : unitTimeLikeVector a] [futureVector a] : distance a a = 0 := by
  rw [distance]
  rw [u.unitTimeLike]
  rw [arcosh]
  simp

theorem zero_dis_origin : distance origin origin = 0 := zero_dis origin

structure Line where
  endpoints : Fin 2 → vector -- NEED TO INDICATE THAT THESE ARE FUTURE AND UNIT TIME LIKE
  neg_prod : inner_product (endpoints 0) (endpoints 1) < 0

def PReal := { r : ℝ // 0 < r }

def point_on_line (l : Line) (t : Fin 2 -> PReal) : vector :=
  normalized_time_like (((t 0).val * (l.endpoints 0)) + ((t 1).val * (l.endpoints 1)))

set_option maxHeartbeats 0

#check Real.cosh_sq
#check Real.sinh_arsinh
