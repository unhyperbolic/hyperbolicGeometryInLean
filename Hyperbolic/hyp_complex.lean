import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Data.Vector
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Fin.VecNotation

namespace Complex

noncomputable def sqrt (z : ℂ) := if z = 0 then 0 else exp ((log z) / 2)

noncomputable def arcsinh (z : ℂ) : ℂ := log (z + sqrt (z^2 + 1))
noncomputable def arccosh (z : ℂ) : ℂ := log (z + sqrt (z^2 - 1))

theorem sq_sqrt (z : ℂ) : sqrt (z)^2 = z := by
  rw [sqrt]
  cases' (eq_or_ne z 0) with z_zero z_nonzero
  · rw [if_pos z_zero, z_zero]
    simp only [ne_eq, zero_pow']
  · rw [if_neg z_nonzero, sq, ← exp_add, add_halves']
    exact Complex.exp_log z_nonzero

end Complex

namespace Real

noncomputable def arcsinh (x : ℝ) : ℝ := (Complex.arcsinh x).re
noncomputable def arccosh (x : ℝ) : ℝ := (Complex.arccosh x).re

theorem sinh_arsinh

end Real


set_option maxHeartbeats 0


 

-- noncomputable def arcsinh (x : ℝ) : ℝ := Real.log ( x + Real.sqrt (x^2 + 1) )
-- noncomputable def arccosh (x : ℝ) : ℝ := Real.log ( x + Real.sqrt (x^2 - 1) )

#check Complex.cosh_sq
#check Real.cosh_sq

theorem sinh_inv (x : ℝ) : arcsinh (Real.sinh x) = x := by
  rw [Real.sinh]


def Vec4 := Fin 4 → ℝ
def r13_product (a b : Vec4) : ℝ := -(a 0) * (b 0) + (a 1) * (b 1) + (a 2) * (b 2) + (a 3) * (b 3)



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


@[ext]
structure FinitePoint where
  point : Vec4
  hyperboloid : (r13_product point point) = -1
  positivity: (point 0) > 0

noncomputable def d' (a b : FinitePoint) : ℝ  := 
  arccosh (-(r13_product a.point b.point))

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

