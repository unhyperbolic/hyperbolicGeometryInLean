--import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
--import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

namespace Real

def PReal := { r : ℝ // 0 < r }

instance : Coe PReal ℝ := ⟨ fun p => p.val ⟩

#check cosh_eq
#check mul_left_cancel_iff_of_pos

@[reducible]
noncomputable def arcosh (x : ℝ) :=
  log (x + sqrt (x ^ 2 - 1))

lemma cosh_arcosh (x : ℝ) (h : x ≥ 1) : cosh (arcosh x) = x := by
  rw [cosh_eq, arcosh]
  have pos : x + sqrt (x ^ 2 - 1) > 0 := by
    apply add_pos_of_pos_of_nonneg
    . linarith
    . exact sqrt_nonneg _
  rw [exp_log pos, exp_neg, exp_log pos]
  simp
  rw [div_eq_iff (by linarith)]
  apply add_eq_of_eq_neg_add
  rw [← one_mul (-(x + sqrt (x ^ 2 - 1)) + x * 2)]
  have nzero : x + sqrt (x ^ 2 - 1) ≠ 0 := by linarith
  nth_rw 2 [← inv_mul_cancel nzero]
  have inzero : (x + sqrt (x ^ 2 - 1))⁻¹ > 0 := inv_pos.mpr pos
  nth_rw 1 [← mul_one (x + sqrt (x ^ 2 - 1))⁻¹]
  rw [mul_assoc, mul_left_cancel_iff_of_pos inzero]
  ring_nf
  rw [sq_sqrt]
  simp
  have h' : -1 + x^2 = (x + 1) * (x - 1) := by ring
  rw [h']
  apply mul_nonneg
  . linarith
  . linarith

lemma arcosh_cosh (x : ℝ) (h : x ≥ 0) : arcosh (cosh x) = x := by
  rw [arcosh, cosh_sq]
  simp
  rw [sqrt_sq (sinh_nonneg_iff.mpr h)]
  rw [cosh_eq, sinh_eq]
  ring_nf
  exact log_exp x

#check sqrt_sq_eq_abs

lemma arcosh_cosh_neg (x : ℝ) (h : x < 0) : arcosh (cosh x) = -x := by
  rw [arcosh, cosh_sq]
  simp
  rw [sqrt_sq_eq_abs, abs_of_neg ]
  rw [cosh_eq, sinh_eq]
  ring_nf
  exact log_exp (-x)
  apply neg_of_neg_pos
  rw [← sinh_neg]
  rw [sinh_pos_iff]
  linarith

lemma arcosh_eq {x y : ℝ} (hy : y ≥ 0) : x = cosh y → arcosh x = y := by
  intro h'
  rw [h']
  exact arcosh_cosh y hy

lemma arcosh_eq_neg {x y : ℝ} (hy : y < 0) : x = cosh y → arcosh x = -y := by
  intro h'
  rw [h']
  apply arcosh_cosh_neg y hy

end Real
