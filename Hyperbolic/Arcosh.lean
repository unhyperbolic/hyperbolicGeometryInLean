--import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
--import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace Real

noncomputable def arcosh (x : ℝ) :=
  log (x + sqrt (1 - x ^ 2))

end Real
