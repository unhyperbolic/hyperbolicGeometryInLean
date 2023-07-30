import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Topology.MetricSpace.Basic
import Hyperbolic.Arcosh

open BigOperators

namespace PseudoEuclideanSpace

def Sign := {r : ℝ // r = 1 ∨ r = -1}
instance : Coe Sign ℝ := ⟨ fun r => r.val ⟩

def PlusSign  : Sign := ⟨ 1, by left;  rfl⟩
def MinusSign : Sign := ⟨-1, by right; rfl⟩

end PseudoEuclideanSpace

@[reducible, nolint unusedArguments]
def PseudoEuclideanSpace {f : Type _} [Fintype f] (_: f → PseudoEuclideanSpace.Sign) := f → ℝ

instance : AddCommGroup (@PseudoEuclideanSpace f k signature) := inferInstanceAs <| AddCommGroup (f → ℝ)
noncomputable instance : Module ℝ (@PseudoEuclideanSpace f k signature) := by delta PseudoEuclideanSpace; infer_instance

instance : Inner ℝ (@PseudoEuclideanSpace f k signature) :=
  ⟨fun v w => ∑ i, (v i) * (w i) * (signature i)⟩

def MinkowskiSpaceSignature (n : ℕ) : Fin n → PseudoEuclideanSpace.Sign :=
    fun i => if (↑i : ℕ) == 0 then PseudoEuclideanSpace.MinusSign else PseudoEuclideanSpace.PlusSign

def MinkowskiSpace (d : ℕ+) := PseudoEuclideanSpace (MinkowskiSpaceSignature d)

instance : Inner ℝ (MinkowskiSpace d) := by delta MinkowskiSpace; infer_instance

def TimeLike (v : MinkowskiSpace d) : Prop := ⟪v,v⟫_ℝ < 0
def UnitTimeLike (v : MinkowskiSpace d) : Prop := ⟪v,v⟫_ℝ = -1
def LightLike (v : MinkowskiSpace d) : Prop := ⟪v,v⟫_ℝ = 0
def SpaceLike (v : MinkowskiSpace d) : Prop := ⟪v,v⟫_ℝ > 0
def UnitSpaceLike (v : MinkowskiSpace d) : Prop := ⟪v,v⟫_ℝ =1

def Future (v : MinkowskiSpace d) : Prop := v 0 > 0

def Hyperboloid (d : ℕ+) := { p : MinkowskiSpace d // TimeLike p ∧ Future p}

noncomputable instance : Dist (MinkowskiSpace d) :=
  ⟨fun v w => Real.arcosh (-(⟪v, w⟫_ℝ))⟩

