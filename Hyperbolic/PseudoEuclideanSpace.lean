import Mathlib.Analysis.InnerProductSpace.Basic

open BigOperators

namespace PseudoEuclideanSpace

def Sign := {r : ℝ // r = 1 ∨ r = -1}
instance : Coe Sign ℝ := ⟨ fun r => r.val ⟩

def PlusSign  : Sign := ⟨ 1, by left;  rfl⟩
def MinusSign : Sign := ⟨-1, by right; rfl⟩

end PseudoEuclideanSpace

@[reducible, nolint unusedArguments]
def PseudoEuclideanSpace {f : Type _} [Fintype f] (signature: f → PseudoEuclideanSpace.Sign) := f → ℝ

instance : AddCommGroup (@PseudoEuclideanSpace f k signature) := inferInstanceAs <| AddCommGroup (f → ℝ)
noncomputable instance : Module ℝ (@PseudoEuclideanSpace f k signature) := by delta PseudoEuclideanSpace; infer_instance

instance : Inner ℝ (@PseudoEuclideanSpace f k signature) :=
  ⟨fun v w => ∑ i, (v i) * (w i) * (signature i)⟩

def MinkowskiSpaceSignature (n : ℕ) : Fin n → PseudoEuclideanSpace.Sign :=
    fun i => if (↑i : ℕ) == 0 then PseudoEuclideanSpace.MinusSign else PseudoEuclideanSpace.PlusSign

def MinkowskiSpace (d : ℕ) := PseudoEuclideanSpace (MinkowskiSpaceSignature d)
