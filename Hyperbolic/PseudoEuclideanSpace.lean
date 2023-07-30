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

def PseudoEuclideanSpaceBilinearForm : BilinForm ℝ (@PseudoEuclideanSpace f k signature) := {
    bilin := fun v w => ⟪v, w⟫_ℝ
    bilin_add_left := by
      dsimp
      rw [inner, instInnerRealPseudoEuclideanSpace]
      simp only [Pi.add_apply]
      intro x y z
      simp [← Finset.sum_add_distrib]
      apply congrArg (Finset.sum Finset.univ)
      refine Eq.symm (funext ?h)
      intro x1
      rw [add_mul]
      rw [add_mul]
    bilin_smul_left := by
      dsimp
      rw [inner, instInnerRealPseudoEuclideanSpace]
      simp only [Pi.add_apply]
      simp [Finset.mul_sum]
      intro a x y
      apply congrArg (Finset.sum Finset.univ)
      refine Eq.symm (funext ?h)
      intro x1
      linarith
    bilin_add_right := by
      dsimp
      [inner, instInnerRealPseudoEuclideanSpace]
      simp only [Pi.add_apply]
      intro x y z
      simp [← Finset.sum_add_distrib]
      apply congrArg (Finset.sum Finset.univ)
      refine Eq.symm (funext ?h)
      intro x1
      rw [mul_add]
      rw [add_mul]
    bilin_smul_right := by
      dsimp
      rw [inner, instInnerRealPseudoEuclideanSpace]
      simp only [Pi.add_apply]
      simp [Finset.mul_sum]
      intro a x y
      apply congrArg (Finset.sum Finset.univ)
      refine Eq.symm (funext ?h)
      intro x1
      linarith
  }

-- set_option maxHeartbeats 0

class PseudoInnerProductSpace (𝕜 : Type _) (E : Type _) [IsROrC 𝕜] [AddCommGroup E] [Module 𝕜 E] [Inner 𝕜 E] extends
   Inner 𝕜 E where
   bilin_form : BilinForm 𝕜 E
   symm : ∀ (u v : E), inner u v = inner v u
   nondeg : ∀ (u : E), (∀ (v : E), inner u v = 0 → u = 0)

noncomputable instance : PseudoInnerProductSpace ℝ (@PseudoEuclideanSpace f k signature) :=
  ⟨PseudoEuclideanSpaceBilinearForm,
    by
      intro u v
      rw [inner, instInnerRealPseudoEuclideanSpace]
      simp only [Pi.add_apply]
      apply congrArg (Finset.sum Finset.univ)
      refine Eq.symm (funext ?h)
      intro x
      linarith
   , by sorry⟩
   

def MinkowskiSpaceSignature (d : ℕ) : Fin d → PseudoEuclideanSpace.Sign :=
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
  ⟨fun v w => Real.arcosh (-⟪v, w⟫_ℝ)⟩

