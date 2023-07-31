import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Topology.MetricSpace.Basic
import Hyperbolic.Arcosh
import Mathlib.Init.Set

-- set_option maxHeartbeats 0

open BigOperators

namespace PseudoEuclideanSpace

def Sign := {r : ℝ // r = 1 ∨ r = -1}
instance : Coe Sign ℝ := ⟨ fun r => r.val ⟩

def Plus  : Sign := ⟨ 1, by left;  rfl⟩
def Minus : Sign := ⟨-1, by right; rfl⟩

end PseudoEuclideanSpace

@[reducible, nolint unusedArguments]
def PseudoEuclideanSpace {f : Type _} [Fintype f] [DecidableEq f] (_: f → PseudoEuclideanSpace.Sign) := f → ℝ

instance : AddCommGroup (@PseudoEuclideanSpace f k b signature) := inferInstanceAs <| AddCommGroup (f → ℝ)
noncomputable instance : Module ℝ (@PseudoEuclideanSpace f k b signature) := by delta PseudoEuclideanSpace; infer_instance

instance : Inner ℝ (@PseudoEuclideanSpace f k b signature) :=
  ⟨fun v w => ∑ i, (v i) * (w i) * (signature i)⟩

namespace PseudoEuclideanSpace

def BasisVector {f : Type _} [k: Fintype f] [b : DecidableEq f] (signature: f → PseudoEuclideanSpace.Sign) (i : f) : (@PseudoEuclideanSpace f k b signature) :=
  (fun (j : f) => if i = j then 1 else 0)

theorem inner_product_basis_vector {f : Type _} [k: Fintype f] [b : DecidableEq f] { signature: f → PseudoEuclideanSpace.Sign } { u : PseudoEuclideanSpace signature} {i : f}:
    inner u (BasisVector signature i) = (u i) * (signature i) :=
  by
    rw [inner, instInnerRealPseudoEuclideanSpace]
    simp only [Pi.add_apply]
    have s : ∑ i_1 : f, u i_1 * BasisVector signature i i_1 * ↑(signature i_1) = u i  * BasisVector signature i i * ↑(signature i) := by
      apply Finset.sum_eq_single_of_mem
      · exact Finset.mem_univ i
      · intro iu _ it
        rw [BasisVector]
        symm at it
        rw [if_neg it]
        simp only [mul_zero, zero_mul]
    have k : BasisVector signature i i = 1 := by
      rw [BasisVector]
      rw [if_pos]
      rfl
    rw [s, k]
    simp only [mul_one]

theorem inner_product_sum {f : Type _} [Fintype f] [b : DecidableEq f] {signature: f → PseudoEuclideanSpace.Sign} [k: Fintype f] (u v : (@PseudoEuclideanSpace f k b signature)): 
      inner u v = ∑ i : f, u i * v i * ↑(signature i) := by
  rw [inner, instInnerRealPseudoEuclideanSpace]

end PseudoEuclideanSpace

def PseudoEuclideanSpaceBilinearForm : BilinForm ℝ (@PseudoEuclideanSpace f k b signature) := {
    bilin := fun v w => ⟪v, w⟫_ℝ
    bilin_add_left := by
      dsimp
      intro x y z
      rw [PseudoEuclideanSpace.inner_product_sum]
      rw [PseudoEuclideanSpace.inner_product_sum]
      rw [PseudoEuclideanSpace.inner_product_sum]
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

class PseudoInnerProductSpace (𝕜 : Type _) (E : Type _) [IsROrC 𝕜] [AddCommGroup E] [Module 𝕜 E] [Inner 𝕜 E] extends
   Inner 𝕜 E where
   bilin_form : BilinForm 𝕜 E
   symm : ∀ (u v : E), inner u v = inner v u
   nondeg : ∀ (u : E), (∀ (v : E), inner u v = 0) → u = 0

noncomputable instance : PseudoInnerProductSpace ℝ (@PseudoEuclideanSpace f k b signature) :=
  ⟨PseudoEuclideanSpaceBilinearForm,
    by
      intro u v
      rw [PseudoEuclideanSpace.inner_product_sum]
      apply congrArg (Finset.sum Finset.univ)
      refine Eq.symm (funext ?h)
      intro x
      linarith,
    by
      intro u i
      apply funext
      dsimp
      intro j
      have p := i (PseudoEuclideanSpace.BasisVector signature j)
      rw [PseudoEuclideanSpace.inner_product_basis_vector] at p
      symm at p
      have := zero_eq_mul.mp p
      cases' this with r s
      · exact r
      · exfalso
        cases' (signature j).2 with d d
        · rw [d] at s
          linarith
        · rw [d] at s
          linarith
      ⟩

def MinkowskiSpaceSignature (d : ℕ) : Fin d → PseudoEuclideanSpace.Sign :=
    fun i => if (↑i : ℕ) = 0 then PseudoEuclideanSpace.Minus else PseudoEuclideanSpace.Plus

def MinkowskiSpace (d : ℕ+) := PseudoEuclideanSpace (MinkowskiSpaceSignature d)

instance : Inner ℝ (MinkowskiSpace d) := by delta MinkowskiSpace; infer_instance

def TimeLike (v : MinkowskiSpace d) : Prop := ⟪v,v⟫_ℝ < 0
def UnitTimeLike (v : MinkowskiSpace d) : Prop := ⟪v,v⟫_ℝ = -1
def LightLike (v : MinkowskiSpace d) : Prop := ⟪v,v⟫_ℝ = 0
def SpaceLike (v : MinkowskiSpace d) : Prop := ⟪v,v⟫_ℝ > 0
def UnitSpaceLike (v : MinkowskiSpace d) : Prop := ⟪v,v⟫_ℝ =1

def Future (v : MinkowskiSpace d) : Prop := v 0 > 0

def Hyperboloid (d : ℕ) := { p : MinkowskiSpace ⟨d + 1, by linarith⟩ // TimeLike p ∧ Future p}

instance : Coe (Hyperboloid (d : ℕ)) (MinkowskiSpace ⟨d + 1, by linarith⟩) := ⟨ fun r => r.val ⟩

instance : Inner ℝ (Hyperboloid d) := ⟨fun v w => ⟪v.val,w.val⟫_ℝ⟩

noncomputable instance : Dist (Hyperboloid d) :=
  ⟨fun v w => Real.arcosh (-⟪v, w⟫_ℝ)⟩

