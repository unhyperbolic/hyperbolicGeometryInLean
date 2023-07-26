import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Vector
import Mathlib.Data.Fin.VecNotation
import Mathlib.LinearAlgebra.BilinearForm
import Mathlib.Algebra.BigOperators.Basic
import Hyperbolic.Arcosh

import Mathlib.Data.Vector

open Real BigOperators

def Sign := {r : ℝ // r = 1 ∨ r = -1}
instance : Coe Sign ℝ := ⟨ fun r => r.val ⟩

structure PseudoEuclideanSpace where
  dim : Nat
  signature : Fin dim → Sign
  form : BilinForm ℝ (Fin dim → ℝ) := {
    bilin := fun v w => ∑ i, (v i) * (w i) * (signature i)
    bilin_add_left := sorry
    bilin_smul_left := sorry
    bilin_add_right := sorry
    bilin_smul_right := sorry
  }

namespace Minkowski

@[reducible]
def MinkowskiSpace : PseudoEuclideanSpace where
  dim := 4
  signature := ![⟨-1, by right; rfl⟩, ⟨1, by left; rfl⟩, ⟨1, by left; rfl⟩, ⟨1, by left; rfl⟩]

@[reducible]
def MVector := Fin 4 → ℝ
deriving AddCommGroup
noncomputable instance : Module ℝ MVector := by delta MVector; infer_instance
def MForm := MinkowskiSpace.form

theorem MForm_eval (v : MVector) (w : MVector) : 
  MForm v w = ∑ i, (v i) * (w i) * (MinkowskiSpace.signature i) := by rfl

theorem MForm_sym (v w : MVector) : MForm v w = MForm w v := by
  rw [MForm_eval, MForm_eval, Fin.sum_univ_four, Fin.sum_univ_four]
  ring

def TimeLike (v : MVector) : Prop := MForm v v < 0
def UnitTimeLike (v : MVector) : Prop := MForm v v = -1
def LightLike (v : MVector) : Prop := MForm v v = 0
def SpaceLike (v : MVector) : Prop := MForm v v > 0
def UnitSpaceLike (v : MVector) : Prop := MForm v v =1

def Future (v : MVector) : Prop := v 0 > 0

theorem UTL_TL (v : MVector) : UnitTimeLike v → TimeLike v := by
  rw [TimeLike, UnitTimeLike]
  intro h
  rw [h]
  linarith

theorem USL_SL (v : MVector) : UnitSpaceLike v → SpaceLike v := by
  rw [SpaceLike, UnitSpaceLike] 
  intro h
  rw [h]
  linarith

@[reducible]
def origin : MVector := ![1,0,0,0]
theorem origin0 : origin 0 = 1 := by rfl
theorem origin1 : origin 1 = 0 := by rfl
theorem origin2 : origin 2 = 0 := by rfl
theorem origin3 : origin 3 = 0 := by rfl

theorem origin_UTL : UnitTimeLike origin := by
  rw [UnitTimeLike, MForm_eval origin origin, Fin.sum_univ_four]
  rw [origin0, origin1, origin2, origin3]
  simp

theorem origin_Future : Future origin := by
  rw [Future, origin0]
  exact one_pos

noncomputable def normalize_TL (v : MVector) :=
  (sqrt (- MForm v v))⁻¹ • v 

theorem normalize_TL_UTL (v : MVector) (hv : TimeLike v) : UnitTimeLike (normalize_TL v) := by
  rw [TimeLike] at hv
  rw [UnitTimeLike, normalize_TL]
  rw [BilinForm.smul_left, BilinForm.smul_right]
  rw [← mul_assoc, ← mul_inv, mul_self_sqrt (by linarith)]
  rw [neg_eq_neg_one_mul, mul_inv, mul_assoc]
  rw [inv_mul_cancel (by linarith)]
  norm_num

theorem smul_MVector {r : Real} {v : MVector} : ∀ i, (r • v) i = r * (v i) := by intro i; rfl
theorem add_MVector {v w : MVector} : ∀ i, (v + w) i = v i + w i := by intro i; rfl

theorem scale_Future {r : Real} (hr : r > 0) (hv : Future v) : Future (r • v) := by
  rw [Future] at hv
  rw [Future]
  rw [smul_MVector 0]
  exact Real.mul_pos hr hv

theorem normalize_TL_Future (v : MVector) (hvf : Future v) (hvt : TimeLike v) :
  Future (normalize_TL v) := by
    apply scale_Future _ hvf
    apply inv_pos_of_pos
    apply sqrt_pos_of_pos
    rw [TimeLike] at hvt
    linarith

@[reducible]
def MPoint := { v : MVector // UnitTimeLike v ∧ Future v}
instance : Coe MPoint MVector := ⟨ fun v => v.val ⟩
@[reducible]
def LightPoint := { v : MVector // LightLike v ∧ Future v}
instance : Coe LightPoint MVector := ⟨ fun v => v.val ⟩  

noncomputable def normalized_TL (v : MVector) (hvt : TimeLike v) (hvf : Future v) : MPoint := 
  ⟨ normalize_TL v, by
    constructor
    . exact normalize_TL_UTL v hvt
    . exact normalize_TL_Future v hvf hvt ⟩

noncomputable def Distance (v w : MPoint) : ℝ := Real.arcosh (- MForm v w)

def Origin : MPoint := ⟨ origin, ⟨origin_UTL, origin_Future⟩ ⟩

theorem self_dist (v : MPoint) : Distance v v = 0 := by
  rw [Distance, Real.arcosh, v.prop.1]
  simp

@[reducible]
structure Line where
  endpoints : Fin 2 → LightPoint
  neg_prod : MForm (endpoints 0) (endpoints 1) < 0

noncomputable def PointOnLine (l : Line) (t : Fin 2 → PReal) : MVector :=
  (t 0 : Real) • (l.endpoints 0 : MVector) +
  (t 1 : Real) • (l.endpoints 1 : MVector)

lemma endpoint_form (l : Line) (i : Fin 2) :
  MForm (l.endpoints i) (l.endpoints i) = 0 := by
  have h := (l.endpoints i).prop
  rw [LightLike, Future] at h
  exact h.1

theorem lines_timelike (l : Line) (t : Fin 2 → PReal) :
  TimeLike (PointOnLine l t) := by
  rw [TimeLike, PointOnLine]
  simp; rw [endpoint_form, endpoint_form, MForm_sym]; simp 
  have _ := l.neg_prod
  ring_nf
  apply mul_neg_of_neg_of_pos _ (by linarith)
  rw [mul_assoc]
  apply mul_neg_of_pos_of_neg (t 0).prop
  exact mul_neg_of_pos_of_neg (t 1).prop l.neg_prod

lemma lines_future (l : Line) (t : Fin 2 → PReal) : Future (PointOnLine l t) := by
  rw [Future, PointOnLine, add_MVector, smul_MVector, smul_MVector]
  apply add_pos <;> apply mul_pos
  exact (t 0).prop
  exact (l.endpoints 0).prop.2
  exact (t 1).prop
  exact (l.endpoints 1).prop.2

noncomputable def MPoint_on_line (l : Line) (t : Fin 2 → PReal) : MPoint :=
  ⟨normalize_TL (PointOnLine l t), by
    constructor
    . exact normalize_TL_UTL (PointOnLine l t) (lines_timelike l t)
    . exact normalize_TL_Future (PointOnLine l t) (lines_future l t) (lines_timelike l t)
  ⟩

def HPoint (v : MPoint) (w : LightPoint) : Prop := MForm v w = -1

noncomputable def RayVector (t : ℝ) : MVector := ![cosh t, sinh t, 0, 0]
lemma RayVector0 (t : ℝ) : RayVector t 0 = cosh t := rfl
lemma RayVector1 (t : ℝ) : RayVector t 1 = sinh t := rfl
lemma RayVector2 (t : ℝ) : RayVector t 2 = 0 := rfl
lemma RayVector3 (t : ℝ) : RayVector t 3 = 0 := rfl

noncomputable def MRay (t : ℝ) : MPoint := ⟨RayVector t, by
  constructor
  . rw [UnitTimeLike, MForm_eval, Fin.sum_univ_four]
    rw [RayVector0, RayVector1, RayVector2, RayVector3]
    rw [← sq, ← sq, Real.cosh_sq]
    simp
  . rw [Future, RayVector0]
    exact Real.cosh_pos t
  ⟩

def HVector (t s : ℝ) : MVector := ![t, s * t, 0, 0]
lemma HVector0 (t s : ℝ) : HVector t s 0 = t := rfl
lemma HVector1 (t s : ℝ) : HVector t s 1 = s * t := rfl
lemma HVector2 (t s : ℝ) : HVector t s 2 = 0 := rfl
lemma HVector3 (t s : ℝ) : HVector t s 3 = 0 := rfl

@[reducible]
def Direction := { r : ℝ // r^2 = 1 }
instance : Coe Direction ℝ := ⟨ fun r => r.val ⟩

instance : Neg Direction := ⟨fun r => ⟨-r, by
  rw [neg_sq]
  exact r.prop
  ⟩ ⟩

def HLightPoint (t : PReal) (s : Direction) : LightPoint := ⟨ HVector t s, by
  rw [LightLike, Future]
  constructor
  . rw [MForm_eval, Fin.sum_univ_four]
    rw [HVector0, HVector1, HVector2, HVector3]
    simp; ring_nf
    rw [s.prop]
    ring
  . rw [HVector0]
    exact t.prop
  ⟩

theorem horosphere_point1 : HPoint (MRay 0) (HLightPoint ⟨1, by linarith⟩ ⟨1, by linarith⟩) := by
  rw [HPoint, MForm_eval, Fin.sum_univ_four, MRay, HLightPoint]
  simp
  rw [RayVector0, RayVector1, RayVector2, RayVector3]
  rw [HVector0, HVector1, HVector2, HVector3]
  simp

def MirrorX (v : MVector) := ![v 0, -(v 1), v 2, v 3]
lemma MirrorX0 (v : MVector) : (MirrorX v) 0 = v 0 := rfl
lemma MirrorX1 (v : MVector) : (MirrorX v) 1 = -(v 1) := rfl
lemma MirrorX2 (v : MVector) : (MirrorX v) 2 = v 2 := rfl
lemma MirrorX3 (v : MVector) : (MirrorX v) 3 = v 3 := rfl

theorem mirrorx_MForm (v w : MVector) : MForm (MirrorX v) (MirrorX w) = MForm v w := by
  rw [MForm_eval, Fin.sum_univ_four]
  rw [MForm_eval, Fin.sum_univ_four]
  rw [MirrorX0, MirrorX1, MirrorX2, MirrorX3]
  rw [MirrorX0, MirrorX1, MirrorX2, MirrorX3]
  simp

theorem mirrorx_MRay (t : ℝ) : MirrorX (MRay t) = MRay (-t) := by
  rw [MirrorX, MRay, MRay]
  simp
  rw [RayVector0, RayVector1, RayVector2, RayVector3, RayVector]
  simp

theorem mirrorx_HLightPoint (t : PReal) (d : Direction) :
  MirrorX (HLightPoint t d) = HLightPoint t (-d) := by
  rw [MirrorX, HLightPoint, HLightPoint]
  simp
  rw [HVector0, HVector1, HVector2, HVector3, HVector]
  rw [← neg_mul]
  rfl

theorem exp_neg_log (t : PReal) : exp (-log t) = 1/t := by
  rw [exp_neg (log t), exp_log t.prop]
  simp
  
theorem horosphere_point_general (t : PReal) :
  HPoint (MRay (log t)) (HLightPoint t ⟨1, by linarith⟩) := by
  rw [HPoint, MRay, HLightPoint]
  rw [MForm_eval, Fin.sum_univ_four]
  simp
  rw [RayVector0, RayVector1, RayVector2, RayVector3, HVector]
  simp
  rw [← neg_mul, cosh_log t.prop, sinh_log t.prop]
  ring_nf
  rw [mul_inv_cancel]
  linarith [t.prop]

theorem horosphere_point_general_neg (t : PReal) : 
  HPoint (MRay (-log t)) (HLightPoint t ⟨-1, by linarith⟩) := by
  rw [HPoint, MRay, HLightPoint]
  rw [MForm_eval, Fin.sum_univ_four]
  simp
  rw [RayVector0, RayVector1, RayVector2, RayVector3, HVector]
  simp
  rw [← neg_mul, cosh_log t.prop, sinh_log t.prop]
  ring_nf
  rw [mul_inv_cancel]
  linarith [t.prop]

def HLP1 (t0 : PReal) := HLightPoint t0 ⟨1, by linarith⟩
def HLP2 (t1 : PReal):= HLightPoint t1 ⟨-1, by linarith⟩
noncomputable def MRay1 (t0 : PReal) := MRay (log t0)
noncomputable def MRay2 (t1 : PReal) := MRay (-(log t1))

theorem d1 (t0 t1 : PReal) : 
  Distance (MRay1 t0) (MRay2 t1) = log (MForm (HLP1 t0) (HLP2 t1)) := by
  rw [Distance, MRay1, MRay2, HLP1, HLP2, MRay, MRay, HLightPoint, HLightPoint]
  rw [MForm_eval, MForm_eval, Fin.sum_univ_four, Fin.sum_univ_four]
  simp [RayVector0, RayVector1, RayVector2, RayVector3]
  simp [HVector0, HVector1, HVector2, HVector3]
  sorry
  
end Minkowski