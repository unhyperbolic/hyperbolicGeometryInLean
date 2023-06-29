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

