import Mathlib.Tactic


@[ext]
structure Mat where
  a : ℝ
  b : ℝ
  c : ℝ
  d : ℝ

/- Operations -/

def matPlus (A B : Mat) : Mat where
  a := A.a + B.a
  b := A.b + B.b
  c := A.c + B.c
  d := A.d + B.d

def matMult (A B : Mat) : Mat where
  a := A.a * B.a + A.b * B.c
  b := A.a * B.b + A.b * B.d
  c := A.c * B.a + A.d * B.c
  d := A.c * B.b + A.d * B.d

def matZero : Mat := { a := 0, b := 0, c := 0, d := 0 }

def matUnit : Mat := { a := 1, b := 0, c := 0, d := 1 }

def matNeg (A : Mat) : Mat where
  a := -A.a
  b := -A.b
  c := -A.c
  d := -A.d

/- Instances -/

instance : Add Mat where
  add := matPlus

instance : Mul Mat where
  mul := matMult

@[simp]
lemma _add_plus (A B : Mat) : A + B = matPlus A B := by rfl

@[simp]
lemma _add_mult (A B : Mat) : A * B = matMult A B := by rfl

/- Properties-/

theorem mat_add_zero (A : Mat) : matPlus A matZero = A := by
  simp [matPlus, matZero]

theorem mat_zero_add (A : Mat) : matPlus matZero A = A := by
  simp [matPlus, matZero]

theorem mat_add_assoc (A B C : Mat)
  : matPlus (matPlus A B) C = matPlus A (matPlus B C) := by
  simp [matPlus]
  constructor <;> simp [add_assoc]

theorem mat_add_comm (A B : Mat) : matPlus A B = matPlus B A := by
  simp [matPlus]
  constructor <;> simp [add_comm]

theorem mat_mul_assoc (A B C : Mat)
  : matMult (matMult A B) C = matMult A (matMult B C) := by
  -- ext <;> ( simp [matMult] ; ring )
  ext <;> (
    simp [matMult]
    repeat rw [add_mul, mul_add]
    repeat rw [mul_assoc]
    rw [← add_assoc]
    nth_rw 2 [add_assoc]
    nth_rw 3 [add_comm]
    rw [← add_assoc, add_assoc]
  )

theorem mat_left_distrib (A B C : Mat)
  : matMult A (matPlus B C) = matPlus (matMult A B) (matMult A C) := by
  ext <;> ( simp [matMult, matPlus] ; ring )

instance : Ring Mat where
  add := matPlus
  mul := matMult
  zero := matZero
  one := matUnit
  neg := matNeg
  add_zero := mat_add_zero
  zero_add := mat_zero_add
  add_assoc := mat_add_assoc
  add_comm := mat_add_comm
  mul_one := sorry /- by
    intro A
    simp; unfold matMult
    ext <;> ( simp; ring ) -/

  one_mul := sorry
  mul_zero := sorry
  zero_mul := sorry
  mul_assoc := mat_mul_assoc
  nsmul := sorry
  nsmul_zero := sorry
  nsmul_succ := sorry
  zsmul := sorry
  zsmul_zero' := sorry
  zsmul_succ' := sorry
  zsmul_neg' := sorry
  left_distrib := mat_left_distrib
  right_distrib := sorry
  neg_add_cancel := sorry
