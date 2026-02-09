import Mathlib.Tactic


noncomputable def kk
  (a : ℕ → ℝ)
  (h : ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ a n ≠ a N)
  (n : ℕ) : ℕ := match n with
  | 0 => 0
  | m + 1 => (h (kk a h m)).choose

theorem q3
  (a : ℕ → ℝ)
  (nonincr : ∀ i j : ℕ, i ≤ j → a j ≤ a i)
  (h : ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ a n ≠ a N)
  : ∃ n : ℕ → ℕ,
      ∀ i : ℕ, n i < n (i + 1) ∧ a (n (i+1)) ≤ a (n i) := by
  use kk a h
  intro i
  constructor
  · simp [kk]
    apply lt_of_le_of_ne
    exact (h (kk a h i)).choose_spec.1
    intro h'
    have := (h  (kk a h i)).choose_spec.2
    apply this
    apply_fun a at h'
    symm
    assumption
  · apply nonincr
    sorry

/- ---------- -/

example (h : ∃ n : ℕ, n ≥ 10) : ∃ n : ℕ, n ≥ 5 := by
  rcases h with ⟨ n, h1 ⟩
  use n
  linarith

def f : ℕ → ℕ := fun m => match m with
  | 0 => 0
  | k + 1 => f k
