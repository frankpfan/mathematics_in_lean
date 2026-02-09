import Mathlib.Tactic


noncomputable def nn
  (a : ℕ → ℝ)
  (h : ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ a n ≠ a N)
  (m : ℕ) : ℕ := match m with
  | 0 => 0
  | k + 1 => (h (nn a h k)).choose

variable (a : ℕ → ℝ)
  (h : ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ a n ≠ a N)

theorem q3
  (a : ℕ → ℝ)
  (nonincr : ∀ i : ℕ, a i ≥ a (i + 1))
  (h : ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ a n ≠ a N)
  : ∃ n : ℕ → ℕ,
      ∀ i : ℕ, n i < n (i + 1) ∧ a (n i) ≤ a (n (i + 1)) := by
  let n := nn a h
  use n
  intro i
  constructor
  sorry
  sorry

/- ---------- -/

example (h : ∃ n : ℕ, n ≥ 10) : ∃ n : ℕ, n ≥ 5 := by
  rcases h with ⟨ n, h1 ⟩
  use n
  linarith

def f : ℕ → ℕ := fun m => match m with
  | 0 => 0
  | k + 1 => f k
