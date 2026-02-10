import Mathlib


-- Useful lemmas.
#check le_of_forall_pos_le_add
#check QuotientAddGroup.exists_norm_mk_lt

theorem ultra_of_quot_ultra
  {𝕜 E : Type*}
  [NormedField 𝕜]
  [SeminormedAddCommGroup E]
  [NormedSpace 𝕜 E]
  (F : Subspace 𝕜 E)
  [IsUltrametricDist E]
  : IsUltrametricDist (E ⧸ F) := by
  constructor
  intro x y z
  repeat rw [dist_eq_norm]
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨ u, hu1, hu2 ⟩ :=
    QuotientAddGroup.exists_norm_mk_lt (x - y) hε
  obtain ⟨ v, hv1, hv2 ⟩ :=
    QuotientAddGroup.exists_norm_mk_lt (y - z) hε
  calc
    ‖x - z‖ = ‖(x - y) + (y - z)‖ := by
      simp
    _ ≤ ‖u + v‖ := by
      rw [← hu1, ← hv1]
      apply QuotientAddGroup.norm_mk_le_norm
    _ ≤ max ‖u‖ ‖v‖ := by
      apply IsUltrametricDist.norm_add_le_max
    _ ≤ max (‖x - y‖ + ε) (‖y - z‖ + ε) := max_le_max hu2.le hv2.le
    _ = max ‖x - y‖ ‖y - z‖ + ε := by
      rw [← max_add]
