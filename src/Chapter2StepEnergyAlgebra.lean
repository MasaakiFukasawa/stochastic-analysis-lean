import Chapter2StepRefinement

open Set
namespace Asakura.Chapter2Complete
set_option maxHeartbeats 1000000

def stepIncrement {α : Type*} [LinearOrder α] (a b : α) (f : α → ℝ) (t : α) : ℝ :=
  f (min b t)-f (min a t)

/-- Disjoint holding intervals have zero iterated increment. -/
theorem step_increment_disjoint {α : Type*} [LinearOrder α]
    (a b c d : α) (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d)
    (f : α → ℝ) (t : α) : stepIncrement a b (stepIncrement c d f) t = 0 := by
  simp only [stepIncrement,← min_assoc,min_eq_right (hbc.trans hcd),
    min_eq_right hbc,min_eq_right (hab.trans (hbc.trans hcd)),min_eq_right (hab.trans hbc),sub_self]

theorem step_increment_comm {α : Type*} [LinearOrder α]
    (a b c d : α) (f : α → ℝ) (t : α) :
    stepIncrement a b (stepIncrement c d f) t = stepIncrement c d (stepIncrement a b f) t := by
  simp only [stepIncrement,← min_assoc]
  rw [min_comm d b,min_comm c b,min_comm d a,min_comm c a]
  ring

theorem step_increment_idempotent {α : Type*} [LinearOrder α]
    (a b : α) (hab : a ≤ b) (f : α → ℝ) (t : α) :
    stepIncrement a b (stepIncrement a b f) t = stepIncrement a b f t := by
  simp only [stepIncrement,← min_assoc,min_self,min_eq_left hab,min_eq_right hab,sub_self,sub_zero]

/-- On a common ordered time grid, all cross-cell increment terms vanish. -/
theorem grid_increment_diagonal {α : Type*} [LinearOrder α]
    (N : ℕ) (u : ℕ → α) (hu : StrictMonoOn u (Iic N))
    (i j : ℕ) (hi : i < N) (hj : j < N) (f : α → ℝ) (t : α) :
    stepIncrement (u i) (u (i+1)) (stepIncrement (u j) (u (j+1)) f) t =
      if i = j then stepIncrement (u i) (u (i+1)) f t else 0 := by
  have hmono {k l : ℕ} (hk : k ≤ N) (hl : l ≤ N) (hkl : k ≤ l) : u k ≤ u l :=
    hu.monotoneOn hk hl hkl
  have hui : u i ≤ u (i+1) := hmono hi.le (by omega) (by omega)
  have huj : u j ≤ u (j+1) := hmono hj.le (by omega) (by omega)
  by_cases hij : i = j
  · subst j
    simp only [ite_true,step_increment_idempotent _ _ hui]
  · rw [if_neg hij]
    rcases lt_or_gt_of_ne hij with hij | hji
    · exact step_increment_disjoint _ _ _ _ hui (hmono (by omega) hj.le (by omega)) huj f t
    · rw [step_increment_comm]
      exact step_increment_disjoint _ _ _ _ huj (hmono (by omega) hi.le (by omega)) hui f t

/-- Applying the elementary covariation formula twice yields exactly
the square-coefficient Stieltjes sum on a common partition. -/
theorem grid_square_energy_identity {α : Type*} [LinearOrder α]
    (N : ℕ) (u : ℕ → α) (hu : StrictMonoOn u (Iic N))
    (G : ℕ → ℝ) (A : α → ℝ) (t : α) :
    (∑ i ∈ Finset.range N, G i * stepIncrement (u i) (u (i+1))
      (fun r => ∑ j ∈ Finset.range N, G j * stepIncrement (u j) (u (j+1)) A r) t) =
      ∑ i ∈ Finset.range N, G i ^ 2 * stepIncrement (u i) (u (i+1)) A t := by
  classical
  apply Finset.sum_congr rfl
  intro i hi
  have hin : i < N := Finset.mem_range.1 hi
  have he : stepIncrement (u i) (u (i+1))
      (fun r => ∑ j ∈ Finset.range N, G j * stepIncrement (u j) (u (j+1)) A r) t =
      ∑ j ∈ Finset.range N, G j * stepIncrement (u i) (u (i+1))
        (stepIncrement (u j) (u (j+1)) A) t := by
    simp only [stepIncrement,← Finset.sum_sub_distrib,mul_sub]
  rw [he]
  have he' : (∑ j ∈ Finset.range N, G j * stepIncrement (u i) (u (i+1))
      (stepIncrement (u j) (u (j+1)) A) t) = G i * stepIncrement (u i) (u (i+1)) A t := by
    rw [Finset.sum_eq_single i]
    · rw [step_increment_idempotent _ _ (hu.monotoneOn (Finset.mem_range.1 hi).le
        (show i+1 ∈ Iic N by change i+1 ≤ N; omega) (by omega))]
    · intro j hj hji
      rw [grid_increment_diagonal N u hu i j (Finset.mem_range.1 hi) (Finset.mem_range.1 hj) A t,
        if_neg (Ne.symm hji),mul_zero]
    · intro hn
      exact (hn hi).elim
  rw [he']
  ring

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.step_increment_disjoint
#print axioms Asakura.Chapter2Complete.step_increment_comm
#print axioms Asakura.Chapter2Complete.step_increment_idempotent
#print axioms Asakura.Chapter2Complete.grid_increment_diagonal
#print axioms Asakura.Chapter2Complete.grid_square_energy_identity
