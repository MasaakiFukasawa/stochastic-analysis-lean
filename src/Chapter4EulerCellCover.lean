import Chapter4EulerStepGrowth

open Set
open scoped BigOperators
namespace Asakura.Chapter4

lemma uniform_grid_interval_cover (h : ℝ) (hh : 0≤h) (n : ℕ) (r : ℝ)
    (hr : r∈Ioc 0 ((n:ℝ)*h)) :
    ∃ k∈Finset.range n,r∈Ioc ((k:ℝ)*h) (((k:ℝ)+1)*h) := by
  induction n with
  | zero => simpa using hr
  | succ n ih =>
    by_cases hn : r≤(n:ℝ)*h
    · obtain ⟨k,hk,hkr⟩ := ih ⟨hr.1,hn⟩
      exact ⟨k,Finset.mem_range.mpr ((Finset.mem_range.mp hk).trans (Nat.lt_succ_self n)),hkr⟩
    · refine ⟨n,Finset.mem_range.mpr (Nat.lt_succ_self n),lt_of_not_ge hn,?_⟩
      simpa only [Nat.cast_add,Nat.cast_one] using hr.2

lemma uniform_grid_step_on_cell (h : ℝ) (hh : 0≤h) (n k : ℕ) (hk : k<n)
    (G : ℕ → ℝ) (r : ℝ) (hr : r∈Ioc ((k:ℝ)*h) (((k:ℝ)+1)*h)) :
    (∑ l∈Finset.range n,(Ioc ((l:ℝ)*h) (((l:ℝ)+1)*h)).indicator (fun _ => G l) r)=G k := by
  classical
  rw [Finset.sum_eq_single k,indicator_of_mem hr]
  · intro l hl hlk
    apply indicator_of_notMem
    intro hlr
    exact hlk (uniform_grid_interval_unique h hh l k r hlr hr)
  · exact fun hkn => (hkn (Finset.mem_range.mpr hk)).elim

end Asakura.Chapter4
