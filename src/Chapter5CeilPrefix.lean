import Chapter5CeilIntegrandGluing

open MeasureTheory Set Filter
open scoped BigOperators
namespace Asakura.Chapter5

/-- The ceiling-index pasted integrand agrees exactly, on every finite
integer prefix, with the finite sum of interval-supported integrands. -/
theorem ceil_integrand_prefix_sum
    {Ω : Type*} (H : ℕ → Ω × ℝ → ℝ) (N : ℕ) (w : Ω) (r : ℝ) :
    (Ioc (0:ℝ) N).indicator (fun r => H (Nat.ceil r-1) (w,r)) r=
      ∑ j∈Finset.range N,(Ioc (j:ℝ) (j+1)).indicator (fun r => H j (w,r)) r := by
  classical
  by_cases hr : r∈Ioc (0:ℝ) N
  · have hk0 : Nat.ceil r≠0 := by intro hk; exact not_le_of_gt hr.1 (Nat.ceil_eq_zero.mp hk)
    have hkN : Nat.ceil r≤N := Nat.ceil_le.mpr hr.2
    have hk : Nat.ceil r-1∈Finset.range N := Finset.mem_range.mpr (by omega)
    have hkr : r∈Ioc ((Nat.ceil r-1:ℕ):ℝ) ((Nat.ceil r-1:ℕ)+1) := by
      have hh := (Nat.ceil_eq_iff hk0).mp (rfl : Nat.ceil r=Nat.ceil r)
      have he : Nat.ceil r-1+1=Nat.ceil r := by omega
      have hecast : ((Nat.ceil r-1:ℕ):ℝ)+1=(Nat.ceil r:ℝ) := by exact_mod_cast he
      exact ⟨hh.1,hecast.symm ▸ hh.2⟩
    rw [indicator_of_mem hr,Finset.sum_eq_single (Nat.ceil r-1)]
    · rw [indicator_of_mem hkr]
    · intro j hj hne
      have hjr : r∉Ioc (j:ℝ) (j+1) := by
        intro hh
        have he : Nat.ceil r=j+1 := (Nat.ceil_eq_iff (by omega)).mpr (by simpa using hh)
        omega
      exact indicator_of_notMem hjr _
    · exact fun hh => (hh hk).elim
  · rw [indicator_of_notMem hr]
    symm
    apply Finset.sum_eq_zero
    intro j hj
    apply indicator_of_notMem
    intro hh
    apply hr
    exact ⟨(Nat.cast_nonneg j).trans_lt hh.1,hh.2.trans (by exact_mod_cast (Nat.succ_le_of_lt (Finset.mem_range.mp hj)))⟩

end Asakura.Chapter5
