import Chapter5SmoothExtension

open Set Filter Function
open scoped Topology
namespace Asakura.Chapter4
set_option maxHeartbeats 2400000

/-- A smooth change of time keeps every argument positive and is exactly
the identity on a neighborhood of [eps,infinity). It allows Ito's formula
to be used without assuming differentiability at the terminal boundary. -/
theorem positive_time_retraction (eps : ℝ) (heps : 0<eps) :
    ∃ ρ : ℝ → ℝ,ContDiff ℝ 2 ρ ∧ (∀ t,0<ρ t) ∧
      ∀ t,eps≤t → ρ =ᶠ[𝓝 t] id := by
  obtain ⟨χ,hχ,hχb,hsupp,hone⟩ := exists_contDiff_support_eq_eq_one_iff
    (n := (2:ℕ∞)) (s := Ioi (eps/4)) (t := Ici (eps/2)) isOpen_Ioi isClosed_Ici
    (fun x hx => by change eps/2≤x at hx;change eps/4<x;linarith)
  let ρ := fun t => χ t*t+(1-χ t)*(eps/2)
  refine ⟨ρ,(hχ.mul contDiff_id).add ((contDiff_const.sub hχ).mul contDiff_const),?_,?_⟩
  · intro t
    have hχt := hχb (mem_range_self t)
    by_cases ht : t∈Ioi (eps/4)
    · dsimp only [ρ]
      have htp : 0<t := by change eps/4<t at ht;linarith
      by_cases hz : χ t=0
      · rw [hz];nlinarith
      · have hcp : 0<χ t := lt_of_le_of_ne hχt.1 (Ne.symm hz)
        exact add_pos_of_pos_of_nonneg (mul_pos hcp htp) (mul_nonneg (sub_nonneg.mpr hχt.2) (by positivity))
    · have hz : χ t=0 := notMem_support.mp (by rwa [hsupp])
      dsimp only [ρ]
      rw [hz]
      nlinarith
  · intro t ht
    filter_upwards [isOpen_Ioi.mem_nhds (show t∈Ioi (eps/2) by change eps/2<t;linarith)] with u hu
    have h1 := (hone u).mp (show u∈Ici (eps/2) by change eps/2≤u;exact le_of_lt hu)
    simp only [ρ,h1,one_mul,sub_self,zero_mul,add_zero,id_eq]

end Asakura.Chapter4
