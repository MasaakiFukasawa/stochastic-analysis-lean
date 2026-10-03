import Chapter2StoppedM2Equivalence

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
set_option maxHeartbeats 700000

/-- On a compact time interval the continuous path norm is attained. -/
theorem continuous_path_norm_attained {ι : Type*} [TopologicalSpace ι]
    [CompactSpace ι] [Nonempty ι] (f : C(ι,ℝ)) : ∃ t, ‖f t‖ = ‖f‖ := by
  obtain ⟨t,_,ht⟩ := isCompact_univ.exists_isMaxOn univ_nonempty f.continuous.norm.continuousOn
  exact ⟨t,le_antisymm (f.norm_coe_le_norm t)
    ((f.norm_le (norm_nonneg _)).2 fun s => ht (mem_univ s))⟩

theorem continuous_path_square_sup {ι : Type*} [TopologicalSpace ι]
    [CompactSpace ι] [Nonempty ι] (f : C(ι,ℝ)) :
    (⨆ t, ENNReal.ofReal (f t ^ 2)) = ENNReal.ofReal (‖f‖ ^ 2) := by
  apply le_antisymm
  · apply iSup_le
    intro t
    apply ENNReal.ofReal_le_ofReal
    have h := pow_le_pow_left₀ (norm_nonneg _) (f.norm_coe_le_norm t) 2
    simpa only [Real.norm_eq_abs,sq_abs] using h
  · obtain ⟨t,ht⟩ := continuous_path_norm_attained f
    have hs : f t ^ 2 = ‖f‖ ^ 2 := by
      rw [← ht,Real.norm_eq_abs,sq_abs]
    rw [← hs]
    exact le_iSup (fun t => ENNReal.ofReal (f t ^ 2)) t

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.continuous_path_norm_attained
#print axioms Asakura.Chapter2Complete.continuous_path_square_sup
