import Chapter4FiniteSumPowerMoment

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter4
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

lemma constant_path_memLp
    {Ω D : Type*} [MeasurableSpace Ω] [MetricSpace D] [CompactSpace D] [SecondCountableTopology D]
    (P : Measure Ω) (ξ : Ω → ℝ) (hm : Measurable ξ) (p : ℝ≥0∞) (hi : MemLp ξ p P) :
    MemLp (fun w => ContinuousMap.const D (ξ w)) p P := by
  have hcm : Measurable (fun w => ContinuousMap.const D (ξ w)) := ContinuousMap.measurable_iff_eval.mpr (fun _ => hm)
  apply hi.of_le_mul (c := 1) hcm.aestronglyMeasurable
  exact .of_forall (fun w => by simpa only [one_mul] using
    (ContinuousMap.norm_le _ (norm_nonneg (ξ w))).2 (fun _ => le_rfl))

lemma constant_path_norm {D : Type*} [TopologicalSpace D] [CompactSpace D] [Nonempty D] (x : ℝ) :
    ‖ContinuousMap.const D x‖=|x| := by
  apply le_antisymm
  · exact (ContinuousMap.norm_le _ (abs_nonneg x)).2 (fun _ => le_rfl)
  · obtain ⟨d⟩ := ‹Nonempty D›
    exact ContinuousMap.norm_coe_le_norm (ContinuousMap.const D x) d

/-- Combine the initial value and the two actual integral paths. -/
theorem three_term_path_power_moment
    {Ω D : Type*} [MeasurableSpace Ω] [MetricSpace D] [CompactSpace D]
    [SecondCountableTopology D] [Nonempty D] (P : Measure Ω)
    (ξ : Ω → ℝ) (hξ : Measurable ξ) (p : ℝ) (hp : 1≤p) (hiξ : MemLp ξ (ENNReal.ofReal p) P)
    (Y A N : Ω → C(D,ℝ)) (hiA : MemLp A (ENNReal.ofReal p) P) (hiN : MemLp N (ENNReal.ofReal p) P)
    (he : Y=ᵐ[P] fun w => ContinuousMap.const D (ξ w)+A w+N w) :
    MemLp Y (ENNReal.ofReal p) P ∧ (∫ w,‖Y w‖^p ∂P)≤
      (3:ℝ)^(p-1)*((∫ w,|ξ w|^p ∂P)+(∫ w,‖A w‖^p ∂P)+(∫ w,‖N w‖^p ∂P)) := by
  let B := fun w => ContinuousMap.const D (ξ w)
  have hiB := constant_path_memLp P ξ hξ (ENNReal.ofReal p) hiξ (D := D)
  let V : Fin 3 → Ω → C(D,ℝ) := ![B,A,N]
  have hiV : ∀ i,MemLp (V i) (ENNReal.ofReal p) P := by
    intro i; fin_cases i
    · exact hiB
    · exact hiA
    · exact hiN
  obtain ⟨hi,hb⟩ := finite_sum_power_moment P V p hp hiV
  have heV : (fun w => ∑ i,V i w)=(fun w => B w+A w+N w) := by
    funext w
    simp [V,Fin.sum_univ_succ,add_assoc]
  rw [heV] at hi
  simp_rw [show ∀ w,(∑ i,V i w)=B w+A w+N w from fun w => congrFun heV w] at hb
  refine ⟨(memLp_congr_ae he).2 hi,?_⟩
  have heI : (∫ w,‖Y w‖^p ∂P)=(∫ w,‖B w+A w+N w‖^p ∂P) :=
    integral_congr_ae (he.mono (fun w hw => congrArg (fun x => ‖x‖^p) hw))
  rw [heI]
  simpa [V,Fin.sum_univ_succ,B,constant_path_norm,add_assoc] using hb

end Asakura.Chapter4
