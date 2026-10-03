import Chapter5FiniteTimeEnergy

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter5
set_option maxHeartbeats 1800000

/-- The infinite-time L² assumption supplies the integrable limiting
quadratic variation used to construct the terminal Ito integral. -/
theorem infinite_time_energy_limit
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (H : Ω × ℝ → ℝ) (hH : Measurable H)
    (hi : MemLp H 2 (P.prod (volume.restrict (Ioi 0))))
    (c : ℕ → ℝ) (hc : ∀ n,0 ≤ c n) (hcm : Monotone c) (hco : ∀ r,∃ n,r ≤ c n) :
    Integrable (fun w => ∫ r in Ioi 0,H (w,r)^2) P ∧
      (∀ n,∀ᵐ w ∂P,IntervalIntegrable (fun r => H (w,r)^2) volume 0 (c n)) ∧
      (∀ᵐ w ∂P,Tendsto (fun n => ∫ r in 0..c n,H (w,r)^2) atTop
        (𝓝 (∫ r in Ioi 0,H (w,r)^2))) := by
  have hs := (memLp_two_iff_integrable_sq hi.aestronglyMeasurable).mp hi
  have hun : (⋃ n,Ioc (0:ℝ) (c n)) = Ioi 0 := by
    ext r
    simp only [mem_iUnion,mem_Ioc,mem_Ioi]
    constructor
    · rintro ⟨n,hn,_⟩; exact hn
    · intro hr; obtain ⟨n,hn⟩ := hco r; exact ⟨n,hr,hn⟩
  have hm : Monotone (fun n => Ioc (0:ℝ) (c n)) := fun i j hij => Ioc_subset_Ioc_right (hcm hij)
  refine ⟨hs.integral_prod_left,?_,?_⟩
  · intro n
    filter_upwards [hs.prod_right_ae] with w hw
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (hc n)).mpr
      (hw.mono_measure (Measure.restrict_mono (fun r hr => hr.1) le_rfl))
  · filter_upwards [hs.prod_right_ae] with w hw
    have hh := tendsto_setIntegral_of_monotone (fun _ => measurableSet_Ioc) hm
      (show IntegrableOn (fun r => H (w,r)^2) (⋃ n,Ioc 0 (c n)) volume by rwa [hun])
    simpa only [hun,intervalIntegral.integral_of_le (hc _)] using hh

end Asakura.Chapter5
