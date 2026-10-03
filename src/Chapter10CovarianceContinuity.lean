import Chapter10ErrorCovariancePositive

open MeasureTheory Set Filter
namespace Asakura.Chapter10
set_option backward.isDefEq.respectTransparency false

/-- The covariance of a continuous error process is continuous on every
interval where its path supremum is square integrable. -/
theorem covariance_continuous_on {Ω S ι : Type*} [MeasurableSpace Ω] [TopologicalSpace S] [FirstCountableTopology S]
    (P : Measure Ω) (D : Set S) (e : S → ι → Ω → ℝ)
    (hm : ∀ t∈D,∀ i,AEStronglyMeasurable (e t i) P)
    (hc : ∀ i,∀ᵐ w ∂P,ContinuousOn (fun t => e t i w) D)
    (K : Ω → ℝ) (hK : MemLp K 2 P)
    (hb : ∀ t∈D,∀ i,∀ᵐ w ∂P,‖e t i w‖≤K w) (i j : ι) :
    ContinuousOn (fun t => ∫ w,e t i w*e t j w ∂P) D := by
  apply continuousOn_of_dominated (bound := fun w => (K w)^2)
  · exact fun t ht => (hm t ht i).mul (hm t ht j)
  · intro t ht
    filter_upwards [hb t ht i,hb t ht j] with w hi hj
    rw [norm_mul,pow_two]
    exact mul_le_mul hi hj (norm_nonneg _) ((norm_nonneg _).trans hi)
  · exact hK.integrable_sq
  · filter_upwards [hc i,hc j] with w hi hj
    exact hi.mul hj

end Asakura.Chapter10
