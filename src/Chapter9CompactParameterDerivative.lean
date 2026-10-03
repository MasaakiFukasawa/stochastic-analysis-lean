import Chapter9CompactPriorIntegrable
import Mathlib.Analysis.Calculus.ParametricIntegral

open MeasureTheory Set Filter
open scoped Topology
namespace Asakura.Chapter9
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

/-- Differentiation under a compactly supported finite measure with a
continuous parameter derivative. The domination is derived on a compact
neighborhood, not assumed as an unexplained interchange rule. -/
theorem compact_parameter_integral_derivative {E V : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (μ : Measure E) [IsFiniteMeasure μ] (K : Set E) (hK : IsCompact K)
    (hμ : ∀ᵐ x ∂μ,x∈K) (F D : ℝ → E → V) (U : Set ℝ) (hU : IsOpen U)
    (hF : ContinuousOn F.uncurry (U ×ˢ univ)) (hcD : ContinuousOn D.uncurry (U ×ˢ univ))
    (hD : ∀ t∈U,∀ x,HasDerivAt (fun s => F s x) (D t x) t)
    (t : ℝ) (ht : t∈U) :
    HasDerivAt (fun s => ∫ x,F s x ∂μ) (∫ x,D t x ∂μ) t := by
  obtain ⟨r,hr,hrU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds ht)
  let S := Metric.closedBall t (r/2) ×ˢ K
  have hSU : S⊆U ×ˢ univ := by
    intro z hz
    exact ⟨hrU ((Metric.closedBall_subset_ball (by linarith : r/2<r)) hz.1),mem_univ _⟩
  have hS : IsCompact S := (isCompact_closedBall t (r/2)).prod hK
  obtain ⟨M,hM⟩ := hS.bddAbove_image (hcD.norm.mono hSU)
  have hFc s (hs : s∈U) : Continuous (F s) :=
    hF.comp_continuous (continuous_const.prodMk continuous_id) (fun _ => ⟨hs,mem_univ _⟩)
  have hDc : Continuous (D t) :=
    hcD.comp_continuous (continuous_const.prodMk continuous_id) (fun _ => ⟨ht,mem_univ _⟩)
  have hsmall : ∀ᶠ s in 𝓝 t,s∈U := hU.mem_nhds ht
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := μ) (F := F) (F' := D) (s := Metric.ball t (r/2)) (bound := fun _ => M)
    (Metric.ball_mem_nhds t (by linarith)) ?_ ?_ ?_ ?_ ?_ ?_).2
  · exact hsmall.mono (fun s hs => (hFc s hs).aestronglyMeasurable)
  · exact compact_prior_integrable μ K hK hμ (F t) (hFc t ht)
  · exact hDc.aestronglyMeasurable
  · filter_upwards [hμ] with x hx
    intro s hs
    exact hM (mem_image_of_mem _ (show (s,x)∈S from ⟨Metric.ball_subset_closedBall hs,hx⟩))
  · exact integrable_const M
  · apply ae_of_all
    intro x s hs
    exact hD s (hrU ((Metric.ball_subset_ball (by linarith : r/2≤r)) hs)) x
end Asakura.Chapter9
