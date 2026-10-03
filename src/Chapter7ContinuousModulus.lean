import Chapter7ProbabilitySqrtEnergy
import Chapter7FiniteTimeCLT

open MeasureTheory Set Filter
open scoped Topology NNReal
namespace Asakura.Chapter7
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

abbrev ClosePairs (E : Type*) [MetricSpace E] (h : ℝ≥0) :=
  {p : E × E // dist p.1 p.2 ≤ (h:ℝ)}

instance closePairs_compact (E : Type*) [MetricSpace E] [CompactSpace E] (h : ℝ≥0) :
    CompactSpace (ClosePairs E h) :=
  isCompact_iff_compactSpace.mp
    (isClosed_le (continuous_fst.dist continuous_snd) continuous_const : IsClosed {p : E × E | dist p.1 p.2 ≤ (h:ℝ)}).isCompact

noncomputable def modulusPath {E : Type*} [MetricSpace E] (f : C(E,ℝ)) (h : ℝ≥0) :
    C(ClosePairs E h,ℝ) := ⟨fun p => f p.val.1-f p.val.2,by fun_prop⟩

lemma modulusPath_bound {E : Type*} [MetricSpace E] [CompactSpace E]
    (f : C(E,ℝ)) (h : ℝ≥0) (s t : E) (hst : dist s t ≤ (h:ℝ)) :
    |f s-f t| ≤ ‖modulusPath f h‖ := by
  have hh := (modulusPath f h).norm_coe_le_norm ⟨(s,t),hst⟩
  change ‖f s-f t‖ ≤ ‖modulusPath f h‖ at hh
  simpa only [Real.norm_eq_abs] using hh

lemma continuous_modulus_zero {E : Type*} [MetricSpace E] [CompactSpace E]
    (f : C(E,ℝ)) (h : ℕ → ℝ≥0) (hh : Tendsto (fun n => (h n:ℝ)) atTop (𝓝 0)) :
    Tendsto (fun n => ‖modulusPath f (h n)‖) atTop (𝓝 0) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Eventually.of_forall (fun n => ha.trans_le (norm_nonneg _))
  · intro ε hε
    obtain ⟨δ,hδ,hd⟩ := Metric.uniformContinuous_iff.mp (CompactSpace.uniformContinuous_of_continuous f.continuous) (ε/2) (half_pos hε)
    filter_upwards [hh.eventually (gt_mem_nhds hδ)] with n hn
    have hb : ‖modulusPath f (h n)‖ ≤ ε/2 := by
      apply (modulusPath f (h n)).norm_le (half_pos hε).le |>.mpr
      intro p
      have hx : dist (f p.val.1) (f p.val.2) < ε/2 := hd (p.property.trans_lt hn)
      change ‖f p.val.1-f p.val.2‖ ≤ ε/2
      simpa only [Real.dist_eq,Real.norm_eq_abs] using hx.le
    linarith

lemma measurable_modulus {Ω E : Type*} [MeasurableSpace Ω] [MetricSpace E]
    [CompactSpace E] [SecondCountableTopology E]
    (f : Ω → C(E,ℝ)) (hf : ∀ t,Measurable (fun w => f w t)) (h : ℝ≥0) :
    Measurable (fun w => ‖modulusPath (f w) h‖) := by
  apply Measurable.norm
  apply ContinuousMap.measurable_iff_eval.mpr
  intro p
  exact (hf p.val.1).sub (hf p.val.2)

end Asakura.Chapter7
