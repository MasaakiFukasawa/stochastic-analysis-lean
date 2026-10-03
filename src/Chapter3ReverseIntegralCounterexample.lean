import Chapter3ShrinkingStrategy
import BrownianExists
import Chapter3LocalItoFormula

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal
namespace Asakura.Chapter3Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false

theorem half_time_real_clamp (r : ℝ) (hr : 0 ≤ r) :
    halfTimeReal (realTimeClamp (T := (⊤:EReal)) r) = Real.toNNReal r := by
  apply Subtype.ext
  change (realTimeClamp (T := (⊤:EReal)) r : EReal).toReal = (Real.toNNReal r : ℝ)
  rw [real_time_clamp_eq r hr le_top,EReal.toReal_coe,Real.coe_toNNReal r hr]

/-- A genuine counterexample, with existence of the probability space and
Brownian motion supplied by the appendix construction. Its bracket is time,
its strategies are actual H0 generators, their actual Stieltjes energies
vanish on every finite horizon, and the reverse integrals fail in probability. -/
theorem reverse_integral_counterexample_exists :
    ∃ Ω : Type, ∃ m : MeasurableSpace Ω, letI := m;
    ∃ P : Measure Ω, ∃ hP : IsProbabilityMeasure P, letI := hP;
    ∃ B : ℝ≥0 → Ω → ℝ,
      IsBrownianReal B P ∧
      (let F := halfClosedFiltration m (fun t => Asakura.nullAugmentation P (pastSigma B t));
       let X := fun t ω => B (halfTimeReal t) ω;
       LocalMProcessWitness P F X ∧
       LocalCovarianceWitness P F X X (fun t _ => (halfTimeReal t : ℝ))) ∧
      (∀ n, Measurable[Asakura.nullAugmentation P (pastSigma B 1)] (fun _ : Ω => (1:ℝ)) ∧
        MemLp (fun _ : Ω => (1:ℝ)) ∞ P ∧ (1:ℝ) < 1+spikeWidth n) ∧
      Tendsto (fun n => ∫ ω, (∫ r : ℝ, (spikeHolding n r)^2) ∂P) atTop (𝓝 0) ∧
      (∀ d (hd : 0 ≤ d), Tendsto (fun n => ∫ r, (spikeHolding n r)^2
        ∂(intervalStieltjes 0 d hd (fun r => r) monotoneOn_id
          (fun _ _ => continuousWithinAt_id)).measure) atTop (𝓝 0)) ∧
      ¬ TendstoInMeasure P (fun n ω => spikeReverse (fun r => B (Real.toNNReal r) ω) n 1)
        atTop (fun _ => 0) := by
  obtain ⟨Ω,m,P,hP,B,hm,hc,hB,_⟩ := Asakura.brownian_motion_exists
  letI := m
  letI := hP
  refine ⟨Ω,m,P,hP,B,hB,brownian_half_line_local_covariance P B hB.toIsPreBrownianReal hm hc,?_,?_,?_,
    brownian_spike_reverse_not_convergent P B hB.toIsPreBrownianReal⟩
  · intro n
    exact ⟨measurable_const,memLp_const _,by linarith [spike_width_positive n]⟩
  · simpa using (spike_energy_tends_zero : Tendsto (fun n => ∫ r : ℝ, (spikeHolding n r)^2) atTop (𝓝 0))
  · intro d hd
    exact spike_energy_actual_stieltjes d hd (fun r => r) monotoneOn_id continuousOn_id

end Asakura.Chapter3Complete
#print axioms Asakura.Chapter3Complete.half_time_real_clamp
#print axioms Asakura.Chapter3Complete.reverse_integral_counterexample_exists
