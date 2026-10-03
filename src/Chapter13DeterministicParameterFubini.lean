import Chapter13BoundedParameterEnergy

open MeasureTheory Set
namespace Asakura.Chapter13
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

/-- Ordinary Fubini for the original HJM drift on a finite rectangle.
Absolute integrability is derived from its pathwise bound. -/
theorem deterministic_parameter_fubini {E:Type*} [MeasurableSpace E]
    (μ:Measure E) [IsFiniteMeasure μ] (H:E × ℝ → ℝ) (hm:Measurable H)
    (t:ℝ) (ht:0≤t) (K:ℝ) (hb:∀x r,r∈Icc 0 t → |H (x,r)|≤K) :
    Integrable (fun x => ∫r in 0..t,H (x,r)) μ ∧
      (∫x,(∫r in 0..t,H (x,r))∂μ)=(∫r in 0..t,∫x,H (x,r)∂μ) := by
  have hi:Integrable H (μ.prod (volume.restrict (Ioc 0 t))) := by
    apply (integrable_const K).mono' hm.aestronglyMeasurable
    have hs:∀ᵐz:E × ℝ∂μ.prod (volume.restrict (Ioc 0 t)),z.2∈Ioc 0 t :=
      Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem measurableSet_Ioc)
    filter_upwards [hs] with z hz
    exact hb z.1 z.2 ⟨hz.1.le,hz.2⟩
  simp only [intervalIntegral.integral_of_le ht]
  exact ⟨hi.integral_prod_left,integral_integral_swap hi⟩

/-- Integrate the original forward-rate equation after the two Fubini
steps. Integrability of every summand is retained explicitly. -/
theorem integrated_forward_equation {E:Type*} [MeasurableSpace E]
    (μ:Measure E) {d:ℕ} (f0 D:E → ℝ) (N:Fin d → E → ℝ)
    (hf:Integrable f0 μ) (hD:Integrable D μ) (hN:∀i,Integrable (N i) μ)
    (a:ℝ) (z:Fin d → ℝ) (ha:(∫x,D x∂μ)=a) (hz:∀i,(∫x,N i x∂μ)=z i) :
    -(∫x,f0 x+D x-∑i,N i x∂μ)=-(∫x,f0 x∂μ)-a+∑i,z i := by
  have hs:Integrable (fun x => ∑i,N i x) μ := by
    simpa only [Finset.sum_fn,Finset.sum_apply] using integrable_finset_sum Finset.univ (fun i _ => hN i)
  rw [integral_sub (f:=fun x => f0 x+D x) (hf.add hD) hs,integral_add hf hD,integral_finset_sum _ (fun i _ => hN i),ha]
  simp only [hz]
  ring
end Asakura.Chapter13
#print axioms Asakura.Chapter13.deterministic_parameter_fubini
#print axioms Asakura.Chapter13.integrated_forward_equation
