import Chapter13GlobalDriftPrimitive
import Chapter13MatrixNoiseConstruction
import Chapter13HJMExponentialNecessity

open MeasureTheory Set
namespace Asakura.Chapter13
open Asakura.Chapter6 Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter5
set_option maxHeartbeats 4200000
set_option backward.isDefEq.respectTransparency false

/-- Construct the exponent's decomposition and bracket from its original
Brownian coefficients, then derive the necessary exponential-martingale drift. -/
theorem brownian_exponent_constructed {Ω:Type*} {m:MeasurableSpace Ω}
    (P:Measure Ω) [IsProbabilityMeasure P] {d:ℕ} (B:BrownianSystem P d)
    (ξ:Ω → ℝ) (hξ:Measurable[B.F ⊥] ξ)
    (b:Ω × ℝ → ℝ) (hbm:Measurable b)
    (hbp:∀R,0<R → @Measurable _ _ (progressiveSpace (fun t:Icc (0:ℝ) R => B.F (realTimeClamp t.val))) inferInstance
      (fun z:Ω × Icc (0:ℝ) R => b (z.1,z.2.val)))
    (hbi:∀w R,0≤R → IntervalIntegrable (fun r => b (w,r)) volume 0 R)
    (H:Fin d → Ω × ℝ → ℝ) (hHm:∀i,Measurable (H i))
    (hHp:∀i R,0<R → @Measurable _ _ (progressiveSpace (fun t:Icc (0:ℝ) R => B.F (realTimeClamp t.val))) inferInstance
      (fun z:Ω × Icc (0:ℝ) R => H i (z.1,z.2.val)))
    (hHi:∀i w R,0≤R → IntervalIntegrable (fun r => H i (w,r)^2) volume 0 R) :
    ∃(N:Fin d → HalfClosedTime → Ω → ℝ) (X A:HalfClosedTime → Ω → ℝ),
      (∀i,LocalMProcessWitness P B.F (N i)) ∧
      (∀i,ItoCovarianceFormula P B.F (B.W i) (H i) (N i)) ∧
      SemimartingaleDecomposition P B.F X A (fun t w => ∑i,N i t w) ∧
      (∀w r,0≤r → X (realTimeClamp r) w=ξ w+(∫s in 0..r,b (w,s))+∑i,N i (realTimeClamp r) w) ∧
      (LocalMProcessWitness P B.F (fun t w => Real.exp (X t w)-Real.exp (X ⊥ w)) →
        ∀R,0≤R → ∀ᵐw∂P,∀ᵐr∂volume,r∈Ioo 0 R → b (w,r)=-(∑i,H i (w,r)^2)/2) := by
  have hT:(0:EReal)<⊤ := by simp
  obtain ⟨D,hD,hDc,hD0,hDe⟩:=global_drift_primitive B.F B.mono b hbp hbi
  obtain ⟨NN,hNN,hNI,hNC⟩:=matrix_noise_constructed (n:=1) P B (fun _ i => H i)
    (fun _ => hHm) (fun _ => hHp) (fun _ => hHi)
  let N:=NN 0
  have hNs:LocalMProcessWitness P B.F (fun t w => ∑i,N i t w) :=
    local_process_finset_sum P B.F B.mono B.le Finset.univ N (fun i _ => hNN 0 i)
      (zero_local_process P hT B.F)
  obtain ⟨C,hC,hCe⟩:=hNC 0 0
  let A:=fun t w => ξ w+D t w
  let X:=fun t w => A t w+∑i,N i t w
  have hξv:=continuous_increasing_adapted_variation hT B.F B.mono (fun _ w => ξ w)
    (fun t _ => hξ.mono (B.mono bot_le) le_rfl) (fun _ => monotoneOn_const) (fun _ _ _ => continuousAt_const)
  have hX:SemimartingaleDecomposition P B.F X A (fun t w => ∑i,N i t w) :=
    ⟨hξv.add hD B.mono,hNs,fun w t ht => (continuousAt_const.add (hDc w t ht)).add (hNs.path P B.F w t ht),fun _ _ _ => rfl⟩
  refine ⟨N,X,A,hNN 0,hNI 0,hX,?_,?_⟩
  · intro w r hr
    simp only [X,A,hDe w r hr]
  · intro hE R hR
    obtain ⟨c,hc,hcm,hcT,hct,hcut,hcc⟩:=positive_real_time_exhaustion hT
    let q:=fun z:Ω × ℝ => ∑i,H i z^2
    have hqi w a (ha:0≤a):IntervalIntegrable (fun r => q (w,r)) volume 0 a := by
      simpa only [q,Finset.sum_fn,Finset.sum_apply] using IntervalIntegrable.sum Finset.univ (fun i _ => hHi i w a ha)
    have hqm:Measurable q := Finset.measurable_sum _ (fun i _ => (hHm i).pow_const 2)
    have hCQ n:∀ᵐw∂P,∀r∈Icc 0 (c n),C (realTimeClamp r) w=∫s in 0..r,q (w,s) := by
      apply covariance_density_common_time P B.F _ _ C hNs hNs hC q
        (fun a ha => ae_of_all _ fun w => hqi w a ha) ?_ (c n) (hc n).le
      intro r hr
      simpa only [q,pow_two,N] using hCe r hr
    have hh:=exponential_martingale_drift_necessary P hT B.F B.mono B.le B.null X A _ C hX hC hE
      c hc hcm.monotone hcT hcc b q
      (fun w => hbm.comp measurable_prodMk_left) (fun w => hqm.comp measurable_prodMk_left)
      (fun n => ae_of_all _ fun w => hbi w (c n) (hc n).le)
      (fun n => ae_of_all _ fun w => hqi w (c n) (hc n).le)
      (fun n => ae_of_all _ fun w r hr => by simp only [A,hDe w r hr.1,hD0,add_zero]) hCQ
    obtain ⟨n,hn⟩:=hcc (realTimeClamp R) (real_time_below R hR (EReal.coe_lt_top R))
    have hRn:R<c n := by
      change (realTimeClamp R:EReal)<(realTimeClamp (c n):EReal) at hn
      rw [real_time_clamp_eq R hR le_top,real_time_clamp_eq (c n) (hc n).le le_top] at hn
      exact_mod_cast hn
    filter_upwards [hh n] with w hw
    filter_upwards [hw] with r hr
    exact fun hri => hr ⟨hri.1,hri.2.trans hRn⟩
end Asakura.Chapter13
#print axioms Asakura.Chapter13.brownian_exponent_constructed
