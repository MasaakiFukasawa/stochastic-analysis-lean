import Chapter13PositiveLogDecomposition
import Chapter6DensityCriterionWritten

open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal
namespace Asakura.Chapter13
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter5 Asakura.Chapter6
set_option maxHeartbeats 3800000
set_option backward.isDefEq.respectTransparency false

/-- Numeraire drift correction with the bracket of the actual logarithmic
semimartingale, rather than a formally named stochastic logarithm. X is centered. -/
theorem forward_measure_log_drift {Ω:Type*} {m:MeasurableSpace Ω}
    (P Q:Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {T:EReal} [Fact (0≤T)] (hT:0<T)
    (F:ClosedTime T → MeasurableSpace Ω) (hF:Monotone F) (hle:∀t,F t≤m)
    (hnull:∀t E,MeasurableSet[m] E → P E=0 → MeasurableSet[F t] E)
    (d:Ω → ℝ≥0) (hd:Measurable d) (hdi:Integrable (fun w => (d w:ℝ)) P)
    (hp:∀ᵐw∂P,0<(d w:ℝ)) (hQ:Q=P.withDensity (fun w => (d w:ℝ≥0∞)))
    (N:ClosedTime T → Ω → ℝ) (hNa:∀t,Measurable[F t] (N t))
    (hNc:∀w t,t<⊤ → ContinuousAt (fun s => N s w) t) (hNp:∀t w,0<N t w)
    (hNE:∀t,N t=ᵐ[P] P[(fun w => (d w:ℝ))|F t])
    (X A Y:ClosedTime T → Ω → ℝ) (hX:SemimartingaleDecomposition P F X A Y)
    (hXQ:LocalMProcessWitness Q F X) :
    ∃V L D,SemimartingaleDecomposition P F (fun t w => Real.log (N t w)) V L ∧
      LocalCovarianceWitness P F Y L D ∧ LocalMProcessWitness P F (fun t w => X t w+D t w) := by
  let M:=fun t w => N t w-N ⊥ w
  have hM:=centered_density_local P hT F hF hle _ hdi N hNa hNc hNE
  have hNv:=continuous_increasing_adapted_variation hT F hF (fun _ w => N ⊥ w)
    (fun _ _ => (hNa ⊥).mono (hF bot_le) le_rfl) (fun _ => monotoneOn_const) (fun _ _ _ => continuousAt_const)
  have hNs:SemimartingaleDecomposition P F N (fun _ w => N ⊥ w) M :=
    ⟨hNv,hM,hNc,fun _ _ _ => by dsimp [M];ring⟩
  obtain ⟨C0,hC0⟩:=local_covariance_witness_exists P F hF hle hnull M M hM hM
  obtain ⟨C,hC⟩:=local_covariance_witness_exists P F hF hle hnull M Y hM hX.martingale
  obtain ⟨c,hc,hcm,hcT,_,_,hcc⟩:=positive_real_time_exhaustion hT
  obtain ⟨V,L,hlog,hLI⟩:=positive_log_decomposition P hT F hF hle hnull N _ M C0 hNs hC0 hNp
    c (fun n => (hc n).le) hcm.monotone hcT hcc
  obtain ⟨K,hKv,hKc,hKI,hiff⟩:=density_criterion_written P Q hT F hF hle hnull d hd hdi hp hQ N hNa hNc hNp hNE
    X A Y C hX hC c (fun n => (hc n).le) hcm.monotone hcT hcc
  have hlocal:=hiff.mp hXQ
  obtain ⟨D,hD,hDK⟩:=ito_covariance_variation_identity P F M Y L C K hX.martingale hlog.martingale hC
    (fun z => (N (realTimeClamp z.2) z.1)⁻¹)
    (fun w => (open_path_real_measurable _ (hNc w)).inv) hLI
    c (fun n => (hc n).le) hcT hcc hKI
  have hDa:=covariance_adapted_variation P F hF hle hlog.martingale hX.martingale hD
  have hDc:=local_covariance_path_continuous P F L Y D hlog.martingale hX.martingale hD
  refine ⟨V,L,D,hlog,hD.symm P F,?_⟩
  apply Asakura.Chapter3Complete.LocalMProcessWitness.congr_ae_open P F hF hlocal
  · intro t ht
    have hh:X t=fun w => A t w+Y t w := funext (hX.decomposition t ht)
    rw [hh]
    exact ((hX.variation.adapted t ht).add (hX.martingale.adapted P F t ht)).add (hDa.adapted t ht)
  · intro w t ht
    exact (hX.continuous w t ht).add (hDc w t ht)
  · filter_upwards [hDK] with w hw
    intro t ht
    rw [hw t ht]
end Asakura.Chapter13
#print axioms Asakura.Chapter13.forward_measure_log_drift
