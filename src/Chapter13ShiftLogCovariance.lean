import Chapter13LogBankFactor
import Chapter3OpenPathMeasurable

open MeasureTheory Set Filter
open scoped Topology
namespace Asakura.Chapter13
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter5 Asakura.Chapter6
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

theorem shifted_log_covariance {Ω:Type*} {m:MeasurableSpace Ω}
    (P:Measure Ω) [IsProbabilityMeasure P] {T:EReal} [Fact (0≤T)] (hT:0<T)
    (F:ClosedTime T → MeasurableSpace Ω) (hF:Monotone F) (hle:∀t,F t≤m)
    (hnull:∀t E,MeasurableSet[m] E → P E=0 → MeasurableSet[F t] E)
    (R A M Y C:ClosedTime T → Ω → ℝ) (hR:SemimartingaleDecomposition P F R A M)
    (hY:LocalMProcessWitness P F Y) (hC:LocalCovarianceWitness P F M Y C)
    (k:ℝ) (hp:∀t w,0<R t w+k)
    (c:ℕ → ℝ) (hc:∀n,0≤c n) (hcm:Monotone c) (hcT:∀n,(c n:EReal)<T)
    (hcc:∀t,t<⊤ → ∃n,t<realTimeClamp (T:=T) (c n)) :
    ∃V L D,SemimartingaleDecomposition P F (fun t w => Real.log (R t w+k)) V L ∧
      LocalCovarianceWitness P F Y L D ∧
      VariationIntegralFormula P c hc C (fun z => (R (realTimeClamp z.2) z.1+k)⁻¹) D := by
  have hk:=continuous_increasing_adapted_variation hT F hF (fun _ _ => k)
    (fun _ _ => measurable_const) (fun _ => monotoneOn_const) (fun _ _ _ => continuousAt_const)
  have hU:SemimartingaleDecomposition P F (fun t w => R t w+k) (fun t w => A t w+k) M :=
    ⟨hR.variation.add hk hF,hR.martingale,fun w t ht => (hR.continuous w t ht).add continuousAt_const,
      fun t ht w => by rw [hR.decomposition t ht w];ring⟩
  obtain ⟨C0,hC0⟩:=local_covariance_witness_exists P F hF hle hnull M M hR.martingale hR.martingale
  obtain ⟨V,L,hlog,hLI⟩:=positive_log_decomposition P hT F hF hle hnull _ _ M C0 hU hC0 hp c hc hcm hcT hcc
  have hRa t (ht:t<⊤):Measurable[F t] (R t) := by
    have he:R t=fun w => A t w+M t w := funext (hR.decomposition t ht)
    rw [he]
    exact (hR.variation.adapted t ht).add (hR.martingale.adapted P F t ht)
  have hHc w t ht:ContinuousAt (fun s => (R s w+k)⁻¹) t := ((hR.continuous w t ht).add continuousAt_const).inv₀ (hp t w).ne'
  have hr:=open_process_real_regularity F (fun t w => (R t w+k)⁻¹)
    (fun t ht => ((hRa t ht).add_const k).inv) hHc
  obtain ⟨J,hJv,hJc,hJ⟩:=continuous_adapted_variation_exists P F hF hnull c hc hcm hcT hcc C
    (covariance_adapted_variation P F hF hle hR.martingale hY hC)
    (local_covariance_path_continuous P F M Y C hR.martingale hY hC) (fun z => (R (realTimeClamp z.2) z.1+k)⁻¹) hr.1 hr.2
  obtain ⟨D,hD,hDJ⟩:=ito_covariance_variation_identity P F M Y L C J hY hlog.martingale hC _
    (fun w => open_path_real_measurable _ (hHc w)) hLI c hc hcT hcc hJ
  refine ⟨V,L,D,hlog,hD.symm P F,?_⟩
  exact hJ.congr_integral P c hc hcT C J D _ (hDJ.mono (fun w hw t ht => (hw t ht).symm))
end Asakura.Chapter13
#print axioms Asakura.Chapter13.shifted_log_covariance
