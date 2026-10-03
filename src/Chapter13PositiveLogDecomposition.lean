import Chapter13PositiveLogIto
import Chapter2StochasticFubiniPrinted
import Chapter6ItoCovarianceVariation

open MeasureTheory Set Filter
open scoped Topology
namespace Asakura.Chapter13
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter5 Asakura.Chapter6
set_option maxHeartbeats 3500000
set_option backward.isDefEq.respectTransparency false

theorem positive_log_decomposition {Ω:Type*} {m:MeasurableSpace Ω}
    (P:Measure Ω) [IsProbabilityMeasure P] {T:EReal} [Fact (0≤T)] (hT:0<T)
    (F:ClosedTime T → MeasurableSpace Ω) (hF:Monotone F) (hle:∀t,F t≤m)
    (hnull:∀t E,MeasurableSet[m] E → P E=0 → MeasurableSet[F t] E)
    (X A M C:ClosedTime T → Ω → ℝ) (hX:SemimartingaleDecomposition P F X A M)
    (hC:LocalCovarianceWitness P F M M C) (hp:∀t w,0<X t w)
    (c:ℕ → ℝ) (hc:∀n,0≤c n) (hcm:Monotone c) (hcT:∀n,(c n:EReal)<T)
    (hcc:∀t,t<⊤ → ∃n,t<realTimeClamp (T:=T) (c n)) :
    ∃B N,SemimartingaleDecomposition P F (fun t w => Real.log (X t w)) B N ∧
      ItoCovarianceFormula P F M (fun z => (X (realTimeClamp z.2) z.1)⁻¹) N := by
  obtain ⟨I,J,L,hIv,hJv,hL,hIc,hJc,hI,hJ,hLI,he⟩:=positive_log_ito_constructed P hT F hF hle hnull X A M C hX hC hp c hc hcm hcT hcc
  have hXa t (ht:t<⊤):Measurable[F t] (X t) := by
    have hh:X t=fun w => A t w+M t w := funext (hX.decomposition t ht)
    rw [hh]
    exact (hX.variation.adapted t ht).add (hX.martingale.adapted P F t ht)
  have hEa t ht := (hXa t ht).log
  have hEc w t ht:ContinuousAt (fun s => Real.log (X s w)) t := (hX.continuous w t ht).log (hp t w).ne'
  have hconst:=continuous_increasing_adapted_variation hT F hF (fun _ w => Real.log (X ⊥ w))
    (fun _ _ => (hEa ⊥ hT).mono (hF bot_le) le_rfl) (fun _ => monotoneOn_const) (fun _ _ _ => continuousAt_const)
  let B:=fun t w => Real.log (X ⊥ w)+I t w+J t w/2
  have hB:AdaptedLocalVariationWitness F B := by
    convert (hconst.add hIv hF).add (hJv.smul (1/2)) hF using 1
    funext t w
    dsimp [B]
    ring
  have hBc w t ht:ContinuousAt (fun s => B s w) t :=
    (continuousAt_const.add (hIc w t ht)).add ((hJc w t ht).div_const 2)
  have hd:∀ᵐw∂P,∀t,t<⊤ → Real.log (X t w)=B t w+L t w := by
    filter_upwards [he] with w hw
    intro t ht
    dsimp [B]
    linarith [hw t ht]
  obtain ⟨hD,hNe⟩:=semimartingale_of_ae_decomposition P F hF _ B L hEa hEc hB hBc hL hd
  exact ⟨B,_,hD,hLI.congr_integral P F hF hle M L _ _ hL hD.martingale hNe⟩
end Asakura.Chapter13
#print axioms Asakura.Chapter13.positive_log_decomposition
