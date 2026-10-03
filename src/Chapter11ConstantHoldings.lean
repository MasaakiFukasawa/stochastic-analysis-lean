import Chapter11ConstantVariationIntegral
import Chapter11ConstantIntegral
import Chapter11GeneralAssociativity

open MeasureTheory Set Filter
open scoped Topology
namespace Asakura.Chapter11
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

/-- Constant stock and bank holdings satisfy the actual self-financing
 equation. This supplies the integral interpretation of the forward hedge. -/
theorem constant_holdings_self_financing {Ω : Type*} {m : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] {T : EReal} [Fact (0≤T)] (hT : 0<T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t E,MeasurableSet[m] E → P E=0 → MeasurableSet[F t] E)
    (c : ℕ → ℝ) (hc : ∀ n,0≤c n) (hcT : ∀ n,(c n:EReal)<T)
    (hcc : ∀ t,t<⊤ → ∃ n,t<realTimeClamp (T:=T) (c n))
    (S A M B G E : ClosedTime T → Ω → ℝ) (hS : SemimartingaleDecomposition P F S A M)
    (h k d : ℝ) (hd : 0≤d) (hdT : (d:EReal)<T)
    (hG : SemimartingaleIntegralFormula P F c hc A M (fun _ => h) G)
    (hE : VariationIntegralFormula P c hc B (fun _ => k) E) :
    (fun w => h*S (realTimeClamp d) w+k*B (realTimeClamp d) w)=ᵐ[P]
      fun w => h*S ⊥ w+k*B ⊥ w+G (realTimeClamp d) w+E (realTimeClamp d) w := by
  obtain ⟨J,N,hGN,hJ,hN⟩ := hG
  have hj := constant_variation_integral_at P c hc hcT hcc A J h d hd hdT hJ
  have he := constant_variation_integral_at P c hc hcT hcc B E k d hd hdT hE
  have hn := constant_ito_integral_unique P hT F hF hle hnull M N hS.martingale hGN.martingale h hN
  filter_upwards [hj,he,hn,hS.martingale.initial P F] with w hj he hn hzero
  rw [hGN.decomposition _ (real_time_below d hd hdT) w,hj,he,hn _ (real_time_below d hd hdT),
    hS.decomposition _ (real_time_below d hd hdT) w,hS.decomposition ⊥ hT w,hzero]
  simp only [Pi.zero_apply]
  ring

end Asakura.Chapter11
