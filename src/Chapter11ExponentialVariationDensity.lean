import Chapter11ExponentialVariation
import Chapter3VariationChainRule
import Chapter6FiniteTimeDensity
import Chapter4FinitePathLift
import Chapter3OpenPathMeasurable

open MeasureTheory Set Filter
open scoped Topology
namespace Asakura.Chapter11
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter5 Asakura.Chapter6
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

/-- Exponential chain rule for merely integrable time densities, rather
than continuous rates. This is the bank-account and discount-factor step. -/
theorem exponential_variation_time_density {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) {T : EReal} [Fact (0≤T)] (hT : 0<T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t N,MeasurableSet[m] N → P N=0 → MeasurableSet[F t] N)
    (A : ClosedTime T → Ω → ℝ) (hA : AdaptedLocalVariationWitness F A)
    (hAc : ∀ w t,t<⊤ → ContinuousAt (fun s => A s w) t)
    (b : Ω × ℝ → ℝ) (hbm : ∀ w,Measurable (fun r => b (w,r)))
    (R : ℝ) (hR : 0≤R) (hRT : (R:EReal)<T)
    (hbi : ∀ᵐ w ∂P,IntervalIntegrable (fun r => b (w,r)) volume 0 R)
    (hAe : ∀ᵐ w ∂P,∀ r∈Icc 0 R,A (realTimeClamp r) w=A ⊥ w+∫ s in 0..r,b (w,s)) :
    ∀ t∈Icc 0 R,(fun w => Real.exp (A (realTimeClamp t) w))=ᵐ[P]
      fun w => Real.exp (A ⊥ w)+(∫ s in 0..t,Real.exp (A (realTimeClamp s) w)*b (w,s)) := by
  obtain ⟨c,hc,hcm,hcT,_,_,hcc⟩ := positive_real_time_exhaustion hT
  have hr := open_process_real_regularity F (fun t w => Real.exp (A t w))
    (fun t ht => (hA.adapted t ht).exp) (fun w t ht => Real.continuous_exp.continuousAt.comp (hAc w t ht))
  obtain ⟨I,hIv,hIc,hI⟩ := continuous_adapted_variation_exists P F hF hnull c (fun n => (hc n).le)
    hcm.monotone hcT hcc A hA hAc (fun z => Real.exp (A (realTimeClamp z.2) z.1)) hr.1 hr.2
  have hchain := continuous_variation_chain_rule P hT F hF hle A I hA hAc Real.exp Real.contDiff_exp
    c (fun n => (hc n).le) hcT hcc (by simpa only [Real.deriv_exp] using hI)
  intro t ht
  have htT := (EReal.coe_le_coe ht.2).trans_lt hRT
  have hbti : ∀ᵐ w ∂P,IntervalIntegrable (fun r => b (w,r)) volume 0 t :=
    hbi.mono (fun w hw => hw.mono_set (by simpa only [uIcc_of_le ht.1,uIcc_of_le hR] using Icc_subset_Icc_right ht.2))
  have hi := finite_time_density_variation_integral P A I (A ⊥) b _ c (fun n => (hc n).le) hcT hcc
    t ht.1 htT (hAe.mono (fun w hw r hr => hw r (Icc_subset_Icc_right ht.2 hr))) hbm hbti
    (fun w => open_path_real_measurable _ (fun s hs => Real.continuous_exp.continuousAt.comp (hAc w s hs)))
    (hr.2 t ht.1 htT) hI
  filter_upwards [hchain,hi] with w hw hi
  rw [hw _ (real_time_below t ht.1 htT),hi]

end Asakura.Chapter11
