import Chapter6ItoCovarianceVariation
import Chapter6VariationAdd
import Chapter3VariationWeightProduct
import Chapter6ExponentialLocal
import Chapter6RandomVariationScalar
import Chapter4UnboundedInitialWeight

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter6
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete
set_option maxHeartbeats 3500000
set_option backward.isDefEq.respectTransparency false

/-- The drift cancellation in Girsanov's theorem, from the actual Ito
covariance formula and integration by parts with the bracket process.
The product's local-martingale property is the conclusion, not a hypothesis. -/
theorem initial_shifted_corrected_product_local
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t ≤ m)
    (hnull : ∀ t N,MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (Z Y L K : ClosedTime T → Ω → ℝ) (a : Ω → ℝ) (ha : Measurable[F ⊥] a)
    (hZ : LocalMProcessWitness P F Z) (hY : LocalMProcessWitness P F Y)
    (hL : LocalMProcessWitness P F L) (hK : LocalCovarianceWitness P F Z Y K)
    (hLI : ItoCovarianceFormula P F Z (fun z => a z.1+L (realTimeClamp z.2) z.1) L)
    (hHm : ∀ w,Measurable (fun r => a w+L (realTimeClamp r) w)) :
    LocalMProcessWitness P F (fun t w => (a w+L t w)*(Y t w-K t w)) := by
  have hKv := covariance_adapted_variation P F hF hle hZ hY hK
  have hKc := local_covariance_path_continuous P F Z Y K hZ hY hK
  have hLr := open_process_real_regularity F L (hL.adapted P F) (hL.path P F)
  have hKr := open_process_real_regularity F K (hK.adapted P F hZ hY) hKc
  obtain ⟨c,hc,hcm,hcT,_,_,hcc⟩ := positive_real_time_exhaustion hT
  obtain ⟨U,hUv,hUc,hU⟩ := continuous_adapted_variation_exists P F hF hnull c
    (fun n => (hc n).le) hcm.monotone hcT hcc K hKv hKc (fun _ => (1:ℝ))
    (fun _ _ _ => measurable_const) (fun _ _ _ _ => continuousOn_const)
  obtain ⟨V,hVv,hVc,hV⟩ := continuous_adapted_variation_exists P F hF hnull c
    (fun n => (hc n).le) hcm.monotone hcT hcc K hKv hKc
    (fun z => L (realTimeClamp z.2) z.1) hLr.1 hLr.2
  have haU := variation_integrand_random_scalar P c (fun n => (hc n).le) K U (fun _ => (1:ℝ)) a hU
  have hUV := variation_integrand_add P c (fun n => (hc n).le) K (fun t w => a w*U t w) V _ _ haU hV
  simp only [mul_one] at hUV
  obtain ⟨D,hD,hDUV⟩ := ito_covariance_variation_identity P F Z Y L K (fun t w => a w*U t w+V t w)
    hY hL hK _ hHm hLI c (fun n => (hc n).le) hcT hcc hUV
  obtain ⟨I,hI,hII⟩ := continuous_adapted_ito_exists P hT F hF hle hnull L hL
    (fun z => K (realTimeClamp z.2) z.1) hKr.1 hKr.2
  have hprod := variation_weight_product_formula P hT F hF hle hnull L K I V hL hKv hKc hI hII
    c (fun n => (hc n).le) hcT hcc hV
  have hchain := continuous_variation_chain_rule P hT F hF hle K U hKv hKc
    (fun x : ℝ => x) contDiff_id c (fun n => (hc n).le) hcT hcc (by simpa using hU)
  have hK0 : K ⊥ =ᵐ[P] 0 := by
    filter_upwards [local_initial_zero P F Z hZ,local_initial_zero P F Y hY,
      local_initial_zero P F _ hK.defect] with w hz hy hd
    change Z ⊥ w*Y ⊥ w-K ⊥ w = 0 at hd
    change K ⊥ w = 0
    simp only [hz,hy,Pi.zero_apply,zero_mul,zero_sub,neg_eq_zero] at hd
    exact hd
  have haY := Asakura.Chapter4.unbounded_initial_weight_local P hT F hF hle hnull Y hY a ha
  have hN := (haY.add P F hF hle hD.defect).add P F hF hle (hI.smul P F (-1))
  apply Asakura.Chapter3Complete.LocalMProcessWitness.congr_ae_open P F hF hN
  · intro t ht
    exact ((ha.mono (hF bot_le) le_rfl).add (hL.adapted P F t ht)).mul
      ((hY.adapted P F t ht).sub (hK.adapted P F hZ hY t ht))
  · intro w t ht
    exact (continuousAt_const.add (hL.path P F w t ht)).mul ((hY.path P F w t ht).sub (hKc w t ht))
  · filter_upwards [hDUV,hprod,hchain,hK0] with w hd hp hc hk0
    intro t ht
    have hu : U t w = K t w := by
      have hh := hc t ht
      change K t w = K ⊥ w+U t w at hh
      simpa only [hk0,Pi.zero_apply,zero_add] using hh.symm
    have hd := hd t ht
    have hp := hp t ht
    change a w*Y t w+(L t w*Y t w-D t w)+(-1)*I t w = (a w+L t w)*(Y t w-K t w)
    rw [hu] at hd
    nlinarith

end Asakura.Chapter6
