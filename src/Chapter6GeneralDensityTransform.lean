import Chapter6DensityLogarithm
import Chapter6InitialShiftedProduct
import Chapter6OpenDensityReverse

open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal
namespace Asakura.Chapter6
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete
set_option maxHeartbeats 3500000
set_option backward.isDefEq.respectTransparency false

/-- General positive-density drift correction, allowing a random M_0.
The correction is constructed as the signed Stieltjes integral of 1/M
against the actual covariance of M-M_0 with Y. -/
theorem general_density_transform {Ω : Type*} {m : MeasurableSpace Ω}
    (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {T : EReal} [Fact (0≤T)] (hT : 0<T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t N,MeasurableSet[m] N → P N=0 → MeasurableSet[F t] N)
    (d : Ω → ℝ≥0) (hd : Measurable d) (hdi : Integrable (fun w => (d w:ℝ)) P)
    (hp : ∀ᵐ w ∂P,0<(d w:ℝ)) (hQ : Q=P.withDensity (fun w => (d w:ℝ≥0∞)))
    (M : ClosedTime T → Ω → ℝ) (hMa : ∀ t,Measurable[F t] (M t))
    (hMc : ∀ w t,t<⊤ → ContinuousAt (fun s => M s w) t) (hMp : ∀ t w,0<M t w)
    (hME : ∀ t,M t=ᵐ[P] P[(fun w => (d w:ℝ))|F t])
    (Y C : ClosedTime T → Ω → ℝ) (hY : LocalMProcessWitness P F Y)
    (hC : LocalCovarianceWitness P F (fun t w => M t w-M ⊥ w) Y C)
    (c : ℕ → ℝ) (hc : ∀ n,0≤c n) (hcm : Monotone c) (hcT : ∀ n,(c n:EReal)<T)
    (hcc : ∀ t,t<⊤ → ∃ n,t<realTimeClamp (T := T) (c n)) :
    ∃ K,AdaptedLocalVariationWitness F K ∧
      (∀ w t,t<⊤ → ContinuousAt (fun s => K s w) t) ∧
      VariationIntegralFormula P c hc C (fun z => (M (realTimeClamp z.2) z.1)⁻¹) K ∧
      LocalMProcessWitness Q F (fun t w => Y t w-K t w) := by
  let L := fun t w => M t w-M ⊥ w
  have hL := centered_density_local P hT F hF hle _ hdi M hMa hMc hME
  obtain ⟨R,hR,hRI,hLI⟩ := density_stochastic_logarithm P hT F hF hle hnull _ hdi M hMa hMc hMp hME
  have hCv := covariance_adapted_variation P F hF hle hL hY hC
  have hCc := local_covariance_path_continuous P F L Y C hL hY hC
  have hir := open_process_real_regularity F (fun t w => (M t w)⁻¹)
    (fun t _ => (hMa t).inv) (fun w t ht => (hMc w t ht).inv₀ (hMp t w).ne')
  obtain ⟨J,hJv,hJc,hJI⟩ := continuous_adapted_variation_exists P F hF hnull c hc hcm hcT hcc
    C hCv hCc (fun z => (M (realTimeClamp z.2) z.1)⁻¹) hir.1 hir.2
  have hMm w : Measurable (fun r => M (realTimeClamp r) w) := open_path_real_measurable _ (hMc w)
  obtain ⟨K,hK,hKJ⟩ := ito_covariance_variation_identity P F L Y R C J hY hR hC
    (fun z => (M (realTimeClamp z.2) z.1)⁻¹) (fun w => (hMm w).inv) hRI c hc hcT hcc hJI
  have hKv := covariance_adapted_variation P F hF hle hR hY hK
  have hKc := local_covariance_path_continuous P F R Y K hR hY hK
  have hKI := hJI.congr_integral P c hc hcT C J K _ (hKJ.mono (fun w hw t ht => (hw t ht).symm))
  have hLI' : ItoCovarianceFormula P F R (fun z => M ⊥ z.1+L (realTimeClamp z.2) z.1) L := by
    apply hLI.congr_on_time_domain P F R L _ _
    intro w r _ _
    dsimp [L]
    ring
  have hsum : (fun t w => M ⊥ w+L t w)=M := by funext t w; dsimp [L]; ring
  have hprod := initial_shifted_corrected_product_local P hT F hF hle hnull R Y L K (M ⊥)
    (hMa ⊥) hR hY hL hK hLI' (fun w => by simpa only [congrFun (congrFun hsum _) w] using hMm w)
  have hMX : LocalMProcessWitness P F (fun t w => M t w*(Y t w-K t w)) := by
    convert hprod using 1
    funext t w
    dsimp [L]
    ring
  obtain ⟨u,_,_,_,hum,hut,huc⟩ := positive_real_time_exhaustion hT
  refine ⟨K,hKv,hKc,hKI,?_⟩
  exact open_process_local_of_density_product P Q hT F hF hle d hd hdi hp hQ M _ hMa hMc hMp hME
    (fun t ht => (hY.adapted P F t ht).sub (hK.adapted P F hR hY t ht)) hMX
    (fun n => realTimeClamp (u n)) hum.monotone hut huc

end Asakura.Chapter6
