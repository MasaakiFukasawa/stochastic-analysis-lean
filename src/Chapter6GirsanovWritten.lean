import Chapter6GirsanovProduct
import Chapter6OpenDensityReverse
import Chapter6ExponentialClosed

open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal
namespace Asakura.Chapter6
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete
set_option maxHeartbeats 3500000
set_option backward.isDefEq.respectTransparency false

/-- Girsanov--Maruyama from the original local martingales, actual brackets,
mean-one exponential and density measure. The corrected process is proved
local by the product cancellation and the proved reverse Bayes criterion. -/
theorem girsanov_maruyama_written
    {Ω : Type*} {m : MeasurableSpace Ω}
    (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t ≤ m)
    (hnull : ∀ t N,MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (Z C : ClosedTime T → Ω → ℝ) (hZ : LocalMProcessWitness P F Z)
    (hC : LocalCovarianceWitness P F Z Z C)
    (τ : Ω → ClosedTime T) (hτ : ∀ t,MeasurableSet[F t] {w | τ w ≤ t})
    (hτt : ∀ w,τ w < ⊤)
    (hmean : (∫ w,Real.exp (Z (τ w) w-C (τ w) w/2) ∂P) = 1)
    (hQ : Q = P.withDensity (fun w => ENNReal.ofReal (Real.exp (Z (τ w) w-C (τ w) w/2))))
    (Y K : ClosedTime T → Ω → ℝ) (hY : LocalMProcessWitness P F Y)
    (hK : LocalCovarianceWitness P F (fun t w => Z (min (τ w) t) w) Y K) :
    LocalMProcessWitness Q F (fun t w => Y t w-K t w) := by
  let Z' := fun t w => Z (min (τ w) t) w
  let C' := fun t w => C (min (τ w) t) w
  let M := fun t w => Real.exp (Z' t w-C' t w/2)
  let L := fun t w => M t w-1
  have hZ' := hZ.stopped P F hF hle τ hτ
  have hC' := hC.stopped P F hF hle τ hτ
  obtain ⟨hMa,hMi,hMc,_,hME⟩ := stochastic_exponential_closed_martingale P hT F hF hle hnull
    Z C hZ hC τ hτ hτt hmean
  obtain ⟨hL,hLI⟩ := stochastic_exponential_constructed P hT F hF hle hnull Z' C' hZ' hC'
  have hLInt : ItoCovarianceFormula P F Z' (fun z => 1+L (realTimeClamp z.2) z.1) L := by
    apply hLI.congr_on_time_domain P F Z' L _ _
    intro w r _ _
    dsimp [L,M]
    ring
  have hLm w : Measurable (fun r => 1+L (realTimeClamp r) w) := by
    have hh := (hMc w).comp real_time_clamp_continuous
    have he : (fun r => 1+L (realTimeClamp r) w) = fun r => M (realTimeClamp r) w := by
      funext r
      dsimp [L]
      ring
    rw [he]
    exact hh.measurable
  have hprod := girsanov_corrected_product_local P hT F hF hle hnull Z' Y L K hZ' hY hL hK hLInt hLm
  have hMX : LocalMProcessWitness P F (fun t w => M t w*(Y t w-K t w)) := by
    convert hprod using 1
    funext t w
    dsimp [L]
    ring
  let d := fun w => (M ⊤ w).toNNReal
  have hd : Measurable d := ((hMa ⊤).mono (hle ⊤) le_rfl).real_toNNReal
  have he : (fun w => (d w : ℝ)) = M ⊤ := by
    funext w
    exact Real.coe_toNNReal _ (Real.exp_pos _).le
  have hdi : Integrable (fun w => (d w : ℝ)) P := by rw [he]; exact hMi ⊤
  have hp : ∀ᵐ w ∂P,0 < (d w : ℝ) := by
    apply ae_of_all
    intro w
    rw [congrFun he w]
    exact Real.exp_pos _
  have hQ' : Q = P.withDensity (fun w => (d w : ℝ≥0∞)) := by
    change Q = P.withDensity (fun w => ENNReal.ofReal (M ⊤ w))
    simpa only [M,Z',C',min_top_right] using hQ
  have hME' : ∀ t,M t =ᵐ[P] P[(fun w => (d w : ℝ))|F t] := by
    intro t
    rw [he]
    exact hME t
  obtain ⟨u,_,_,_,hum,hut,huc⟩ := positive_real_time_exhaustion hT
  exact open_process_local_of_density_product P Q hT F hF hle d hd hdi hp hQ' M _ hMa
    (fun w t _ => (hMc w).continuousAt) (fun _ _ => Real.exp_pos _) hME'
    (fun t ht => (hY.adapted P F t ht).sub (hK.adapted P F hZ' hY t ht)) hMX
    (fun n => realTimeClamp (u n)) hum.monotone hut huc

end Asakura.Chapter6
