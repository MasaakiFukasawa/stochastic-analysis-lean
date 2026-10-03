import Chapter6CenteredDensityLocal
import Chapter3IdentityItoIntegral
import Chapter3OpenPathMeasurable
import Chapter2ItoAssociativity
import Chapter2StochasticFubiniPrinted

open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal
namespace Asakura.Chapter6
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false

/-- Construct the stochastic logarithm of a positive conditional density,
then prove the inverse Ito-integral identity by associativity. -/
theorem density_stochastic_logarithm {Ω : Type*} {m : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] {T : EReal} [Fact (0≤T)] (hT : 0<T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t N,MeasurableSet[m] N → P N=0 → MeasurableSet[F t] N)
    (D : Ω → ℝ) (hD : Integrable D P) (M : ClosedTime T → Ω → ℝ)
    (hMa : ∀ t,Measurable[F t] (M t))
    (hMc : ∀ w t,t<⊤ → ContinuousAt (fun s => M s w) t)
    (hMp : ∀ t w,0<M t w)
    (hME : ∀ t,M t=ᵐ[P] P[D|F t]) :
    let L := fun t w => M t w-M ⊥ w
    ∃ R,LocalMProcessWitness P F R ∧
      ItoCovarianceFormula P F L (fun z => (M (realTimeClamp z.2) z.1)⁻¹) R ∧
      ItoCovarianceFormula P F R (fun z => M (realTimeClamp z.2) z.1) L := by
  let L := fun t w => M t w-M ⊥ w
  have hL := centered_density_local P hT F hF hle D hD M hMa hMc hME
  have hr := open_process_real_regularity F M (fun t _ => hMa t) hMc
  have hir := open_process_real_regularity F (fun t w => (M t w)⁻¹)
    (fun t _ => (hMa t).inv) (fun w t ht => (hMc w t ht).inv₀ (hMp t w).ne')
  obtain ⟨R,hR,hRI⟩ := continuous_adapted_ito_exists P hT F hF hle hnull L hL (fun z => (M (realTimeClamp z.2) z.1)⁻¹) hir.1 hir.2
  obtain ⟨N,hN,hNI⟩ := continuous_adapted_ito_exists P hT F hF hle hnull R hR (fun z => M (realTimeClamp z.2) z.1) hr.1 hr.2
  have hMm w : Measurable (fun r => M (realTimeClamp r) w) :=
    open_path_real_measurable _ (hMc w)
  have hId := identity_ito_integral P hT F hF hle hnull L hL
  have hId' : ItoCovarianceFormula P F L
      (fun z => M (realTimeClamp z.2) z.1*(M (realTimeClamp z.2) z.1)⁻¹) L := by
    apply hId.congr_on_time_domain P F L L _ _
    intro w r _ _
    exact (mul_inv_cancel₀ (hMp _ _).ne').symm
  have he := ito_integral_associativity P hT F hF hle hnull L R N L
    (fun z => (M (realTimeClamp z.2) z.1)⁻¹) (fun z => M (realTimeClamp z.2) z.1)
    hL hR hN hL (fun w => (hMm w).inv) hMm hRI hNI hId'
  exact ⟨R,hR,hRI,hNI.congr_integral P F hF hle R N L _ hN hL he⟩

end Asakura.Chapter6
