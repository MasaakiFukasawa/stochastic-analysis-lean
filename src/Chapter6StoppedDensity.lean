import Chapter6DensityMartingale
import FullAuditContinuousOptional

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
namespace Asakura.Chapter6
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

/-- Bayes' formula at two ordered stopping times. The stopped density is
identified by the already proved continuous optional-sampling theorem. -/
theorem stopped_density_transport
    {Ω : Type*} {m : MeasurableSpace Ω}
    (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {T : EReal} (hT : 0 ≤ T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t ≤ m)
    (d : Ω → ℝ≥0) (hd : Measurable d)
    (hdi : Integrable (fun w => (d w : ℝ)) P)
    (hp : ∀ᵐ w ∂P,0 < (d w : ℝ))
    (hQ : Q = P.withDensity (fun w => (d w : ℝ≥0∞)))
    (M : ClosedTime T → Ω → ℝ) (hMa : ∀ t,Measurable[F t] (M t))
    (hMc : ∀ w,Continuous (fun t => M t w))
    (hME : ∀ t,M t =ᵐ[P] P[(fun w => (d w : ℝ))|F t])
    (σ τ : Ω → ClosedTime T)
    (hσ : ∀ t,MeasurableSet[F t] {w | σ w ≤ t})
    (hτ : ∀ t,MeasurableSet[F t] {w | τ w ≤ t}) (hst : ∀ w,σ w ≤ τ w)
    (Y : Ω → ℝ) (hY : StronglyMeasurable[writtenStoppedSpace m F τ hτ] Y)
    (hi : Integrable Y Q) :
    Integrable (fun w => M (τ w) w * Y w) P ∧
    P[(fun w => M (τ w) w * Y w)|writtenStoppedSpace m F σ hσ] =ᵐ[P]
      (fun w => M (σ w) w * Q[Y|writtenStoppedSpace m F σ hσ] w) := by
  have hσm : writtenStoppedSpace m F σ hσ ≤ m := fun _ h => h.1
  have hτm : writtenStoppedSpace m F τ hτ ≤ m := fun _ h => h.1
  have he (ρ : Ω → ClosedTime T) (hρ : ∀ t,MeasurableSet[F t] {w | ρ w ≤ t}) :=
    continuous_closed_optional_written P hT F hF hle ρ hρ M hMa
      (fun w _ => (hMc w).continuousAt.continuousWithinAt) hd.coe_nnreal_real hdi hME
  have heτ := he τ hτ
  have heσ := he σ hσ
  have hh := conditional_density_product P Q hτm d hd hdi hQ Y hY hi
  have hprod : (fun w => M (τ w) w * Y w) =ᵐ[P]
      (fun w => P[(fun w => (d w : ℝ))|writtenStoppedSpace m F τ hτ] w * Y w) := by
    filter_upwards [heτ] with w hw
    rw [hw]
  refine ⟨hh.1.congr hprod.symm,?_⟩
  have ht := density_conditional_transport P Q
    (written_stoppedSpace_mono m F σ τ hσ hτ hst) hτm d hd hdi hp hQ Y hY hi
  apply ((condExp_congr_ae hprod).trans ht).trans
  filter_upwards [heσ] with w hw
  rw [hw]

end Asakura.Chapter6
