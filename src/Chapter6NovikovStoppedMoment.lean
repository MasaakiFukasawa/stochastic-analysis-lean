import Chapter6NovikovHolder
import Chapter6PositiveLocalMean
import Chapter3OpenProcessRegularity

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter6
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

/-- The quadratic variation of a scalar multiple is obtained directly
from the defining product-minus-variation local martingale. -/
theorem scaled_self_covariance
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    (Z C : ClosedTime T → Ω → ℝ) (hC : LocalCovarianceWitness P F Z Z C) (a : ℝ) :
    LocalCovarianceWitness P F (fun t w => a*Z t w) (fun t w => a*Z t w)
      (fun t w => a^2*C t w) := by
  refine ⟨?_,hC.variation.smul F (a^2)⟩
  convert hC.defect.smul P F (a^2) using 1
  funext t w
  ring

/-- The uniform terminal Lp estimate in the Novikov proof. The expectation
of the tilted exponential is proved by conditional Fatou, not assumed. -/
theorem novikov_stopped_moment
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t ≤ m)
    (hnull : ∀ t N,MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (Z C : ClosedTime T → Ω → ℝ) (hZ : LocalMProcessWitness P F Z)
    (hC : LocalCovarianceWitness P F Z Z C)
    (σ : Ω → ClosedTime T) (hσ : ∀ t,MeasurableSet[F t] {w | σ w ≤ t})
    (hσt : ∀ w,σ w < ⊤)
    (V : Ω → ℝ) (hV : ∀ᵐ w ∂P,C (σ w) w ≤ V w)
    (α p γ : ℝ) (ha : 1 < α) (hg0 : 0 ≤ γ)
    (hg : γ = p*((α*p-1)/(α-1))*(α/2)) :
    (∫⁻ w,ENNReal.ofReal (Real.exp (p*(Z (σ w) w-C (σ w) w/2))) ∂P) ≤
      (∫⁻ w,ENNReal.ofReal (Real.exp (γ*V w)) ∂P)^((α-1)/α) := by
  have hscaled := scaled_self_covariance P F Z C hC (α*p)
  have hE := stochastic_exponential_local P hT F hF hle hnull _ _
    (hZ.smul P F (α*p)) hscaled
  have hbound : ∀ᵐ w ∂P,∀ t,t < ⊤ → -(1:ℝ) ≤
      Real.exp (α*p*Z t w-(α*p)^2*C t w/2)-1 := by
    exact .of_forall fun w t _ => by linarith [Real.exp_pos (α*p*Z t w-(α*p)^2*C t w/2)]
  have hmean := (positive_shifted_local_mean_bound P F hF hle _ hE hbound σ hσ hσt).2
  simp only [sub_add_cancel] at hmean
  have hZsm := (open_process_stopped_regular F hF Z (hZ.adapted P F) (hZ.path P F) σ hσ hσt).1 ⊤
  have hCsm := (hC.stopped_regular P F hF hle hZ hZ σ hσ hσt).1 ⊤
  simp only [min_top_right] at hZsm hCsm
  have hh := novikov_holder_bound P (fun w => Z (σ w) w) (fun w => C (σ w) w)
    (hZsm.mono (hle ⊤) le_rfl) (hCsm.mono (hle ⊤) le_rfl) α p γ ha hg hmean
  apply hh.trans
  apply ENNReal.rpow_le_rpow _ (by positivity : 0 ≤ (α-1)/α)
  apply lintegral_mono_ae
  filter_upwards [hV] with w hw
  exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hw hg0))

end Asakura.Chapter6
