import Chapter3BoundedContinuousQuadraticApproximation
import Chapter3ApproximationLocality

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter3Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

/-- A pathwise assertion about the manuscript's actual quadratic sums and
its actual Stieltjes integral, including existence of the measure's data. -/
def QuadraticPathApproximation
    {T : EReal} [Fact (0 ≤ T)] (X Q H : ClosedTime T → ℝ)
    (τ : ℕ → ℕ → ClosedTime T) (d : ℝ) (hd : 0 ≤ d) : Prop :=
  ∃ (hQm : MonotoneOn (fun r => Q (realTimeClamp r)) (Icc 0 d))
    (hQr : ∀ x, x ∈ Icc 0 d → ContinuousWithinAt (fun r => Q (realTimeClamp r)) (Icc 0 d ∩ Ici x) x),
  TendstoUniformly
    (fun n t => ∑' j, H (τ n j)*(X (min (τ n (j+1)) (min (realTimeClamp d) t))-
      X (min (τ n j) (min (realTimeClamp d) t)))^2)
    (fun t : ClosedTime T => ∫ r in Iic (finitePrefixTime d hd t).val, H (realTimeClamp r)
      ∂(intervalStieltjes 0 d hd (fun r => Q (realTimeClamp r)) hQm hQr).measure) atTop

/-- Transfer approximation through agreement on a finite prefix. In
particular this justifies undoing a localization for an individual path. -/
theorem quadratic_path_approximation_congr
    {T : EReal} [Fact (0 ≤ T)] (X Q H Y R K : ClosedTime T → ℝ)
    (τ : ℕ → ℕ → ClosedTime T) (hτ : ∀ n, Monotone (τ n))
    (d : ℝ) (hd : 0 ≤ d)
    (hQm : MonotoneOn (fun r => Q (realTimeClamp r)) (Icc 0 d))
    (hQr : ∀ x, x ∈ Icc 0 d → ContinuousWithinAt (fun r => Q (realTimeClamp r)) (Icc 0 d ∩ Ici x) x)
    (hX : ∀ t, t ≤ realTimeClamp d → X t = Y t)
    (hQ : ∀ t, t ≤ realTimeClamp d → Q t = R t)
    (hH : ∀ t, t ≤ realTimeClamp d → H t = K t)
    (ha : QuadraticPathApproximation Y R K τ d hd) :
    QuadraticPathApproximation X Q H τ d hd := by
  obtain ⟨hRm,hRr,ha⟩ := ha
  refine ⟨hQm,hQr,?_⟩
  have hs : (fun n t => ∑' j, H (τ n j)*(X (min (τ n (j+1)) (min (realTimeClamp d) t))-
      X (min (τ n j) (min (realTimeClamp d) t)))^2) =
      (fun n t => ∑' j, K (τ n j)*(Y (min (τ n (j+1)) (min (realTimeClamp d) t))-
      Y (min (τ n j) (min (realTimeClamp d) t)))^2) := by
    funext n t
    exact quadratic_sum_congr_on_prefix (τ n) (hτ n) X Y H K (realTimeClamp d) t hX hH
  have hi : (fun t : ClosedTime T => ∫ r in Iic (finitePrefixTime d hd t).val, H (realTimeClamp r)
      ∂(intervalStieltjes 0 d hd (fun r => Q (realTimeClamp r)) hQm hQr).measure) =
      (fun t : ClosedTime T => ∫ r in Iic (finitePrefixTime d hd t).val, K (realTimeClamp r)
      ∂(intervalStieltjes 0 d hd (fun r => R (realTimeClamp r)) hRm hRr).measure) := by
    funext t
    exact stieltjes_integral_congr_on_prefix d hd _ _ _ _ hQm hRm hQr hRr
      (fun r hr => hQ _ (real_time_clamp_mono hr.2))
      (fun r hr => hH _ (real_time_clamp_mono hr.2)) _
  rw [hs,hi]
  exact ha

end Asakura.Chapter3Complete
#print axioms Asakura.Chapter3Complete.quadratic_path_approximation_congr
