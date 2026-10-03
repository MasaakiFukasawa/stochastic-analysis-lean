import Chapter10StateRealEquation
import Chapter10PastWeightedDrift
import Chapter10NoiseMartingale

open MeasureTheory Set Filter
open scoped BigOperators NNReal ENNReal
namespace Asakura.Chapter10
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter8
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

/-- Multiply the actual state equation by an arbitrary L2 variable and take
expectations. All drift and noise products are proved integrable. -/
theorem LinearStateWitness.weighted_equation {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d n : ℕ} (B : BrownianSystem P n)
    (A : ℝ → (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)) (hA : Continuous A)
    (K : ℝ≥0) (hAK : ∀ s,‖A s‖≤K)
    (G : Fin d → Fin n → ℝ → ℝ) (hG : ∀ i j,Continuous (G i j))
    (ξ : Ω → Fin d → ℝ) (hξ2 : MemLp ξ 2 P)
    (T : ℝ) (hT : 0≤T) (N : Fin d → Fin n → HalfClosedTime → Ω → ℝ)
    (X : Ω → C(Icc (0:ℝ) T,Fin d → ℝ))
    (h : LinearStateWitness P B A G ξ T hT N X)
    (η : Ω → ℝ) (hη : MemLp η 2 P) (i : Fin d) (r : Icc (0:ℝ) T) :
    (∫ w,η w*X w r i ∂P)=(∫ w,η w*ξ w i ∂P)+
      (∫ s in 0..r.val,∫ w,η w*(A s (X w (projIcc 0 T hT s))) i ∂P)+
      ∑ j,∫ w,η w*N i j (realTimeClamp r.val) w ∂P := by
  have hn2 j : MemLp (N i j (realTimeClamp r.val)) 2 P := by
    have hh := (deterministic_noise_martingale P B j (G i j) (hG i j) (N i j)
      (h.noise i j) (h.ito i j) r.val r.property.1).moment (realTimeClamp r.val)
    simpa only [min_self] using hh
  have hn j : Integrable (fun w => η w*N i j (realTimeClamp r.val) w) P := hη.integrable_mul (hn2 j)
  have hξi : MemLp (fun w => ξ w i) 2 P := by
    apply hξ2.norm.of_le ((continuous_apply i).comp_aestronglyMeasurable hξ2.aestronglyMeasurable)
    exact ae_of_all _ fun w => by simpa only [norm_norm] using norm_le_pi_norm (ξ w) i
  have hiξ : Integrable (fun w => η w*ξ w i) P := hη.integrable_mul hξi
  obtain ⟨hi,hfi⟩ := (past_weighted_drift_regular P T hT X h.measurable h.moment η hη A hA K hAK i).2 r.val r.property.1
  have hsum : Integrable (fun w => ∑ j,η w*N i j (realTimeClamp r.val) w) P :=
    integrable_finsetSum _ (fun j _ => hn j)
  have he : (fun w => η w*X w r i)=(fun w => η w*ξ w i+
      (∫ s in 0..r.val,η w*(A s (X w (projIcc 0 T hT s))) i)+
      ∑ j,η w*N i j (realTimeClamp r.val) w) := by
    funext w
    have hh := congrArg (fun x => η w*x) (h.real_equation P B A G ξ T hT N X w r i)
    simpa only [mul_add,Finset.mul_sum,intervalIntegral.integral_const_mul] using hh
  have hadd : Integrable (fun w => η w*ξ w i+∫ s in 0..r.val,η w*(A s (X w (projIcc 0 T hT s))) i) P := hiξ.add hi
  rw [he,integral_add hadd hsum,integral_add hiξ hi,integral_finsetSum _ (fun j _ => hn j),hfi]

end Asakura.Chapter10
