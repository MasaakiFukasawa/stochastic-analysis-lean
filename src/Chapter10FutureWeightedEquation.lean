import Chapter10WeightedStateEquation
import Chapter10MartingalePastOrthogonality

open MeasureTheory Set Filter
open scoped BigOperators NNReal ENNReal
namespace Asakura.Chapter10
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter8
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

/-- After conditioning against a past L2 variable, the future noise drops out
of the actual SDE and leaves a deterministic homogeneous integral equation. -/
theorem LinearStateWitness.future_weighted_equation {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d n : ℕ} (B : BrownianSystem P n)
    (A : ℝ → (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)) (hA : Continuous A)
    (K : ℝ≥0) (hAK : ∀ s,‖A s‖≤K)
    (G : Fin d → Fin n → ℝ → ℝ) (hG : ∀ i j,Continuous (G i j))
    (ξ : Ω → Fin d → ℝ) (hξ2 : MemLp ξ 2 P)
    (T : ℝ) (hT : 0≤T) (N : Fin d → Fin n → HalfClosedTime → Ω → ℝ)
    (X : Ω → C(Icc (0:ℝ) T,Fin d → ℝ))
    (h : LinearStateWitness P B A G ξ T hT N X)
    (s t : Icc (0:ℝ) T) (hst : s.val≤t.val)
    (η : Ω → ℝ) (hηm : Measurable[B.F (realTimeClamp s.val)] η) (hη : MemLp η 2 P) (i : Fin d) :
    (∫ w,η w*X w t i ∂P)=(∫ w,η w*X w s i ∂P)+
      ∫ u in s.val..t.val,∫ w,η w*(A u (X w (projIcc 0 T hT u))) i ∂P := by
  letI : MeasurableSpace Ω := m
  have hs := h.weighted_equation P B A hA K hAK G hG ξ hξ2 T hT N X η hη i s
  have ht := h.weighted_equation P B A hA K hAK G hG ξ hξ2 T hT N X η hη i t
  have hnoise : (∑ j,∫ w,η w*N i j (realTimeClamp t.val) w ∂P)=
      ∑ j,∫ w,η w*N i j (realTimeClamp s.val) w ∂P := by
    apply Finset.sum_congr rfl
    intro j _
    exact deterministic_noise_past_orthogonal P B j (G i j) (hG i j) (N i j)
      (h.noise i j) (h.ito i j) s.val t.val s.property.1 hst η hηm hη
  have hc := (past_weighted_drift_regular P T hT X h.measurable h.moment η hη A hA K hAK i).1
  have he := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hc.intervalIntegrable 0 s.val) (hc.intervalIntegrable s.val t.val)
  rw [hnoise] at ht
  linarith

end Asakura.Chapter10
