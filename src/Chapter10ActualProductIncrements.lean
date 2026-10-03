import Chapter10ActualStateProducts
import Chapter10ContinuousProductMartingale
import Mathlib.Tactic.LinearCombination

open MeasureTheory Set Filter
open scoped BigOperators NNReal ENNReal
namespace Asakura.Chapter10
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter8
set_option maxHeartbeats 2800000
set_option backward.isDefEq.respectTransparency false

/-- Actual Ito product increments with an integrable martingale residual.
The L2 state path estimate, rather than a fourth moment assumption, suffices. -/
theorem LinearStateWitness.product_increments {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d n : ℕ} (B : BrownianSystem P n)
    (A : ℝ → (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)) (hA : Continuous A)
    (G : Fin d → Fin n → ℝ → ℝ) (hG : ∀ i j,Continuous (G i j))
    (ξ : Ω → Fin d → ℝ) (hξ : Measurable[B.F ⊥] ξ) (hξ2 : MemLp ξ 2 P)
    (T : ℝ) (hT : 0≤T)
    (N : Fin d → Fin n → HalfClosedTime → Ω → ℝ)
    (X : Ω → C(Icc (0:ℝ) T,Fin d → ℝ))
    (h : LinearStateWitness P B A G ξ T hT N X) :
    ∃ (Z : Fin d → Fin d → HalfClosedTime → Ω → ℝ),
      (∀ i j,ContinuousMpWitness P B.F 1 (fun u w => Z i j (min (realTimeClamp T) u) w)) ∧
      ∀ i j (s t : Icc (0:ℝ) T),∀ᵐ w ∂P,
        X w t i*X w t j-X w s i*X w s j=
          (∫ u in s.val..t.val,X w (projIcc 0 T hT u) j*(A u (X w (projIcc 0 T hT u))) i)+
          (∫ u in s.val..t.val,X w (projIcc 0 T hT u) i*(A u (X w (projIcc 0 T hT u))) j)+
          (∫ u in s.val..t.val,∑ k,G i k u*G j k u)+
          (Z i j (realTimeClamp t.val) w-Z i j (realTimeClamp s.val) w) := by
  obtain ⟨Z,hinit,hZ,he⟩ := h.products P B A hA G hG ξ hξ hξ2 T hT N X
  have hq i j : Continuous (fun u => ∑ k,G i k u*G j k u) :=
    continuous_finset_sum _ (fun k _ => (hG i k).mul (hG j k))
  refine ⟨Z,?_,?_⟩
  · intro i j
    exact continuous_linear_product_stopped_martingale P B.F B.mono B.le T hT X h.moment
      A hA i j _ (hq i j) _ (hZ i j) (he i j)
  · intro i j s t
    filter_upwards [he i j s,he i j t] with w hs ht
    have hc : Continuous (fun u => X w (projIcc 0 T hT u)) := (X w).continuous.comp continuous_projIcc
    have hci k := (continuous_apply k).comp hc
    have hdi k := (continuous_apply k).comp (hA.clm_apply hc)
    have h1 := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
      (((hci j).mul (hdi i)).intervalIntegrable 0 s.val)
      (((hci j).mul (hdi i)).intervalIntegrable s.val t.val)
    have h2 := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
      (((hci i).mul (hdi j)).intervalIntegrable 0 s.val)
      (((hci i).mul (hdi j)).intervalIntegrable s.val t.val)
    have h3 := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
      ((hq i j).intervalIntegrable 0 s.val) ((hq i j).intervalIntegrable s.val t.val)
    simp only [Pi.mul_apply,Function.comp_def] at h1 h2
    linear_combination ht-hs-h1-h2-h3

end Asakura.Chapter10
