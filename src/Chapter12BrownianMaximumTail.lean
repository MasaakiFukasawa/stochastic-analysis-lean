import Chapter12BrownianExponentialTail
import Mathlib.Topology.ContinuousMap.Compact

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false

/-- Apply the exponential maximal bound to B and -B and take their union.
The path norm is the actual supremum over the whole time interval. -/
theorem brownian_path_norm_tail {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : ℝ≥0 → Ω → ℝ)
    (hB : IsPreBrownianReal B P) (hm : ∀ t, Measurable (B t))
    (hc : ∀ w, Continuous (fun t => B t w)) (T : ℝ≥0)
    (X : Ω → C(Icc (0:ℝ) T,ℝ))
    (he : ∀ w (s : Icc (0:ℝ) T), X w s = B ⟨s.val,s.property.1⟩ w)
    (a z : ℝ) (ha : 0 < a) (hz : 0 < z) :
    P {w | z < ‖X w‖} ≤ ENNReal.ofReal (2*Real.exp (-a*z+a^2*T/2)) := by
  let Eplus := {w | ∃ t : ℝ≥0, t ≤ T ∧ a*z ≤ a*B t w}
  let Eminus := {w | ∃ t : ℝ≥0, t ≤ T ∧ a*z ≤ (-a)*B t w}
  have hsub : {w | z < ‖X w‖} ⊆ Eplus ∪ Eminus := by
    intro w hw
    have hn : ¬∀ s, ‖X w s‖ ≤ z := by
      intro hs
      exact (not_le.mpr hw) ((ContinuousMap.norm_le _ hz.le).mpr hs)
    push Not at hn
    obtain ⟨s,hs⟩ := hn
    rw [Real.norm_eq_abs,lt_abs] at hs
    rcases hs with hs | hs
    · left
      refine ⟨⟨s.val,s.property.1⟩,s.property.2,?_⟩
      rw [← he]
      exact mul_le_mul_of_nonneg_left hs.le ha.le
    · right
      refine ⟨⟨s.val,s.property.1⟩,s.property.2,?_⟩
      rw [← he]
      nlinarith
  have hp := brownian_linear_hitting_bound P B hB hm hc T a (a*z)
  have hn := brownian_linear_hitting_bound P B hB hm hc T (-a) (a*z)
  have hr : P.real {w | z < ‖X w‖} ≤ 2*Real.exp (-a*z+a^2*T/2) := by
    calc
      _ ≤ P.real (Eplus ∪ Eminus) := measureReal_mono hsub
      _ ≤ P.real Eplus+P.real Eminus := measureReal_union_le _ _
      _ ≤ Real.exp (-(a*z)+a^2*T/2)+Real.exp (-(a*z)+(-a)^2*T/2) := add_le_add hp hn
      _ = _ := by simp only [neg_sq,neg_mul]; ring
  have hr' := ENNReal.ofReal_le_ofReal hr
  rw [ofReal_measureReal (measure_ne_top P _)] at hr'
  exact hr'

/-- Optimizing the exponential parameter gives the Gaussian tail quoted
in the manuscript. -/
theorem brownian_path_norm_gaussian_tail {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : ℝ≥0 → Ω → ℝ)
    (hB : IsPreBrownianReal B P) (hm : ∀ t, Measurable (B t))
    (hc : ∀ w, Continuous (fun t => B t w)) (T : ℝ≥0) (hT : 0 < T)
    (X : Ω → C(Icc (0:ℝ) T,ℝ))
    (he : ∀ w (s : Icc (0:ℝ) T), X w s = B ⟨s.val,s.property.1⟩ w)
    (z : ℝ) (hz : 0 < z) :
    P {w | z < ‖X w‖} ≤ ENNReal.ofReal (2*Real.exp (-z^2/(2*T))) := by
  have ht : (0:ℝ) < T := hT
  have h := brownian_path_norm_tail P B hB hm hc T X he (z/T) z (div_pos hz ht) hz
  convert h using 2
  congr 1
  congr 1
  field_simp
  <;> ring

end Asakura.Chapter12
