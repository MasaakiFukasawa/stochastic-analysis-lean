import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

open MeasureTheory Set
open scoped ENNReal
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- Integrate a tail bound to justify the exponential moments used for
inverse Asian denominators. The layer-cake integrand is written explicitly. -/
theorem exponential_moment_of_tail {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Z : Ω → ℝ)
    (hZ : Measurable Z) (hZpos : ∀ w, 0 ≤ Z w)
    (A b c : ℝ) (hA : 0 ≤ A) (hc : 0 < c) (hbc : c < b)
    (htail : ∀ t > 0, P {w | t < Z w} ≤ ENNReal.ofReal (A*Real.exp (-b*t))) :
    Integrable (fun w => Real.exp (c*Z w)) P := by
  let g := fun t : ℝ => c*Real.exp (c*t)
  have hg : Continuous g := by fun_prop
  have hint (z : ℝ) : (∫ t in 0..z,g t) = Real.exp (c*z)-1 := by
    have hd (t : ℝ) : HasDerivAt (fun x : ℝ => Real.exp (c*x)) (g t) t := by
      simpa only [g,id_eq,mul_one,mul_comm] using ((hasDerivAt_id t).const_mul c).exp
    simpa using intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t _ => hd t) (hg.intervalIntegrable 0 z)
  have hl := lintegral_comp_eq_lintegral_meas_lt_mul P
    (ae_of_all P hZpos) hZ.aemeasurable (fun t _ => hg.intervalIntegrable 0 t)
    (ae_of_all _ fun t => mul_nonneg hc.le (Real.exp_pos _).le)
  simp_rw [hint] at hl
  have hdom : Integrable (fun t : ℝ => A*c*Real.exp ((c-b)*t)) (volume.restrict (Ioi 0)) :=
    (integrableOn_exp_mul_Ioi (sub_neg.mpr hbc) 0).const_mul (A*c)
  have hdompos : ∀ᵐ t ∂volume.restrict (Ioi 0), 0 ≤ A*c*Real.exp ((c-b)*t) :=
    ae_of_all _ fun t => by positivity
  have hb : (∫⁻ w, ENNReal.ofReal (Real.exp (c*Z w)-1) ∂P) < ∞ := by
    rw [hl]
    apply lt_of_le_of_lt _ ((hasFiniteIntegral_iff_ofReal hdompos).mp hdom.hasFiniteIntegral)
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    calc
      P {w | t < Z w}*ENNReal.ofReal (g t) ≤
          ENNReal.ofReal (A*Real.exp (-b*t))*ENNReal.ofReal (g t) :=
        mul_le_mul' (htail t ht) le_rfl
      _ = ENNReal.ofReal (A*c*Real.exp ((c-b)*t)) := by
        rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ A*Real.exp (-b*t))]
        congr 1
        dsimp only [g]
        rw [show (A*Real.exp (-b*t))*(c*Real.exp (c*t)) =
          A*c*(Real.exp (-b*t)*Real.exp (c*t)) by ring,← Real.exp_add]
        congr 2
        ring
  have hi : Integrable (fun w => Real.exp (c*Z w)-1) P := by
    refine ⟨by fun_prop,(hasFiniteIntegral_iff_ofReal (ae_of_all P fun w => ?_)).mpr hb⟩
    exact sub_nonneg.mpr (Real.one_le_exp (mul_nonneg hc.le (hZpos w)))
  convert hi.add (integrable_const (1:ℝ)) using 1
  funext w
  exact (sub_add_cancel _ _).symm

end Asakura.Chapter12
