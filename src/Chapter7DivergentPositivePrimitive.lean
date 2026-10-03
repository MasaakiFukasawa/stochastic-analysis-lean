import Chapter7BrownianOccupationWritten
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter7
set_option maxHeartbeats 1800000

/-- Infinite positive time integral means that its continuous finite-time
primitive is unbounded, the exact clock hypothesis required for inversion. -/
theorem divergent_positive_primitive
    (f : ℝ → ℝ) (hf : Continuous f) (hp : ∀ r,0 ≤ f r)
    (hdiv : (∫⁻ r in Ici (0:ℝ),ENNReal.ofReal (f r)) = ∞) :
    ∀ R : ℝ,∃ t : ℝ,0 ≤ t ∧ R < ∫ r in 0..t,f r := by
  intro R
  by_contra h
  have hb t (ht : 0 ≤ t) : (∫ r in 0..t,f r) ≤ R := by
    exact le_of_not_gt (fun hi => h ⟨t,ht,hi⟩)
  have hi : IntegrableOn f (Ioi (0:ℝ)) := by
    apply integrableOn_Ioi_of_intervalIntegral_norm_bounded (b := fun n : ℕ => (n:ℝ)+1) R 0
      (fun n => (hf.intervalIntegrable 0 ((n:ℝ)+1)).1)
      (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop)
    apply Eventually.of_forall
    intro n
    simpa only [Real.norm_eq_abs,abs_of_nonneg (hp _)] using hb ((n:ℝ)+1) (by positivity)
  have hi' : IntegrableOn f (Ici (0:ℝ)) := (integrableOn_Ici_iff_integrableOn_Ioi (by finiteness)).mpr hi
  have he := ofReal_integral_eq_lintegral_ofReal hi' (ae_of_all _ hp)
  rw [hdiv] at he
  exact ENNReal.ofReal_ne_top he

end Asakura.Chapter7
