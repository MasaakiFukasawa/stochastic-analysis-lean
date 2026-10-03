import Chapter12GaussianArrayNorm
import Mathlib.MeasureTheory.Integral.MeanInequalities

open MeasureTheory
open scoped ENNReal
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

/-- The finite-factor Hölder step in the moment proof, with no coordinate
count in the constant. Extended integrals avoid hidden integrability inputs. -/
theorem finite_holder_moment_lintegral {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (m : ℕ) (hm : 0<m) (f : Fin m → Ω → ℝ)
    (hf : ∀ j,Measurable (f j)) (hn : ∀ j x,0≤f j x) :
    (∫⁻ x,ENNReal.ofReal (∏ j,f j x) ∂P)≤
      ∏ j,(∫⁻ x,ENNReal.ofReal (f j x)^m ∂P)^((m:ℝ)⁻¹) := by
  have hmR : (m:ℝ)≠0 := by exact_mod_cast hm.ne'
  have he (j : Fin m) (x : Ω) :
      (ENNReal.ofReal (f j x)^m)^((m:ℝ)⁻¹)=ENNReal.ofReal (f j x) := by
    rw [← ENNReal.rpow_natCast,← ENNReal.rpow_mul,mul_inv_cancel₀ hmR,ENNReal.rpow_one]
  have hh := ENNReal.lintegral_prod_norm_pow_le (μ:=P) Finset.univ
    (f:=fun j x => ENNReal.ofReal (f j x)^m)
    (fun j _ => ((hf j).ennreal_ofReal.pow_const m).aemeasurable)
    (p:=fun _ => (m:ℝ)⁻¹) (by simp [hmR]) (fun _ _ => inv_nonneg.mpr (Nat.cast_nonneg _))
  simp only [he] at hh
  simpa only [ENNReal.ofReal_prod_of_nonneg (fun j _ => hn j _)] using hh

end Asakura.Chapter12
