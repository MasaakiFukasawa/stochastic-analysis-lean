import Chapter12AsianVegaEnvelope

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

noncomputable def asianVegaPathEnvelope (x r T L : ℝ) (f : C(Icc (0:ℝ) T,ℝ)) : ℝ :=
  (|x| * Real.exp ((|r| +L^2/2)*T)*(1+L*T))*Real.exp ((L+1)*‖f‖)

theorem asian_average_vega_uniform_bound (x r T L σ : ℝ)
    (hT : 0 < T) (hL : 0 ≤ L) (hσ : |σ| ≤ L)
    (f : C(Icc (0:ℝ) T,ℝ)) :
    |((∫ s in 0..T,(x*Real.exp ((r-σ^2/2)*s+σ*f (projIcc 0 T hT.le s)))*
      (f (projIcc 0 T hT.le s)-σ*s))/T)| ≤ asianVegaPathEnvelope x r T L f := by
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0:ℝ)) (b := T) (C := asianVegaPathEnvelope x r T L f)
    (f := fun s => (x*Real.exp ((r-σ^2/2)*s+σ*f (projIcc 0 T hT.le s)))*
      (f (projIcc 0 T hT.le s)-σ*s)) (fun s hs => by
      have hs' : s ∈ Icc (0:ℝ) T := by
        rw [uIoc_of_le hT.le] at hs
        exact ⟨hs.1.le,hs.2⟩
      have hh := stock_volatility_derivative_uniform_bound x r T L σ hT.le hL hσ f ⟨s,hs'⟩
      simpa only [Real.norm_eq_abs,stockPathValue,asianVegaPathEnvelope,projIcc_of_mem hT.le hs'] using hh)
  rw [Real.norm_eq_abs,sub_zero,abs_of_pos hT] at hi
  rw [abs_div,abs_of_pos hT]
  exact (div_le_iff₀ hT).mpr hi

theorem asian_vega_envelope_memLp {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : ℝ≥0 → Ω → ℝ)
    (hB : IsPreBrownianReal B P) (hm : ∀ t, Measurable (B t))
    (hc : ∀ w, Continuous (fun t => B t w)) (T : ℝ≥0)
    (X : Ω → C(Icc (0:ℝ) T,ℝ)) (hXm : Measurable X)
    (he : ∀ w (s : Icc (0:ℝ) T), X w s = B ⟨s.val,s.property.1⟩ w)
    (x r L : ℝ) (p : ℝ≥0∞) (hp : p ≠ ⊤) :
    MemLp (fun w => asianVegaPathEnvelope x r T L (X w)) p P := by
  exact (brownian_path_exponential_memLp P B hB hm hc T X hXm he (L+1) p hp).const_mul _

end Asakura.Chapter12
