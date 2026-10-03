import Chapter12AsianVolatilityFunctions

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

theorem asian_path_average_bound (x r T σ : ℝ) (hT : 0 < T)
    (f : C(Icc (0:ℝ) T,ℝ)) :
    |asianPathAverage x r T hT.le σ f| ≤ |x| * Real.exp (|r-σ^2/2| *T+|σ| *‖f‖) := by
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0:ℝ)) (b := T) (C := |x| *Real.exp (|r-σ^2/2| *T+|σ| *‖f‖))
    (f := fun s => x*Real.exp ((r-σ^2/2)*s+σ*f (projIcc 0 T hT.le s)))
    (fun s hs => by
      have hs' : s ∈ Icc (0:ℝ) T := by
        rw [uIoc_of_le hT.le] at hs
        exact ⟨hs.1.le,hs.2⟩
      simpa only [Real.norm_eq_abs,stockPathValue,projIcc_of_mem hT.le hs'] using
        stock_path_upper_bound x σ r T f ⟨s,hs'⟩)
  rw [Real.norm_eq_abs,sub_zero,abs_of_pos hT] at hi
  unfold asianPathAverage
  rw [abs_div,abs_of_pos hT]
  exact (div_le_iff₀ hT).mpr hi

theorem asian_path_average_memLp {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : ℝ≥0 → Ω → ℝ)
    (hB : IsPreBrownianReal B P) (hm : ∀ t, Measurable (B t))
    (hc : ∀ w, Continuous (fun t => B t w)) (T : ℝ≥0) (hT : 0 < T)
    (X : Ω → C(Icc (0:ℝ) T,ℝ)) (hXm : Measurable X)
    (he : ∀ w (s : Icc (0:ℝ) T), X w s = B ⟨s.val,s.property.1⟩ w)
    (x r σ : ℝ) (p : ℝ≥0∞) (hp : p ≠ ⊤) :
    MemLp (fun w => asianPathAverage x r T (show 0 ≤ (T:ℝ) from hT.le) σ (X w)) p P := by
  have hi := (brownian_path_exponential_memLp P B hB hm hc T X hXm he |σ| p hp).const_mul
    (|x| *Real.exp (|r-σ^2/2| *T))
  apply hi.of_le (((asian_path_average_measurable x r T (show 0 ≤ (T:ℝ) from hT.le) σ).comp hXm).aestronglyMeasurable)
  apply ae_of_all
  intro w
  have hpos : 0 ≤ (|x| *Real.exp (|r-σ^2/2| *T))*Real.exp (|σ| *‖X w‖) := by positivity
  rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg hpos]
  rw [mul_assoc,←Real.exp_add]
  exact asian_path_average_bound x r T σ (show 0 < (T:ℝ) from hT) (X w)

end Asakura.Chapter12
