import Chapter12BasketLevelNull
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

open MeasureTheory ProbabilityTheory Set
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

theorem exponential_basket_atomless_of_density {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (d : ℕ) (Y : Ω → Fin (d+1) → ℝ) (hY : Measurable Y)
    (hac : P.map Y ≪ volume) (c : Fin (d+1) → ℝ) (hc : 0<c 0) (K : ℝ) :
    P {w | (∑ i,c i*Real.exp (Y w i))=K}=0 := by
  have hz := hac (exponential_basket_level_null d c hc K)
  have hf : Measurable (fun y : Fin (d+1) → ℝ => ∑ i,c i*Real.exp (y i)) := by fun_prop
  have hs : MeasurableSet {y : Fin (d+1) → ℝ | (∑ i,c i*Real.exp (y i))=K} :=
    measurableSet_eq_fun hf measurable_const
  rw [Measure.map_apply hY hs] at hz
  exact hz

/-- An invertible linear transformation preserves absolute continuity of the
log-price vector, including all correlations between assets. -/
theorem linear_log_prices_absolutelyContinuous {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (d : ℕ) (Z : Ω → Fin (d+1) → ℝ) (hZ : Measurable Z)
    (hac : P.map Z ≪ volume)
    (L : (Fin (d+1) → ℝ) →ₗ[ℝ] (Fin (d+1) → ℝ)) (hL : LinearMap.det L≠0) :
    P.map (fun w => L (Z w)) ≪ volume := by
  have hq := MeasureTheory.Measure.LinearMap.quasiMeasurePreserving (volume : Measure (Fin (d+1) → ℝ)) L hL
  change P.map (L ∘ Z) ≪ volume
  rw [←Measure.map_map hq.measurable hZ]
  exact (hac.map hq.measurable).trans hq.absolutelyContinuous

end Asakura.Chapter12
