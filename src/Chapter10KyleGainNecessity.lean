import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

open MeasureTheory Set Filter
namespace Asakura.Chapter10

/-- The quadratic-variation identity forces equality of the continuous gain
at every time, including the initial time. -/
theorem continuous_gain_of_zero_energy (k : ℝ → ℝ) (T l σ : ℝ)
    (hT : 0<T) (hσ : σ≠0) (hk : ContinuousOn k (Icc 0 T))
    (he : (∫ s in 0..T,(k s-l)^2*σ^2)=0) :
    ∀ t∈Icc 0 T,k t=l := by
  have hc : ContinuousOn (fun s => (k s-l)^2*σ^2) (Icc 0 T) :=
    ((hk.sub continuousOn_const).pow 2).mul continuousOn_const
  have hz := (intervalIntegral.integral_eq_zero_iff_of_le_of_nonneg_ae hT.le
    (ae_of_all _ fun s => mul_nonneg (sq_nonneg _) (sq_nonneg _))
    (hc.intervalIntegrable_of_Icc hT.le)).mp he
  rw [Measure.restrict_congr_set Ioc_ae_eq_Icc] at hz
  have hp := Measure.eqOn_Icc_of_ae_eq volume hT.ne hz hc continuousOn_const
  intro t ht
  have hh := hp ht
  change (k t-l)^2*σ^2=0 at hh
  exact sub_eq_zero.mp (sq_eq_zero_iff.mp ((mul_eq_zero.mp hh).resolve_right (pow_ne_zero 2 hσ)))

end Asakura.Chapter10
