import Chapter4ConditionalCharacteristicLaw
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter4
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

/-- Successive conditional characteristic functions multiply, using C5
at each step and measurability of all earlier increments. -/
theorem conditional_characteristic_product
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (F : ℕ → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ n,F n≤m)
    (Q : ℕ → Ω → ℝ) (hQ : ∀ n,Measurable[F (n+1)] (Q n)) (K : ℕ → ℂ)
    (hchar : ∀ n,P[(fun w => Complex.exp ((Q n w:ℂ)*Complex.I)) | F n]=ᵐ[P] fun _ => K n) :
    ∀ n,P[(fun w => Complex.exp (((∑ k∈Finset.range n,Q k w : ℝ):ℂ)*Complex.I)) | F 0]=ᵐ[P]
      fun _ => ∏ k∈Finset.range n,K k := by
  letI : MeasurableSpace Ω := m
  let Z := fun n w => Complex.exp (((∑ k∈Finset.range n,Q k w : ℝ):ℂ)*Complex.I)
  let U := fun n w => Complex.exp ((Q n w:ℂ)*Complex.I)
  have hZm n : Measurable[F n] (Z n) := by
    letI : MeasurableSpace Ω := F n
    have hm : Measurable (fun w => ∑ k∈Finset.range n,Q k w) := Finset.measurable_sum _ (fun k hk =>
      (hQ k).mono (hF (Nat.succ_le_of_lt (Finset.mem_range.mp hk))) le_rfl)
    exact Complex.continuous_exp.measurable.comp ((Complex.continuous_ofReal.measurable.comp hm).mul_const _)
  have hUm n : Measurable[m] (U n) := by
    have hm := (hQ n).mono (hle (n+1)) le_rfl
    exact Complex.continuous_exp.measurable.comp ((Complex.continuous_ofReal.measurable.comp hm).mul_const _)
  have hZi n : Integrable (Z n) P := Integrable.of_bound ((hZm n).mono (hle n) le_rfl).aestronglyMeasurable 1
    (ae_of_all _ fun w => by simp [Z,Complex.norm_exp])
  have hUi n : Integrable (U n) P := Integrable.of_bound (hUm n).aestronglyMeasurable 1
    (ae_of_all _ fun w => by simp [U,Complex.norm_exp])
  have hsucc n : Z (n+1)=fun w => Z n w*U n w := by
    funext w
    simp only [Z,U,Finset.sum_range_succ,Complex.ofReal_add,add_mul,Complex.exp_add]
  have hstep n : P[Z (n+1) | F n]=ᵐ[P] fun w => K n*Z n w := by
    rw [hsucc]
    have hh := condExp_bilin_of_stronglyMeasurable_left (ContinuousLinearMap.mul ℝ ℂ)
      (hZm n).stronglyMeasurable (by change Integrable (fun w => Z n w*U n w) P; rw [← hsucc]; exact hZi (n+1)) (hUi n)
    filter_upwards [hh,hchar n] with w hw hc
    change P[(fun w => Z n w*U n w) | F n] w=_
    change P[(fun w => Z n w*U n w) | F n] w=Z n w*P[U n | F n] w at hw
    rw [hw,hc,mul_comm]
  intro n
  change P[Z n | F 0]=ᵐ[P] _
  induction n with
  | zero =>
    simp only [Z,Finset.sum_range_zero,Complex.ofReal_zero,zero_mul,Complex.exp_zero,Finset.prod_range_zero,
      condExp_const (hle 0)]
    exact ae_of_all _ fun _ => rfl
  | succ n ih =>
    have ht := condExp_condExp_of_le (μ:=P) (f:=Z (n+1)) (hF (Nat.zero_le n)) (hle n)
    have he := condExp_congr_ae (m:=F 0) (hstep n)
    have hc := condExp_smul (μ:=P) (K n) (Z n) (F 0)
    filter_upwards [ht,he,hc,ih] with w ht he hc ih
    change P[(fun w => K n*Z n w) | F 0] w=K n*P[Z n | F 0] w at hc
    rw [← ht,he,hc,ih,Finset.prod_range_succ,mul_comm]

end Asakura.Chapter4
