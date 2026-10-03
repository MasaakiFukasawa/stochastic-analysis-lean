import Chapter6NovikovWritten
import Chapter6NovikovEndpointLimit

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter6
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

/-- Critical Novikov, including the endpoint gamma = 1/2 mentioned in the
manuscript. Strict Novikov is applied to l Z, then Holder and l tending to
one establish the original exponential's mean one. -/
theorem novikov_endpoint_mean
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t ≤ m)
    (hnull : ∀ t N,MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (Z C : ClosedTime T → Ω → ℝ) (hZ : LocalMProcessWitness P F Z)
    (hC : LocalCovarianceWitness P F Z Z C)
    (τ : Ω → ClosedTime T) (hτ : ∀ t,MeasurableSet[F t] {w | τ w ≤ t})
    (hτt : ∀ w,τ w < ⊤)
    (hEi : Integrable (fun w => Real.exp (C (τ w) w/2)) P) :
    (∫ w,Real.exp (Z (τ w) w-C (τ w) w/2) ∂P) = 1 := by
  let U := fun w => Real.exp (Z (τ w) w-C (τ w) w/2)
  let V := fun w => Real.exp (C (τ w) w/2)
  have hE := stochastic_exponential_local P hT F hF hle hnull Z C hZ hC
  have hbound : ∀ᵐ w ∂P,∀ t,t < ⊤ → -(1:ℝ) ≤ Real.exp (Z t w-C t w/2)-1 :=
    ae_of_all _ (fun w t _ => by linarith [Real.exp_pos (Z t w-C t w/2)])
  obtain ⟨hUi,hUl⟩ := positive_shifted_local_mean_bound P F hF hle _ hE hbound τ hτ hτt
  simp only [sub_add_cancel] at hUi hUl
  have hn : ∀ᵐ w ∂P,0 ≤ C (τ w) w := by
    filter_upwards [local_quadratic_variation_monotone P F hF hle hnull Z C hZ hC,
      local_quadratic_variation_initial P F Z C hZ hC] with w hw hz
    simpa only [hz,Pi.zero_apply] using hw hT (hτt w) bot_le
  have hK : 1 ≤ ∫ w,V w ∂P := by
    have hh := integral_mono_ae (integrable_const (1:ℝ)) hEi
      (hn.mono fun w hw => Real.one_le_exp_iff.mpr (div_nonneg hw (by norm_num)))
    simpa using hh
  have hUn : 0 ≤ ∫ w,U w ∂P := integral_nonneg (fun w => (Real.exp_pos _).le)
  have hVn : 0 ≤ ∫ w,V w ∂P := le_trans zero_le_one hK
  have hZsm := (open_process_stopped_regular F hF Z (hZ.adapted P F) (hZ.path P F) τ hτ hτt).1 ⊤
  have hCsm := (hC.stopped_regular P F hF hle hZ hZ τ hτ hτt).1 ⊤
  simp only [min_top_right] at hZsm hCsm
  have hLower : 1 ≤ ∫ w,U w ∂P := by
    apply endpoint_holder_limit _ _ (lt_of_lt_of_le zero_lt_one hK)
    intro l hl hl1
    have hl2 : 0 < l^2 := sq_pos_of_pos hl
    have hl21 : l^2 < 1 := by nlinarith
    have hγ : (1:ℝ)/2 < 1/(2*l^2) := (lt_div_iff₀ (by positivity)).mpr (by nlinarith)
    have hscaledI : Integrable (fun w => Real.exp ((1/(2*l^2))*(l^2*C (τ w) w))) P := by
      convert hEi using 1
      funext w
      congr 1
      field_simp
    have hs := novikov_written P hT F hF hle hnull _ _ (hZ.smul P F l)
      (scaled_self_covariance P F Z C hC l) τ hτ hτt (1/(2*l^2)) hγ hscaledI
    have hli : Integrable (fun w => Real.exp (l*Z (τ w) w-l^2*C (τ w) w/2)) P := by
      simpa only [min_top_right] using hs.1 ⊤
    have hlm : (∫ w,Real.exp (l*Z (τ w) w-l^2*C (τ w) w/2) ∂P) = 1 := by
      simpa only [min_top_right] using hs.2.2.1
    have hh := novikov_endpoint_holder P (fun w => Z (τ w) w) (fun w => C (τ w) w)
      (hZsm.mono (hle ⊤) le_rfl) (hCsm.mono (hle ⊤) le_rfl) hn l hl hl1
    rw [← ofReal_integral_eq_lintegral_ofReal hli (ae_of_all _ (fun w => (Real.exp_pos _).le)),hlm,
      ← ofReal_integral_eq_lintegral_ofReal hUi (ae_of_all _ (fun w => (Real.exp_pos _).le)),
      ← ofReal_integral_eq_lintegral_ofReal hEi (ae_of_all _ (fun w => (Real.exp_pos _).le))] at hh
    have hfin : ENNReal.ofReal (∫ w,U w ∂P)^l * ENNReal.ofReal (∫ w,V w ∂P)^(1-l) ≠ ∞ :=
      ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg hl.le ENNReal.ofReal_ne_top)
        (ENNReal.rpow_ne_top_of_nonneg (sub_nonneg.mpr hl1.le) ENNReal.ofReal_ne_top)
    have hr := ENNReal.toReal_mono hfin hh
    simpa only [ENNReal.toReal_mul,← ENNReal.toReal_rpow,ENNReal.toReal_ofReal hUn,
      ENNReal.toReal_ofReal hVn,ENNReal.ofReal_one,ENNReal.toReal_one] using hr
  have hUpper : (∫ w,U w ∂P) ≤ 1 := by
    rw [← ofReal_integral_eq_lintegral_ofReal hUi (ae_of_all _ (fun w => (Real.exp_pos _).le))] at hUl
    change ENNReal.ofReal (∫ w,U w ∂P) ≤ 1 at hUl
    simpa only [ENNReal.toReal_ofReal hUn,ENNReal.toReal_one] using ENNReal.toReal_mono ENNReal.one_ne_top hUl
  exact le_antisymm hUpper hLower

theorem novikov_endpoint_written
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t ≤ m)
    (hnull : ∀ t N,MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (Z C : ClosedTime T → Ω → ℝ) (hZ : LocalMProcessWitness P F Z)
    (hC : LocalCovarianceWitness P F Z Z C)
    (τ : Ω → ClosedTime T) (hτ : ∀ t,MeasurableSet[F t] {w | τ w ≤ t})
    (hτt : ∀ w,τ w < ⊤)
    (hEi : Integrable (fun w => Real.exp (C (τ w) w/2)) P) :
    let M := fun t w => Real.exp (Z (min (τ w) t) w-C (min (τ w) t) w/2)
    (∀ t,Measurable[F t] (M t)) ∧ (∀ t,Integrable (M t) P) ∧
    (∀ w,Continuous (fun t => M t w)) ∧
    (∀ s t,s ≤ t → P[M t|F s] =ᵐ[P] M s) ∧
    (∀ t,M t =ᵐ[P] P[M ⊤|F t]) := by
  exact stochastic_exponential_closed_martingale P hT F hF hle hnull Z C hZ hC τ hτ hτt
    (novikov_endpoint_mean P hT F hF hle hnull Z C hZ hC τ hτ hτt hEi)

end Asakura.Chapter6
