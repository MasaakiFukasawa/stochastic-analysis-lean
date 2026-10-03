import MVNKernelLp
import WienerIntegralInterface

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal Topology
namespace Asakura

noncomputable def mvnFutureLp (H : ℝ) (hH : 0 < H) (t : ℝ≥0) : Lp ℝ 2 (volume : Measure ℝ) :=
  (mvn_future_function_memLp H t hH t.coe_nonneg).toLp (mvnFutureFunction H t)
noncomputable def mvnPastLp (H : ℝ) (hH0 : 0 < H) (hH1 : H < 1) (t : ℝ≥0) : Lp ℝ 2 (volume : Measure ℝ) :=
  (mvn_past_function_memLp H t hH0 hH1 t.coe_nonneg).toLp (mvnPastFunction H t)

lemma mvnFutureLp_supported (H : ℝ) (hH : 0 < H) (t : ℝ≥0) :
    PositiveSupported (mvnFutureLp H hH t) := by
  filter_upwards [(mvn_future_function_memLp H t hH t.coe_nonneg).coeFn_toLp] with r hr
  intro hr0
  have hn : r ∉ Set.Ioc 0 (t:ℝ) := fun h => (not_lt_of_ge hr0) h.1
  exact hr.trans (by simp [mvnFutureFunction,hn])

lemma mvnPastLp_supported (H : ℝ) (hH0 : 0 < H) (hH1 : H < 1) (t : ℝ≥0) :
    PositiveSupported (mvnPastLp H hH0 hH1 t) := by
  filter_upwards [(mvn_past_function_memLp H t hH0 hH1 t.coe_nonneg).coeFn_toLp] with r hr
  intro hr0
  have hn : r ∉ Set.Ioi (0:ℝ) := not_lt_of_ge hr0
  exact hr.trans (by simp [mvnPastFunction,hn])

lemma mvnFutureLp_zero (H : ℝ) (hH : 0 < H) : mvnFutureLp H hH 0 = 0 := by
  apply Lp.ext
  filter_upwards [(mvn_future_function_memLp H 0 hH (by norm_num)).coeFn_toLp,Lp.coeFn_zero ℝ 2 volume] with r h₁ h₂
  simpa [mvnFutureLp,mvnFutureFunction] using h₁

lemma mvnPastLp_zero (H : ℝ) (hH0 : 0 < H) (hH1 : H < 1) : mvnPastLp H hH0 hH1 0 = 0 := by
  apply Lp.ext
  filter_upwards [(mvn_past_function_memLp H 0 hH0 hH1 (by norm_num)).coeFn_toLp,Lp.coeFn_zero ℝ 2 volume] with r h₁ h₂
  have he : mvnPastFunction H 0 = fun _ => 0 := by
    funext x
    by_cases hx : x ∈ Ioi (0:ℝ) <;> simp [mvnPastFunction,mvnPastKernel,hx]
  rw [h₂]
  change (mvnPastLp H hH0 hH1 0 : ℝ → ℝ) r = 0
  exact h₁.trans (congrFun he r)

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

noncomputable def mvnProcessLp (I : IndependentWienerIntegrals P) (H : ℝ) (hH0 : 0 < H)
    (hH1 : H < 1) (t : ℝ≥0) : Lp ℝ 2 P :=
  mvnNormalization H • (I.first (mvnFutureLp H hH0 t) + I.second (mvnPastLp H hH0 hH1 t))

lemma mvn_process_zero (I : IndependentWienerIntegrals P) (H : ℝ) (hH0 : 0 < H) (hH1 : H < 1) :
    mvnProcessLp I H hH0 hH1 0 = 0 := by
  simp [mvnProcessLp,mvnFutureLp_zero,mvnPastLp_zero]

lemma mvn_process_mean (I : IndependentWienerIntegrals P) (H : ℝ) (hH0 : 0 < H)
    (hH1 : H < 1) (t : ℝ≥0) : (∫ ω, mvnProcessLp I H hH0 hH1 t ω ∂P) = 0 := by
  rw [L2_mean_inner]
  unfold mvnProcessLp
  rw [inner_smul_right,inner_add_right,← L2_mean_inner,← L2_mean_inner,
    I.mean_first,I.mean_second]
  simp

lemma mvn_process_increment_inner (I : IndependentWienerIntegrals P) (H : ℝ) (hH0 : 0 < H)
    (hH1 : H < 1) (s t : ℝ≥0) (hst : s ≤ t) :
    inner ℝ (mvnProcessLp I H hH0 hH1 t-mvnProcessLp I H hH0 hH1 s)
      (mvnProcessLp I H hH0 hH1 t-mvnProcessLp I H hH0 hH1 s) = ((t:ℝ)-(s:ℝ))^(2*H) := by
  have he : mvnProcessLp I H hH0 hH1 t-mvnProcessLp I H hH0 hH1 s =
      mvnNormalization H • (I.first (mvnFutureLp H hH0 t-mvnFutureLp H hH0 s) +
        I.second (mvnPastLp H hH0 hH1 t-mvnPastLp H hH0 hH1 s)) := by
    simp only [mvnProcessLp,map_sub]
    module
  have hF := positiveSupported_sub (mvnFutureLp_supported H hH0 t) (mvnFutureLp_supported H hH0 s)
  have hP := positiveSupported_sub (mvnPastLp_supported H hH0 hH1 t) (mvnPastLp_supported H hH0 hH1 s)
  rw [he,real_inner_smul_left,inner_smul_right,I.inner_sum _ _ _ _ hF hP hF hP]
  rw [show mvnNormalization H * (mvnNormalization H *
    (inner ℝ (mvnFutureLp H hH0 t-mvnFutureLp H hH0 s) (mvnFutureLp H hH0 t-mvnFutureLp H hH0 s)+
     inner ℝ (mvnPastLp H hH0 hH1 t-mvnPastLp H hH0 hH1 s) (mvnPastLp H hH0 hH1 t-mvnPastLp H hH0 hH1 s))) =
    mvnNormalization H^2 * (inner ℝ (mvnFutureLp H hH0 t-mvnFutureLp H hH0 s) (mvnFutureLp H hH0 t-mvnFutureLp H hH0 s)+
     inner ℝ (mvnPastLp H hH0 hH1 t-mvnPastLp H hH0 hH1 s) (mvnPastLp H hH0 hH1 t-mvnPastLp H hH0 hH1 s)) by ring]
  unfold mvnFutureLp mvnPastLp
  rw [L2_difference_square_integral,L2_difference_square_integral]
  exact mvn_kernel_increment_variance H s t hH0 hH1 s.coe_nonneg (by exact_mod_cast hst)

lemma mvn_process_self_inner (I : IndependentWienerIntegrals P) (H : ℝ) (hH0 : 0 < H)
    (hH1 : H < 1) (t : ℝ≥0) :
    inner ℝ (mvnProcessLp I H hH0 hH1 t) (mvnProcessLp I H hH0 hH1 t) = (t:ℝ)^(2*H) := by
  simpa [mvn_process_zero] using mvn_process_increment_inner I H hH0 hH1 0 t (by positivity)

lemma mvn_process_covariance (I : IndependentWienerIntegrals P) (H : ℝ) (hH0 : 0 < H)
    (hH1 : H < 1) (s t : ℝ≥0) :
    (∫ ω, mvnProcessLp I H hH0 hH1 s ω * mvnProcessLp I H hH0 hH1 t ω ∂P) =
      ((s:ℝ)^(2*H)+(t:ℝ)^(2*H)-|(s:ℝ)-(t:ℝ)|^(2*H))/2 := by
  have he : inner ℝ (mvnProcessLp I H hH0 hH1 s) (mvnProcessLp I H hH0 hH1 t) =
      (∫ ω, mvnProcessLp I H hH0 hH1 s ω * mvnProcessLp I H hH0 hH1 t ω ∂P) := by
    rw [L2.inner_def]
    simp [mul_comm]
  rw [← he]
  have hs := mvn_process_self_inner I H hH0 hH1 s
  have ht := mvn_process_self_inner I H hH0 hH1 t
  have hcomm : inner ℝ (mvnProcessLp I H hH0 hH1 t) (mvnProcessLp I H hH0 hH1 s) =
      inner ℝ (mvnProcessLp I H hH0 hH1 s) (mvnProcessLp I H hH0 hH1 t) := real_inner_comm _ _
  rcases le_total s t with hst | hts
  · have hh := mvn_process_increment_inner I H hH0 hH1 s t hst
    rw [inner_sub_sub_self,hs,ht] at hh
    rw [abs_of_nonpos (sub_nonpos.mpr (NNReal.coe_le_coe.mpr hst)),neg_sub]
    linarith [hcomm]
  · have hh := mvn_process_increment_inner I H hH0 hH1 t s hts
    rw [inner_sub_sub_self,hs,ht] at hh
    rw [abs_of_nonneg (sub_nonneg.mpr (NNReal.coe_le_coe.mpr hts))]
    linarith [hcomm]
end Asakura
