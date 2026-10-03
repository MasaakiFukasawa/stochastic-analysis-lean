import MVNScaling

open MeasureTheory Set
namespace Asakura

lemma integral_shift_Ioi (f : ℝ → ℝ) (s : ℝ) :
    (∫ r in Ioi 0, f (s+r)) = ∫ u in Ioi s, f u := by
  rw [← integral_indicator measurableSet_Ioi,← integral_indicator measurableSet_Ioi]
  rw [← integral_add_left_eq_self s (f := (Ioi s).indicator f)]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro r
  simp only [indicator_apply,mem_Ioi]
  split_ifs <;> simp_all <;> linarith

noncomputable def mvnIncrementVariance (H s t : ℝ) : ℝ :=
    (∫ r in Ioc 0 s, ((t-r)^(H-1/2)-(s-r)^(H-1/2))^2) +
    (∫ r in Ioc s t, ((t-r)^(H-1/2))^2) +
    (∫ r in Ioi 0, ((t+r)^(H-1/2)-(s+r)^(H-1/2))^2)

lemma mvn_increment_variance_stationary (H s t : ℝ) (hH0 : 0 < H) (hH1 : H < 1)
    (hs : 0 ≤ s) (hst : s ≤ t) :
    mvnIncrementVariance H s t =
      (∫ r in Ioc 0 (t-s), (((t-s)-r)^(H-1/2))^2) + mvnPastVariance H (t-s) := by
  let f : ℝ → ℝ := fun r => (mvnPastKernel (H-1/2) (t-s) r)^2
  have h₁ : (∫ r in Ioc 0 s, ((t-r)^(H-1/2)-(s-r)^(H-1/2))^2) =
      ∫ r in (0:ℝ)..s, f r := by
    rw [← intervalIntegral.integral_of_le hs]
    have he : (fun r => ((t-r)^(H-1/2)-(s-r)^(H-1/2))^2) = fun r => f (s-r) := by
      funext r
      dsimp [f,mvnPastKernel]
      rw [show t-s+(s-r) = t-r by ring]
    rw [he,intervalIntegral.integral_comp_sub_left f s]
    simp
  have h₂ : (∫ r in Ioc s t, ((t-r)^(H-1/2))^2) =
      ∫ r in Ioc 0 (t-s), (((t-s)-r)^(H-1/2))^2 := by
    rw [← intervalIntegral.integral_of_le hst,
      ← intervalIntegral.integral_of_le (sub_nonneg.mpr hst)]
    rw [intervalIntegral.integral_comp_sub_left (fun x : ℝ => (x^(H-1/2))^2) t,
      intervalIntegral.integral_comp_sub_left (fun x : ℝ => (x^(H-1/2))^2) (t-s)]
    simp
  have h₃ : (∫ r in Ioi 0, ((t+r)^(H-1/2)-(s+r)^(H-1/2))^2) = ∫ r in Ioi s, f r := by
    rw [← integral_shift_Ioi f s]
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro r
    dsimp [f,mvnPastKernel]
    rw [show t-s+(s+r) = t+r by ring]
  have hf : IntegrableOn f (Ioi 0) :=
    mvn_past_square_integrable (H-1/2) (t-s) (by linarith) (by linarith) (sub_nonneg.mpr hst)
  have hjoin := intervalIntegral.integral_interval_add_Ioi hf
    (hf.mono_set (Ioi_subset_Ioi hs))
  unfold mvnIncrementVariance
  rw [h₁,h₂,h₃]
  unfold mvnPastVariance
  calc
    _ = (∫ r in Ioc 0 (t-s), (((t-s)-r)^(H-1/2))^2) +
        ((∫ r in (0:ℝ)..s, f r)+(∫ r in Ioi s, f r)) := by ring
    _ = _ := by rw [hjoin]

lemma mvn_normalized_increment_variance (H s t : ℝ) (hH0 : 0 < H) (hH1 : H < 1)
    (hs : 0 ≤ s) (hst : s ≤ t) :
    mvnNormalization H ^ 2 * mvnIncrementVariance H s t = (t-s)^(2*H) := by
  rw [mvn_increment_variance_stationary H s t hH0 hH1 hs hst]
  exact mvn_normalized_variance H (t-s) hH0 (sub_nonneg.mpr hst)
end Asakura
