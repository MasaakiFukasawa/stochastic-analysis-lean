import Chapter6GirsanovBrownian
import Chapter3StoppedMartingaleFromLp
import Chapter6ExponentialSecondMoment

open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal
namespace Asakura.Chapter6
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter7
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

/-- The entropy identity is derived under the actual changed measure.
The martingale term has zero mean by its bounded quadratic variation. -/
theorem stopped_exponential_entropy_identity {Ω : Type*} {m : MeasurableSpace Ω}
    (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (F : HalfClosedTime → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t E,MeasurableSet[m] E → P E=0 → MeasurableSet[F t] E)
    (Z C : HalfClosedTime → Ω → ℝ) (hZ : LocalMProcessWitness P F Z)
    (hC : LocalCovarianceWitness P F Z Z C)
    (τ : Ω → HalfClosedTime) (hτ : ∀ t,MeasurableSet[F t] {w | τ w≤t})
    (R : ℝ) (hR : 0≤R) (hτR : ∀ w,τ w≤realTimeClamp R)
    (K : ℝ) (hK : ∀ᵐ w ∂P,|C (τ w) w|≤K)
    (hmean : (∫ w,Real.exp (Z (τ w) w-C (τ w) w/2) ∂P)=1)
    (hQ : Q=P.withDensity (fun w => ENNReal.ofReal (Real.exp (Z (τ w) w-C (τ w) w/2)))) :
    let D := fun w => Real.exp (Z (τ w) w-C (τ w) w/2)
    Integrable (fun w => D w*Real.log (D w)) P ∧
      (∫ w,D w*Real.log (D w) ∂P)=(∫ w,C (τ w) w ∂Q)/2 := by
  have hT : (0:EReal)<⊤ := by simp
  have hRt : (realTimeClamp R : HalfClosedTime)<⊤ := changed_time_finite R hR
  have hτt w := (hτR w).trans_lt hRt
  let U := fun t w => Z (min (τ w) t) w
  let A := fun t w => C (min (τ w) t) w
  let V := fun t w => U t w-A t w
  let D := fun w => Real.exp (Z (τ w) w-C (τ w) w/2)
  have hU := hZ.stopped P F hF hle τ hτ
  have hA := hC.stopped P F hF hle τ hτ
  have hV : LocalMProcessWitness Q F V := girsanov_maruyama_written P Q hT F hF hle hnull Z C hZ hC
    τ hτ hτt hmean hQ U A hU hA
  have hAv := covariance_adapted_variation P F hF hle hU hU hA
  have hAc := local_covariance_path_continuous P F U U A hU hU hA
  have hz := (open_process_stopped_regular F hF Z (hZ.adapted P F) (hZ.path P F) τ hτ hτt).1 ⊤
  have hc := (hC.stopped_regular P F hF hle hZ hZ τ hτ hτt).1 ⊤
  simp only [min_top_right] at hz hc
  have hDm : Measurable D := ((hz.mono (hle _) le_rfl).sub ((hc.mono (hle _) le_rfl).div_const 2)).exp
  have hAE := fun p => positive_real_density_ae_iff P Q D hDm (ae_of_all _ fun _ => Real.exp_pos _) hQ p
  have hnullQ := null_sets_transfer_to_equivalent_measure P Q F hnull hAE
  have hVA := drift_corrected_quadratic_variation P Q hT F hF hle hnull hnullQ hAE U A A hU hA hAv hAc hV
  have hAi : Integrable (fun w => C (τ w) w) Q := Integrable.of_bound (hc.mono (hle _) le_rfl).aestronglyMeasurable K
    ((hAE _).mp hK)
  have hAR : A (realTimeClamp R)=(fun w => C (τ w) w) := by funext w; dsimp [A]; rw [min_eq_left (hτR w)]
  have hmp := stopped_Mp_of_variation_moment Q hT F hF hle hnullQ V A hV hVA
    (fun _ => realTimeClamp R) (fun t => by by_cases h : realTimeClamp (T := ⊤) R≤t <;> simp [h])
    (fun _ => hRt) 2 (by norm_num) (by simpa only [div_self (by norm_num : (2:ℝ)≠0),Real.rpow_one,hAR] using hAi)
  have hVi : Integrable (V (realTimeClamp R)) Q := by simpa using (hmp.moment (realTimeClamp R)).integrable (by norm_num)
  have hV0 : (∫ w,V (realTimeClamp R) w ∂Q)=0 := by
    have he := hmp.martingale ⊥ (realTimeClamp R) bot_le
    simp only [min_self,min_bot_right] at he
    rw [←integral_condExp (hle ⊥),integral_congr_ae he,integral_congr_ae (hV.initial Q F)]
    simp
  have hlog : (fun w => Real.log (D w))=fun w => V (realTimeClamp R) w+C (τ w) w/2 := by
    funext w
    dsimp [D,V,U,A]
    rw [Real.log_exp,min_eq_left (hτR w)]
    ring
  have hli : Integrable (fun w => Real.log (D w)) Q := by rw [hlog]; exact hVi.add (hAi.div_const 2)
  let d := fun w => (D w).toNNReal
  have hd : Measurable d := hDm.real_toNNReal
  have hdreal w : (d w:ℝ)=D w := Real.coe_toNNReal _ (Real.exp_pos _).le
  have hQ' : Q=P.withDensity (fun w => (d w:ℝ≥0∞)) := hQ
  have hei : Integrable (fun w => D w*Real.log (D w)) P := by
    rw [hQ'] at hli
    have hh := (integrable_withDensity_iff_integrable_smul hd).mp hli
    change Integrable (fun w => (d w:ℝ)*Real.log (D w)) P at hh
    simpa only [hdreal] using hh
  refine ⟨hei,?_⟩
  have he : (∫ w,Real.log (D w) ∂Q)=∫ w,D w*Real.log (D w) ∂P := by
    rw [hQ',integral_withDensity_eq_integral_smul hd]
    change (∫ w,(d w:ℝ)*Real.log (D w) ∂P)=_
    simp only [hdreal]
  rw [←he,hlog,integral_add hVi (hAi.div_const 2),integral_div,hV0,zero_add]

end Asakura.Chapter6
