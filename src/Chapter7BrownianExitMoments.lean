import Chapter7BrownianExitBounds

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter7
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter4
set_option maxHeartbeats 2600000

/-- Both moment identities and the uniform expected-exit-time bound are
derived from the actual stopped Brownian process. -/
theorem brownian_exit_moments
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (B : BrownianSystem P 1) (x R c : ℝ) (hc : 0 ≤ c)
    (τ : Ω → HalfClosedTime)
    (hτ : ∀ t,MeasurableSet[B.F t] {w | τ w ≤ t})
    (hτc : ∀ w,τ w ≤ realTimeClamp c)
    (hb : ∀ᵐ w ∂P,∀ t,x+B.W 0 (min (τ w) t) w ∈ Icc 0 R) :
    Integrable (fun w => x+B.W 0 (τ w) w) P ∧
    Integrable (fun w => B.C 0 0 (τ w) w) P ∧
    (∫ w,x+B.W 0 (τ w) w ∂P) = x ∧
    (∫ w,B.C 0 0 (τ w) w ∂P) ≤ R^2 := by
  have hfinite w : τ w < ⊤ := lt_of_le_of_lt (hτc w) (changed_time_finite c hc)
  obtain ⟨hw,hd⟩ := brownian_exit_path_bounds P B x R c hc τ hτc hb
  obtain ⟨hm,_⟩ := (B.martingale 0).stopped_regular P B.F B.mono B.le τ hτ hfinite
  have hwm : Measurable (fun w => B.W 0 (τ w) w) := by
    simpa only [min_top_right] using (hm ⊤).mono (B.le ⊤) le_rfl
  have hwi : Integrable (fun w => B.W 0 (τ w) w) P := by
    apply (integrable_const (|R|+|x|)).mono' hwm.aestronglyMeasurable
    simpa only [min_top_right,Real.norm_eq_abs] using hw.mono (fun w h => h ⊤)
  have hxi := (integrable_const x).add hwi
  have hcpoint w : 0 ≤ B.C 0 0 (τ w) w ∧ B.C 0 0 (τ w) w ≤ c := by
    rw [brownian_clock_at_finite B _ (hfinite w)]
    refine ⟨(halfTimeReal (τ w)).property,?_⟩
    obtain ⟨r,hr,_,he⟩ := finite_closed_time_real (τ w) (hfinite w)
    rw [← he,changed_time_real r hr]
    have h := hτc w
    rw [← he] at h
    have h' := (changed_time_le_iff r hr _ (changed_time_finite c hc)).mp h
    simpa only [changed_time_real c hc] using h'
  obtain ⟨hcm,_⟩ := (B.cov 0 0).stopped_regular P B.F B.mono B.le (B.martingale 0) (B.martingale 0) τ hτ hfinite
  have hci : Integrable (fun w => B.C 0 0 (τ w) w) P := by
    apply (integrable_const c).mono'
    · simpa only [min_top_right] using ((hcm ⊤).mono (B.le ⊤) le_rfl).aestronglyMeasurable
    · exact ae_of_all _ fun w => by simpa only [Real.norm_eq_abs,abs_of_nonneg (hcpoint w).1] using (hcpoint w).2
  have hwsq : Integrable (fun w => B.W 0 (τ w) w * B.W 0 (τ w) w) P := by
    apply (integrable_const ((|R|+|x|)^2)).mono' (hwm.mul hwm).aestronglyMeasurable
    filter_upwards [hw] with w h
    have h' := h ⊤
    simp only [min_top_right] at h'
    change |B.W 0 (τ w) w * B.W 0 (τ w) w| ≤ (|R|+|x|)^2
    rw [abs_mul]
    nlinarith [abs_nonneg (B.W 0 (τ w) w),abs_nonneg R,abs_nonneg x]
  have hz := brownian_bounded_stop_mean P B τ hτ hfinite _ hw
  have hq := brownian_bounded_stop_square P B τ hτ hfinite _ hd
  rw [integral_sub hwsq hci] at hq
  have hxsq : Integrable (fun w => (x+B.W 0 (τ w) w)^2) P := by
    convert ((integrable_const (x^2)).add (hwi.const_mul (2*x))).add hwsq using 1
    ext w
    simp only [Pi.add_apply]
    ring
  have hid : (∫ w,(x+B.W 0 (τ w) w)^2 ∂P) = x^2+∫ w,B.C 0 0 (τ w) w ∂P := by
    have he : (fun w => (x+B.W 0 (τ w) w)^2) =
        fun w => x^2+(2*x)*B.W 0 (τ w) w+B.W 0 (τ w) w*B.W 0 (τ w) w := by ext w; ring
    have hfirst : Integrable (fun w => x^2+(2*x)*B.W 0 (τ w) w) P := (integrable_const _).add (hwi.const_mul _)
    rw [he,integral_add hfirst hwsq,
      integral_add (integrable_const _) (hwi.const_mul _),integral_const_mul,hz]
    simp only [integral_const,Measure.real,measure_univ,ENNReal.toReal_one,one_smul,mul_zero,add_zero]
    linarith
  refine ⟨hxi,hci,?_,?_⟩
  · rw [integral_add (integrable_const _) hwi,hz]
    simp
  · have hle := integral_mono_ae hxsq (integrable_const (R^2)) (hb.mono fun w h => by
      have h' := h ⊤
      simp only [min_top_right,mem_Icc] at h'
      nlinarith [h'.1,h'.2])
    simp only [integral_const,Measure.real,measure_univ,ENNReal.toReal_one,one_smul] at hle
    rw [hid] at hle
    nlinarith [sq_nonneg x]

end Asakura.Chapter7
