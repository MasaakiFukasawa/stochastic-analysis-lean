import Chapter4TransitionLipschitz
import Chapter4PathMoment
import FullAuditConditionalLimit

open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal
namespace Asakura.Chapter4
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

lemma bounded_lipschitz_image_memLp
    {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → E) (hXm : Measurable X)
    (f : E → ℝ) (L : ℝ≥0) (hL : LipschitzWith L f) (B : ℝ) (hb : ∀ x,‖f x‖≤B) :
    MemLp (fun w => f (X w)) 2 P :=
  MemLp.of_bound (hL.continuous.measurable.comp hXm).aestronglyMeasurable B
    (Filter.Eventually.of_forall (fun w => hb (X w)))

lemma lipschitz_image_square_moment_bound
    {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P] (X Y : Ω → E)
    (hXm : Measurable X) (hYm : Measurable Y) (hXi : MemLp X 2 P) (hYi : MemLp Y 2 P)
    (f : E → ℝ) (L : ℝ≥0) (hL : LipschitzWith L f) (B : ℝ) (hb : ∀ x,‖f x‖≤B) :
    (∫ w,‖f (X w)-f (Y w)‖^2 ∂P)≤(L:ℝ)^2*(∫ w,‖X w-Y w‖^2 ∂P) := by
  have hfX := bounded_lipschitz_image_memLp P X hXm f L hL B hb
  have hfY := bounded_lipschitz_image_memLp P Y hYm f L hL B hb
  rw [← integral_const_mul]
  apply integral_mono ((hfX.sub hfY).integrable_norm_pow (by norm_num : (2:ℕ)≠0))
    (((hXi.sub hYi).integrable_norm_pow (by norm_num : (2:ℕ)≠0)).const_mul _)
  intro w
  have hh : ‖f (X w)-f (Y w)‖≤(L:ℝ)*‖X w-Y w‖ := by
    simpa only [dist_eq_norm] using hL.dist_le_mul (X w) (Y w)
  simpa only [mul_pow,Pi.sub_apply] using pow_le_pow_left₀ (norm_nonneg _) hh 2

lemma lipschitz_image_L2_tendsto
    {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → E) (Y : Ω → E)
    (hXm : ∀ n,Measurable (X n)) (hYm : Measurable Y) (hXi : ∀ n,MemLp (X n) 2 P) (hYi : MemLp Y 2 P)
    (hconv : Tendsto (fun n => ∫ w,‖X n w-Y w‖^2 ∂P) atTop (𝓝 0))
    (f : E → ℝ) (L : ℝ≥0) (hL : LipschitzWith L f) (B : ℝ) (hb : ∀ x,‖f x‖≤B) :
    Tendsto (fun n => eLpNorm (fun w => f (X n w)-f (Y w)) 2 P) atTop (𝓝 0) := by
  have hs : Tendsto (fun n => ∫ w,‖f (X n w)-f (Y w)‖^2 ∂P) atTop (𝓝 0) := by
    apply squeeze_zero (fun n => integral_nonneg (fun w => sq_nonneg _))
      (fun n => lipschitz_image_square_moment_bound P (X n) Y (hXm n) hYm (hXi n) hYi f L hL B hb)
    simpa only [mul_zero] using hconv.const_mul ((L:ℝ)^2)
  have he n := path_eLpNorm_eq_sqrt_moment P (fun w => f (X n w)-f (Y w))
    ((bounded_lipschitz_image_memLp P (X n) (hXm n) f L hL B hb).sub
      (bounded_lipschitz_image_memLp P Y hYm f L hL B hb))
  simp_rw [he]
  have hsq := Real.continuous_sqrt.continuousAt.tendsto.comp hs
  have hh := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hsq
  simpa only [Real.sqrt_zero,ENNReal.ofReal_zero,Function.comp_def] using hh

/-- The simple-initial-state identities pass to the L2 initial-state limit.
The proof uses conditional-expectation contraction, not an a.s. subsequence. -/
theorem markov_initial_L2_limit
    {Ω E : Type*} {m : MeasurableSpace Ω} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P] (G : MeasurableSpace Ω) (hG : G≤m)
    (η Y : Ω → E) (ηn Yn : ℕ → Ω → E)
    (hηm : Measurable[m] η) (hYm : Measurable[m] Y)
    (hηnm : ∀ n,Measurable[m] (ηn n)) (hYnm : ∀ n,Measurable[m] (Yn n))
    (hηi : MemLp η 2 P) (hYi : MemLp Y 2 P)
    (hηni : ∀ n,MemLp (ηn n) 2 P) (hYni : ∀ n,MemLp (Yn n) 2 P)
    (hηlim : Tendsto (fun n => ∫ w,‖ηn n w-η w‖^2 ∂P) atTop (𝓝 0))
    (hYlim : Tendsto (fun n => ∫ w,‖Yn n w-Y w‖^2 ∂P) atTop (𝓝 0))
    (f Pf : E → ℝ) (Lf LPf : ℝ≥0) (hf : LipschitzWith Lf f) (hPf : LipschitzWith LPf Pf)
    (B : ℝ) (hfb : ∀ x,‖f x‖≤B) (hPfb : ∀ x,‖Pf x‖≤B)
    (he : ∀ n,P[(fun w => f (Yn n w)) | G]=ᵐ[P] fun w => Pf (ηn n w)) :
    P[(fun w => f (Y w)) | G]=ᵐ[P] fun w => Pf (η w) := by
  letI : MeasurableSpace Ω := m
  have hiP n := bounded_lipschitz_image_memLp P (ηn n) (hηnm n) Pf LPf hPf B hPfb
  have hiF n := bounded_lipschitz_image_memLp P (Yn n) (hYnm n) f Lf hf B hfb
  have hip := bounded_lipschitz_image_memLp P η hηm Pf LPf hPf B hPfb
  have hif := bounded_lipschitz_image_memLp P Y hYm f Lf hf B hfb
  exact (Asakura.FullAudit.conditional_l2_limit_identity P hG
    (fun n w => Pf (ηn n w)) (fun n w => f (Yn n w)) (fun w => Pf (η w)) (fun w => f (Y w))
    hiP hiF hip hif (fun n => (he n).symm)
    (lipschitz_image_L2_tendsto P ηn η hηnm hηm hηni hηi hηlim Pf LPf hPf B hPfb)
    (lipschitz_image_L2_tendsto P Yn Y hYnm hYm hYni hYi hYlim f Lf hf B hfb)).symm

end Asakura.Chapter4
