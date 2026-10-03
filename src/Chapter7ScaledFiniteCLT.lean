import Chapter7FiniteTimeCLT
import Chapter6NovikovStoppedMoment

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal
namespace Asakura.Chapter7
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter4
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

lemma probability_const_mul {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℕ → Ω → ℝ) (Y : Ω → ℝ)
    (h : TendstoInMeasure P X atTop Y) (b : ℝ) :
    TendstoInMeasure P (fun n w => b*X n w) atTop (fun w => b*Y w) := by
  apply tendstoInMeasure_iff_dist.mpr
  intro ε hε
  by_cases hb : b=0
  · simp [hb,hε.not_ge]
  have hab : 0 < |b| := abs_pos.mpr hb
  have hh := tendstoInMeasure_iff_dist.mp h (ε/|b|) (div_pos hε hab)
  convert hh using 1
  funext n
  congr 1
  ext w
  simp only [mem_setOf_eq,Real.dist_eq,← mul_sub,abs_mul]
  rw [div_le_iff₀ hab, mul_comm |b|]

/-- The normalization actually used in the estimator proof. Only the bracket
convergence up to the observation horizon is needed. -/
theorem scaled_finite_time_clt
    {Ω Γ : Type*} [m : MeasurableSpace Ω] [q : MeasurableSpace Γ]
    (P : Measure Ω) (Q : Measure Γ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (F : HalfClosedTime → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t ≤ m)
    (M C : ℕ → HalfClosedTime → Ω → ℝ)
    (hM : ∀ n,LocalMProcessWitness P F (M n))
    (hC : ∀ n,LocalCovarianceWitness P F (M n) (M n) (C n))
    (a : ℝ≥0) (c : ℝ) (hc : 0 < c)
    (hp : ∀ t : ℝ≥0,t ≤ a → TendstoInMeasure P (fun n => C n (realTimeClamp t)) atTop (fun _ => c*(t:ℝ)))
    (B : BrownianSystem Q 1) :
    ∃ B0 : BrownianSystem (P.prod Q) 1,
      TendstoInDistribution (fun n => M n (realTimeClamp a)) atTop
        (fun z => Real.sqrt c*B0.W 0 (realTimeClamp a) z) (fun _ => P) (P.prod Q) := by
  let b := (Real.sqrt c)⁻¹
  have hs : Real.sqrt c ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hc)
  have hbc : b^2*c=1 := by
    dsimp [b]
    rw [inv_pow,Real.sq_sqrt hc.le]
    exact inv_mul_cancel₀ hc.ne'
  have hm n := (hM n).smul P F b
  have hcov n := Asakura.Chapter6.scaled_self_covariance P F (M n) (C n) (hC n) b
  have hp' (t : ℝ≥0) (ht : t ≤ a) :
      TendstoInMeasure P (fun n w => b^2*C n (realTimeClamp t) w) atTop (fun _ => (t:ℝ)) := by
    have hx := probability_const_mul P (fun n w => C n (realTimeClamp t) w) (fun _ => c*(t:ℝ)) (hp t ht) (b^2)
    exact hx.congr_right (ae_of_all P (fun w => by rw [← mul_assoc,hbc,one_mul]))
  obtain ⟨B0,hlim⟩ := finite_time_clt_of_half_line P Q F hF hle
    (fun n t w => b*M n t w) (fun n t w => b^2*C n t w) hm hcov a hp' B
  let e : Icc (0:ℝ≥0) a := ⟨a,⟨a.property,le_rfl⟩⟩
  have hcont : Continuous (fun f : C(Icc (0:ℝ≥0) a,ℝ) => Real.sqrt c*f e) :=
    continuous_const.mul (continuous_eval_const e)
  refine ⟨B0,?_⟩
  have he := hlim.continuous_comp hcont
  convert he using 1
  · funext n w
    change M n (realTimeClamp a) w = Real.sqrt c*(b*M n (realTimeClamp a) w)
    dsimp [b]; field_simp
  · rfl

end Asakura.Chapter7
