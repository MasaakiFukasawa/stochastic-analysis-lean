import Chapter11MixedApproximation
import Chapter2FiniteDensity

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter11
open Asakura.FullAudit Asakura.Chapter2Complete
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false

/-- One actual adapted step sequence simultaneously approximates an
 L2 martingale integrand and an L1 variation integrand. The control clock
 itself need not integrate H squared. -/
theorem finite_mixed_step_density
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (b : ℝ) (hb : 0 < b) [Fact (0 ≤ b)] (A : Ω → ℝ → ℝ)
    (hA : ∀ ω, MonotoneOn (A ω) (Icc 0 b)) (hc : ∀ ω, ContinuousOn (A ω) (Icc 0 b))
    (hm : ∀ t, Measurable (fun ω => A ω t))
    (F : Icc (0:ℝ) b → MeasurableSpace Ω) (hF : Monotone F)
    (hle : ∀ t, F t ≤ ‹MeasurableSpace Ω›)
    (had : ∀ t : Icc (0:ℝ) b, Measurable[F t] (fun ω => A ω t.val))
    (hnull : ∀ t N, MeasurableSet N → P N = 0 → MeasurableSet[F t] N)
    (H : Ω × Icc (0:ℝ) b → ℝ)
    (hH : @Measurable _ _ (progressiveSpace F) inferInstance H)
    (α β : Ω → Measure ℝ) [∀ w,IsFiniteMeasure (α w)] [∀ w,IsFiniteMeasure (β w)]
    (hα : ∀ w,α w≤(intervalStieltjes 0 b hb.le (A w) (hA w) (fun r hr => (hc w r hr).mono inter_subset_left)).measure)
    (hβ : ∀ w,β w≤(intervalStieltjes 0 b hb.le (A w) (hA w) (fun r hr => (hc w r hr).mono inter_subset_left)).measure)
    (hαm : ∀ f : Ω × ℝ → ℝ,Measurable f → Measurable (fun w => ∫ r,f (w,r) ∂α w))
    (hβm : ∀ f : Ω × ℝ → ℝ,Measurable f → Measurable (fun w => ∫ r,f (w,r) ∂β w))
    (hiα : ∀ᵐ w ∂P,Integrable (fun r => (H (w,projIcc 0 b hb.le r))^2) (α w))
    (hiβ : ∀ᵐ w ∂P,Integrable (fun r => |H (w,projIcc 0 b hb.le r)|) (β w)) :
    ∃ (N : ℕ → ℕ) (u : ℕ → ℕ → Icc (0:ℝ) b) (V : ℕ → ℕ → Ω → ℝ),
      (∀ n,StrictMonoOn (u n) (Iic (N n))) ∧
      (∀ n j,j<N n → Measurable[F (u n j)] (V n j) ∧ MemLp (V n j) ∞ P) ∧
      let J := fun n (z : Ω × ℝ) => ∑ j∈Finset.range (N n),(Ico (u n j) (u n (j+1))).indicator (fun _ => V n j z.1) (projIcc 0 b hb.le z.2)
      (∀ n,Measurable (J n)) ∧
      (∀ n,∀ᵐ w ∂P,Integrable (fun r => (J n (w,r)-H (w,projIcc 0 b hb.le r))^2) (α w)) ∧
      (∀ n,∀ᵐ w ∂P,Integrable (fun r => |J n (w,r)-H (w,projIcc 0 b hb.le r)|) (β w)) ∧
      (∀ ε>0,Tendsto (fun n => P {w | ε≤∫ r,(J n (w,r)-H (w,projIcc 0 b hb.le r))^2 ∂α w}) atTop (𝓝 0)) ∧
      (∀ ε>0,Tendsto (fun n => P {w | ε≤∫ r,|J n (w,r)-H (w,projIcc 0 b hb.le r)| ∂β w}) atTop (𝓝 0)) := by
  classical
  obtain ⟨N,u,V,hmono,hVm,hVbound,happrox⟩ :=
    finite_localized_clipped_step_approximation P b hb A hA hc hm F hF hle had hnull H hH 2 (by norm_num)
  let μ := fun ω => (intervalStieltjes 0 b hb.le (A ω) (hA ω)
    (fun r hr => (hc ω r hr).mono inter_subset_left)).measure
  letI (ω : Ω) : IsFiniteMeasure (μ ω) := intervalStieltjes_finite 0 b hb.le (A ω) (hA ω) _
  let q : Ω × ℝ → Ω × Icc (0:ℝ) b := fun z => (z.1,projIcc 0 b hb.le z.2)
  have hq : Measurable q := measurable_fst.prodMk (continuous_projIcc.measurable.comp measurable_snd)
  let H0 := H ∘ q
  have hH0 : Measurable H0 := (hH.mono (progressive_space_le_product F hle) le_rfl).comp hq
  let J := fun n (z : Ω × ℝ) => ∑ j ∈ Finset.range (N n),
    (Ico (u n j) (u n (j+1))).indicator (fun _ => V n j z.1) (projIcc 0 b hb.le z.2)
  have hJ n : Measurable (J n) := by
    have hj : @Measurable _ _ (progressiveSpace F) inferInstance
        (fun z : Ω × Icc (0:ℝ) b => ∑ j ∈ Finset.range (N n),
          (Ico (u n j) (u n (j+1))).indicator (fun _ => V n j z.1) z.2) := by
      apply Finset.measurable_sum
      intro j hj
      exact progressive_elementary_measurable 0 b F hF _ _ _ ((hVm n j (Finset.mem_range.1 hj)).1)
    exact (hj.mono (progressive_space_le_product F hle) le_rfl).comp hq
  have hαmass : Measurable (fun w => (α w).real univ) := by
    simpa only [integral_const,smul_eq_mul,mul_one] using hαm (fun _ => 1) measurable_const
  have hβmass : Measurable (fun w => (β w).real univ) := by
    simpa only [integral_const,smul_eq_mul,mul_one] using hβm (fun _ => 1) measurable_const
  have hJb n z : |J n z|≤(n:ℝ)+1 := hVbound n (q z)
  have happ : ∀ ε>0,Tendsto (fun n => P {w | ε≤∫ r,(J n (w,r)-max (-((n:ℝ)+1)) (min ((n:ℝ)+1) (H0 (w,r))))^2 ∂μ w}) atTop (𝓝 0) := by
    simpa only [Real.rpow_two,sq_abs,J,H0,q,Function.comp_def,μ] using happrox
  have ha := (mixed_clipped_approximation P μ α hα hαmass H0 hH0 J hJ hJb happ).1
  have hb' := (mixed_clipped_approximation P μ β hβ hβmass H0 hH0 J hJ hJb happ).2
  have hαfull := clipped_approximation_complete P α H0 hH0 J hJ hJb 2 (by norm_num)
    (by simpa only [Real.rpow_two,sq_abs,J,H0,q,Function.comp_def,μ] using hiα)
    (fun n => hαm _ ((measurable_const.max (measurable_const.min hH0)).sub hH0 |>.norm.pow_const 2))
    (by simpa only [Real.rpow_two,sq_abs,J,H0,q,Function.comp_def,μ] using ha)
  have hβfull := clipped_approximation_complete P β H0 hH0 J hJ hJb 1 (by norm_num)
    (by simpa only [Real.rpow_one,J,H0,q,Function.comp_def,μ] using hiβ)
    (fun n => hβm _ ((measurable_const.max (measurable_const.min hH0)).sub hH0 |>.norm.pow_const 1))
    (by simpa only [Real.rpow_one,J,H0,q,Function.comp_def,μ] using hb')
  refine ⟨N,u,V,hmono,hVm,hJ,?_,?_,?_,?_⟩
  · simpa only [Real.rpow_two,sq_abs,J,H0,q,Function.comp_def,μ] using hαfull.1
  · simpa only [Real.rpow_one,J,H0,q,Function.comp_def,μ] using hβfull.1
  · simpa only [Real.rpow_two,sq_abs,J,H0,q,Function.comp_def,μ] using hαfull.2
  · simpa only [Real.rpow_one,J,H0,q,Function.comp_def,μ] using hβfull.2

end Asakura.Chapter11
