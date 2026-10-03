import Chapter2FiniteLocalizedDensity
import Chapter2ProbabilityErrorSum

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
open Asakura.FullAudit
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

/-- The finite-interval density conclusion with no bounds on A or H:
actual adapted elementary processes approximate the original H in
probability for the pathwise pth-power integral. -/
theorem finite_step_density
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
    (p : ℝ) (hp : 0 < p)
    (hi : ∀ᵐ ω ∂P, Integrable (fun r => |H (ω,projIcc 0 b hb.le r)|^p)
      (intervalStieltjes 0 b hb.le (A ω) (hA ω)
        (fun r hr => (hc ω r hr).mono inter_subset_left)).measure) :
    ∃ (N : ℕ → ℕ) (u : ℕ → ℕ → Icc (0:ℝ) b) (V : ℕ → ℕ → Ω → ℝ),
      (∀ n, StrictMonoOn (u n) (Iic (N n))) ∧
      (∀ n j, j < N n → Measurable[F (u n j)] (V n j) ∧ MemLp (V n j) ∞ P) ∧
      (∀ n, ∀ᵐ ω ∂P, Integrable (fun r =>
        |(∑ j ∈ Finset.range (N n), (Ico (u n j) (u n (j+1))).indicator (fun _ => V n j ω)
          (projIcc 0 b hb.le r))-H (ω,projIcc 0 b hb.le r)| ^ p)
          (intervalStieltjes 0 b hb.le (A ω) (hA ω)
            (fun r hr => (hc ω r hr).mono inter_subset_left)).measure) ∧
      ∀ ε > 0, Tendsto (fun n => P {ω | ε ≤ ∫ r,
        |(∑ j ∈ Finset.range (N n), (Ico (u n j) (u n (j+1))).indicator (fun _ => V n j ω)
          (projIcc 0 b hb.le r))-H (ω,projIcc 0 b hb.le r)| ^ p
          ∂(intervalStieltjes 0 b hb.le (A ω) (hA ω)
            (fun r hr => (hc ω r hr).mono inter_subset_left)).measure}) atTop (𝓝 0) := by
  classical
  obtain ⟨N,u,V,hmono,hVm,hVbound,happrox⟩ :=
    finite_localized_clipped_step_approximation P b hb A hA hc hm F hF hle had hnull H hH p hp
  let μ := fun ω => (intervalStieltjes 0 b hb.le (A ω) (hA ω)
    (fun r hr => (hc ω r hr).mono inter_subset_left)).measure
  letI (ω : Ω) : IsFiniteMeasure (μ ω) := intervalStieltjes_finite 0 b hb.le (A ω) (hA ω) _
  let q : Ω × ℝ → Ω × Icc (0:ℝ) b := fun z => (z.1,projIcc 0 b hb.le z.2)
  have hq : Measurable q := measurable_fst.prodMk (continuous_projIcc.measurable.comp measurable_snd)
  let H0 := H ∘ q
  have hH0 : Measurable H0 := (hH.mono (progressive_space_le_product F hle) le_rfl).comp hq
  let k := fun n : ℕ => (n:ℝ)+1
  let Hm := fun n z => max (-(k n)) (min (k n) (H0 z))
  have hHm n : Measurable (Hm n) := measurable_const.max (measurable_const.min hH0)
  have hHmb n z : |Hm n z| ≤ k n :=
    abs_le.2 ⟨le_max_left _ _,max_le (by dsimp [k]; linarith [Nat.cast_nonneg (α := ℝ) n]) (min_le_left _ _)⟩
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
  let R := fun n ω => ∫ r, |J n (ω,r)-H0 (ω,r)|^p ∂μ ω
  let U := fun n ω => ∫ r, |J n (ω,r)-Hm n (ω,r)|^p ∂μ ω
  let W := fun n ω => ∫ r, |Hm n (ω,r)-H0 (ω,r)|^p ∂μ ω
  have hWi n ω (hiω : Integrable (fun r => |H0 (ω,r)|^p) (μ ω)) : Integrable (fun r => |Hm n (ω,r)-H0 (ω,r)|^p) (μ ω) := by
    apply hiω.mono' ((((hHm n).sub hH0).comp measurable_prodMk_left).norm.pow_const p).aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro r
    change ‖|Hm n (ω,r)-H0 (ω,r)|^p‖ ≤ |H0 (ω,r)|^p
    rw [Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) p)]
    exact Real.rpow_le_rpow (abs_nonneg _) (truncation_error_bound (k n) _ (by dsimp [k]; positivity)) hp.le
  have hUi n ω : Integrable (fun r => |J n (ω,r)-Hm n (ω,r)|^p) (μ ω) := by
    apply Integrable.of_bound ((((hJ n).sub (hHm n)).comp measurable_prodMk_left).norm.pow_const p).aestronglyMeasurable ((2*k n)^p)
    apply Filter.Eventually.of_forall
    intro r
    change ‖|J n (ω,r)-Hm n (ω,r)|^p‖ ≤ (2*k n)^p
    rw [Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) p)]
    apply Real.rpow_le_rpow (abs_nonneg _) _ hp.le
    have hj := hVbound n (q (ω,r))
    change |J n (ω,r)| ≤ k n at hj
    have ht := abs_sub_le (J n (ω,r)) 0 (Hm n (ω,r))
    simp only [sub_zero,zero_sub,abs_neg] at ht
    linarith [hHmb n (ω,r)]
  have hRi n : ∀ᵐ ω ∂P, Integrable (fun r => |J n (ω,r)-H0 (ω,r)|^p) (μ ω) := by
    filter_upwards [hi] with ω hiω
    apply (((hUi n ω).add (hWi n ω hiω)).const_mul ((2:ℝ)^p)).mono'
      ((((hJ n).sub hH0).comp measurable_prodMk_left).norm.pow_const p).aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro r
    change ‖|J n (ω,r)-H0 (ω,r)|^p‖ ≤
      (2:ℝ)^p*(|J n (ω,r)-Hm n (ω,r)|^p+|Hm n (ω,r)-H0 (ω,r)|^p)
    rw [Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) p)]
    exact power_error_triangle _ _ _ p hp.le
  have hbnd n : ∀ᵐ ω ∂P, R n ω ≤ (2:ℝ)^p*(U n ω+W n ω) := by
    filter_upwards [hi] with ω hiω
    have h := integral_mono_of_nonneg (μ := μ ω)
      (.of_forall (fun r => Real.rpow_nonneg (abs_nonneg (J n (ω,r)-H0 (ω,r))) p))
      (((hUi n ω).add (hWi n ω hiω)).const_mul ((2:ℝ)^p))
      (.of_forall (fun r => power_error_triangle (J n (ω,r)) (Hm n (ω,r)) (H0 (ω,r)) p hp.le))
    change (∫ r, |J n (ω,r)-H0 (ω,r)|^p ∂μ ω) ≤
      ∫ r, (2:ℝ)^p*(|J n (ω,r)-Hm n (ω,r)|^p+|Hm n (ω,r)-H0 (ω,r)|^p) ∂μ ω at h
    rw [integral_const_mul,integral_add (hUi n ω) (hWi n ω hiω)] at h
    exact h
  have hWm n : Measurable (W n) := random_stieltjes_integral_measurable 0 b hb.le A hA hc hm
    (fun z => |Hm n z-H0 z|^p) (((hHm n).sub hH0).norm.pow_const p)
  have hWlim : ∀ᵐ ω ∂P, Tendsto (fun n => W n ω) atTop (𝓝 0) := by
    filter_upwards [hi] with ω hiω
    have h := (truncation_power_integral_limit (μ ω) (fun r => H0 (ω,r))
      (hH0.comp measurable_prodMk_left).aestronglyMeasurable p hp hiω).comp (tendsto_add_atTop_nat 1)
    simpa only [Function.comp_def,Nat.cast_add,Nat.cast_one] using h
  refine ⟨N,u,V,hmono,hVm,hRi,?_⟩
  intro ε hε
  exact probability_error_sum_limit P R U W ((2:ℝ)^p) (Real.rpow_pos_of_pos (by norm_num) p) hbnd
    happrox (fun δ hδ => nonnegative_ae_limit_probability P W hWm
      (fun n ω => integral_nonneg (fun r => Real.rpow_nonneg (abs_nonneg _) p))
      hWlim δ hδ) ε hε

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.finite_step_density
