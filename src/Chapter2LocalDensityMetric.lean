import Chapter2LocalDensity
import Chapter2IntegrandMetricLimit

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
open Asakura.FullAudit
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

/-- The constructed elementary approximants converge in the actual
expected Stieltjes Lp metric, with no boundedness assumption on A or H. -/
theorem local_step_density_in_metric
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (b : ℕ → ℝ) (hb : ∀ n, 0 < b n) (hbmono : Monotone b)
    (A : Ω → ℝ → ℝ)
    (hA : ∀ n ω, MonotoneOn (A ω) (Icc 0 (b n)))
    (hc : ∀ n ω, ContinuousOn (A ω) (Icc 0 (b n)))
    (hm : ∀ t, Measurable (fun ω => A ω t))
    (F : ℝ → MeasurableSpace Ω) (hF : Monotone F)
    (hle : ∀ t, F t ≤ ‹MeasurableSpace Ω›)
    (had : ∀ n t, t ∈ Icc 0 (b n) → Measurable[F t] (fun ω => A ω t))
    (hnull : ∀ t N, MeasurableSet N → P N = 0 → MeasurableSet[F t] N)
    (H : Ω × ℝ → ℝ)
    (hH : ∀ n, @Measurable _ _ (progressiveSpace (fun t : Icc (0:ℝ) (b n) => F t.val)) inferInstance
      (fun z : Ω × Icc (0:ℝ) (b n) => H (z.1,z.2.val)))
    (p : ℝ) (hp : 0 < p)
    (hi : ∀ n, ∀ᵐ ω ∂P, Integrable (fun r => |H (ω,r)|^p)
      (intervalStieltjes 0 (b n) (hb n).le (A ω) (hA n ω)
        (fun r hr => (hc n ω r hr).mono inter_subset_left)).measure) :
    ∃ (N : ℕ → ℕ) (u : ℕ → ℕ → ℝ) (V : ℕ → ℕ → Ω → ℝ),
      (∀ n, StrictMonoOn (u n) (Iic (N n))) ∧
      (∀ n j, j ≤ N n → u n j ∈ Icc 0 (b n)) ∧
      (∀ n j, j < N n → Measurable[F (u n j)] (V n j) ∧ MemLp (V n j) ∞ P) ∧
      Tendsto (fun n => ∫ ω, ∑' j : ℕ, (1/2:ℝ)^(j+1)*min 1
        ((∫ r, |(∑ i ∈ Finset.range (N n),
          (Ico (u n i) (u n (i+1))).indicator (fun _ => V n i ω) r)-H (ω,r)|^p
          ∂(intervalStieltjes 0 (b j) (hb j).le (A ω) (hA j ω)
            (fun r hr => (hc j ω r hr).mono inter_subset_left)).measure)^(1/p)) ∂P)
        atTop (𝓝 0) := by
  classical
  letI (j : ℕ) : Fact (0 ≤ b j) := ⟨(hb j).le⟩
  obtain ⟨N,u,V,hmono,hmem,hadapt,hint,hprob⟩ := local_step_density P b hb hbmono A hA hc hm F hF hle had hnull H hH p hp hi
  let μ := fun j ω => (intervalStieltjes 0 (b j) (hb j).le (A ω) (hA j ω)
    (fun r hr => (hc j ω r hr).mono inter_subset_left)).measure
  let J := fun n (z : Ω × ℝ) => ∑ i ∈ Finset.range (N n),
    (Ico (u n i) (u n (i+1))).indicator (fun _ => V n i z.1) z.2
  have hJ n : Measurable (J n) := by
    apply Finset.measurable_sum
    intro i hi
    have hV : Measurable (fun z : Ω × ℝ => V n i z.1) :=
      (((hadapt n i (Finset.mem_range.1 hi)).1).mono (hle _) le_rfl).comp measurable_fst
    have h := hV.indicator (measurable_snd (measurableSet_Ico (a := u n i) (b := u n (i+1))))
    convert h using 1
    funext z
    by_cases hz : z.2 ∈ Ico (u n i) (u n (i+1)) <;> simp [hz]
  let R := fun n j ω => ∫ r, |J n (ω,r)-H (ω,r)|^p ∂μ j ω
  have hRm n j : Measurable (R n j) := by
    let q : Ω × ℝ → Ω × Icc (0:ℝ) (b j) := fun z => (z.1,projIcc 0 (b j) (hb j).le z.2)
    have hq : Measurable q := measurable_fst.prodMk (continuous_projIcc.measurable.comp measurable_snd)
    let Hj := fun z : Ω × ℝ => H (z.1,(projIcc 0 (b j) (hb j).le z.2:ℝ))
    have hHj : Measurable Hj := ((hH j).mono
      (progressive_space_le_product (fun t : Icc (0:ℝ) (b j) => F t.val) (fun t => hle t.val)) le_rfl).comp hq
    have hmeas := random_stieltjes_integral_measurable 0 (b j) (hb j).le A (hA j) (hc j) hm
      (fun z => |J n z-Hj z|^p) (((hJ n).sub hHj).norm.pow_const p)
    have he : R n j = fun ω => ∫ r, |J n (ω,r)-Hj (ω,r)|^p ∂μ j ω := by
      funext ω
      apply integral_congr_ae
      filter_upwards [interval_stieltjes_ae_mem_Ioc 0 (b j) (hb j).le (A ω) (hA j ω)
        (fun r hr => (hc j ω r hr).mono inter_subset_left)] with r hr
      have hpr : (projIcc 0 (b j) (hb j).le r:ℝ) = r :=
        congrArg Subtype.val (projIcc_of_mem (hb j).le ⟨hr.1.le,hr.2⟩)
      change |J n (ω,r)-H (ω,r)|^p = |J n (ω,r)-H (ω,(projIcc 0 (b j) (hb j).le r:ℝ))|^p
      rw [hpr]
    rw [he]
    exact hmeas
  refine ⟨N,u,V,hmono,hmem,hadapt,?_⟩
  exact expected_integrand_metric_limit P R hRm
    (fun n j ω => integral_nonneg (fun r => Real.rpow_nonneg (abs_nonneg _) p)) p hp hprob

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.local_step_density_in_metric
