import Chapter2FiniteDensityReal

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
open Asakura.FullAudit
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

/-- Actual elementary strategies on increasing finite horizons can be
chosen as a single sequence approximating H on every fixed horizon.
Together with cofinality of b, this is the local density conclusion on
[0,T), with both finite and infinite T allowed. -/
theorem local_step_density
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
      (∀ n, ∀ᵐ ω ∂P, Integrable (fun r =>
        |(∑ j ∈ Finset.range (N n), (Ico (u n j) (u n (j+1))).indicator (fun _ => V n j ω) r)-H (ω,r)|^p)
          (intervalStieltjes 0 (b n) (hb n).le (A ω) (hA n ω)
            (fun r hr => (hc n ω r hr).mono inter_subset_left)).measure) ∧
      ∀ m (ε : ℝ), 0 < ε → Tendsto (fun n => P {ω | ε ≤ ∫ r,
        |(∑ j ∈ Finset.range (N n), (Ico (u n j) (u n (j+1))).indicator (fun _ => V n j ω) r)-H (ω,r)|^p
          ∂(intervalStieltjes 0 (b m) (hb m).le (A ω) (hA m ω)
            (fun r hr => (hc m ω r hr).mono inter_subset_left)).measure}) atTop (𝓝 0) := by
  classical
  letI (n : ℕ) : Fact (0 ≤ b n) := ⟨(hb n).le⟩
  have hex n := finite_step_density_real P (b n) (hb n) A (hA n) (hc n) hm F hF hle
    (had n) hnull H (hH n) p hp (hi n)
  choose Ns us Vs hmono hmem hadapt hint hlim using hex
  let μ := fun n ω => (intervalStieltjes 0 (b n) (hb n).le (A ω) (hA n ω)
    (fun r hr => (hc n ω r hr).mono inter_subset_left)).measure
  let E := fun n k ω r => |(∑ j ∈ Finset.range (Ns n k),
    (Ico (us n k j) (us n k (j+1))).indicator (fun _ => Vs n k j ω) r)-H (ω,r)|^p
  let δ := fun n : ℕ => 1/((n:ℝ)+1)
  have hδ n : 0 < δ n := by dsimp [δ]; positivity
  have hchoice n : ∃ k, P {ω | δ n ≤ ∫ r, E n k ω r ∂μ n ω} < ENNReal.ofReal (δ n) := by
    exact ((hlim n (δ n) (hδ n)).eventually (gt_mem_nhds (ENNReal.ofReal_pos.2 (hδ n)))).exists
  choose k hk using hchoice
  have hrestr m n (hmn : m ≤ n) ω : μ m ω = (μ n ω).restrict (Iic (b m)) :=
    interval_stieltjes_restrict_Iic 0 (b n) (b m) (hb m).le (hbmono hmn) (A ω)
      (hA n ω) (fun r hr => (hc n ω r hr).mono inter_subset_left)
      (hA m ω) (fun r hr => (hc m ω r hr).mono inter_subset_left)
  have hδlim : Tendsto δ atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hupper : Tendsto (fun n => ENNReal.ofReal (δ n)) atTop (𝓝 0) := by
    have h := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hδlim
    simpa only [Function.comp_def,ENNReal.ofReal_zero] using h
  refine ⟨(fun n => Ns n (k n)),(fun n => us n (k n)),(fun n => Vs n (k n)),
    (fun n => hmono n (k n)),(fun n => hmem n (k n)),(fun n => hadapt n (k n)),(fun n => hint n (k n)),?_⟩
  intro m ε hε
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
    (.of_forall (fun n => bot_le))
  filter_upwards [eventually_ge_atTop m,hδlim.eventually (gt_mem_nhds hε)] with n hmn hδε
  apply le_trans (measure_mono_ae (μ := P) ?_) (hk n).le
  filter_upwards [hint n (k n)] with ω hω
  intro hεR
  have hle : (∫ r, E n (k n) ω r ∂μ m ω) ≤ ∫ r, E n (k n) ω r ∂μ n ω := by
    rw [hrestr m n hmn ω]
    exact setIntegral_le_integral hω (.of_forall (fun r => Real.rpow_nonneg (abs_nonneg _) p))
  change δ n ≤ ∫ r, E n (k n) ω r ∂μ n ω
  exact hδε.le.trans (hεR.trans hle)

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.local_step_density
