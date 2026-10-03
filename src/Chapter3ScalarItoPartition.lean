import Chapter3CovariationIntegralApproximation
import Chapter3SemimartingaleIntegralApproximation
import Chapter3PartitionTaylor

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter3Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false

/-- Scalar Ito formula with an actual common oscillation partition. Both
stochastic sums are identified by the previously proved approximation
theorems; convergence and the Taylor remainder are not hypotheses. -/
theorem scalar_ito_from_common_partition
    {Ω ι : Type*} [Countable ι] {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (X A M C Z J : ClosedTime T → Ω → ℝ)
    (hX : SemimartingaleDecomposition P F X A M)
    (hC : LocalCovarianceWitness P F M M C)
    (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f)
    (hXm : ∀ t, t < ⊤ → Measurable[F t] (X t))
    (c : ℕ → ℝ) (hc : ∀ k, 0 ≤ c k) (hcT : ∀ k, (c k:EReal) < T)
    (hcc : ∀ t, t < ⊤ → ∃ k, t < realTimeClamp (T := T) (c k))
    (hZ : SemimartingaleIntegralFormula P F c hc A M
      (fun z => deriv f (X (realTimeClamp z.2) z.1)) Z)
    (hJ : VariationIntegralFormula P c hc C
      (fun z => iteratedDeriv 2 f (X (realTimeClamp z.2) z.1)) J)
    (τ : ℕ → ℕ → Ω → ClosedTime T)
    (hτ : ∀ n j t, MeasurableSet[F t] {ω | τ n j ω ≤ t})
    (hτm : ∀ n ω, Monotone (fun j => τ n j ω))
    (hτt : ∀ n j ω, τ n j ω < ⊤) (hτ0 : ∀ n ω, τ n 0 ω = ⊥)
    (hτc : ∀ n ω t, t < ⊤ → ∃ j, t < τ n j ω)
    (q : ι → Iio (⊤ : ClosedTime T)) (hq : DenseRange q)
    (hbA : ∀ n j i, eLpNorm (fun ω =>
      A (min (τ n (j+1) ω) (q i).val) ω-A (min (τ n j ω) (q i).val) ω) ∞ P ≤ ENNReal.ofReal ((1/2:ℝ)^n))
    (hbM : ∀ n j i, eLpNorm (fun ω =>
      M (min (τ n (j+1) ω) (q i).val) ω-M (min (τ n j ω) (q i).val) ω) ∞ P ≤ ENNReal.ofReal ((1/2:ℝ)^n))
    (hbD : ∀ n j i, eLpNorm (fun ω =>
      deriv f (X (min (τ n (j+1) ω) (q i).val) ω)-deriv f (X (min (τ n j ω) (q i).val) ω)) ∞ P ≤ ENNReal.ofReal ((1/2:ℝ)^n))
    (hbE : ∀ n j i, eLpNorm (fun ω =>
      iteratedDeriv 2 f (X (min (τ n (j+1) ω) (q i).val) ω)-
      iteratedDeriv 2 f (X (min (τ n j ω) (q i).val) ω)) ∞ P ≤ ENNReal.ofReal ((1/2:ℝ)^n)) :
    ∀ᵐ ω ∂P, ∀ t, t < ⊤ → f (X t ω) = f (X ⊥ ω)+Z t ω+J t ω/2 := by
  let D := fun t ω => deriv f (X t ω)
  let E := fun t ω => iteratedDeriv 2 f (X t ω)
  have hd : Continuous (deriv f) := hf.continuous_deriv (by norm_num)
  have he : Continuous (iteratedDeriv 2 f) := hf.continuous_iteratedDeriv 2 le_rfl
  have hdm t (ht : t < ⊤) : Measurable[F t] (D t) := hd.measurable.comp (hXm t ht)
  have hem t (ht : t < ⊤) : Measurable[F t] (E t) := he.measurable.comp (hXm t ht)
  have hdc ω t (ht : t < ⊤) : ContinuousAt (fun s => D s ω) t :=
    hd.continuousAt.comp (hX.continuous ω t ht)
  have hec ω t (ht : t < ⊤) : ContinuousAt (fun s => E s ω) t :=
    he.continuousAt.comp (hX.continuous ω t ht)
  have hct k : realTimeClamp (T := T) (c k) < ⊤ := by
    change (realTimeClamp (c k) : EReal) < T
    rw [real_time_clamp_eq _ (hc k) (hcT k).le]
    exact hcT k
  have hlu k := semimartingale_integral_approximation P hT F hF hle hnull X A M D Z hX
    hdm hdc c hc hcT hcc hZ τ hτ hτm hτt hτ0 hτc q hq hbD _ (hct k)
  have hlv k := semimartingale_covariation_integral_approximation P hT F hF hle hnull
    X X A A M M C E hX hX hC hem hec τ hτ hτm hτt hτ0 hτc q hq
    hbM hbM hbA hbA hbE c hc hcT J hJ k
  have hlq k := semimartingale_covariation_approximation P hT F hF hle hnull
    X X A A M M C (fun _ _ => 1) hX hX hC (fun _ _ => measurable_const)
    (fun _ _ _ => continuousAt_const) τ hτ hτm hτt hτ0 hτc q hq
    hbM hbM hbA hbA (fun _ _ _ => by simp) (c k) (hc k) (hcT k)
  have ho n j := stopped_dense_essential_bound P q hq E hec (τ n j) (τ n (j+1))
    (fun ω => hτm n ω (Nat.le_succ j)) (hτt n (j+1)) ((1/2:ℝ)^n)
    (pow_nonneg (by norm_num) n) (hbE n j)
  filter_upwards [ae_all_iff.mpr hlu,ae_all_iff.mpr hlv,ae_all_iff.mpr hlq,
    ae_all_iff.mpr (fun n => ae_all_iff.mpr (ho n))] with ω hu hv hqω hoω
  intro t ht
  obtain ⟨k,hk⟩ := hcc t ht
  have hmin : min (realTimeClamp (c k)) t = t := min_eq_right hk.le
  obtain ⟨hCv,hCr,hQ⟩ := hqω k
  have hu' := (hu k).tendsto_at t
  have hv' := (hv k).tendsto_at t
  have hQ' := hQ.tendsto_at t
  simp only [hmin] at hu' hv' hQ'
  have herr n := stopped_partition_taylor_sum (fun t => X t ω) (hX.continuous ω)
    f hf (fun j => τ n j ω) (hτm n ω) (hτ0 n ω) (fun j => hτt n j ω)
    (hτc n ω) ((1/2:ℝ)^n) (pow_nonneg (by norm_num) n) (hoω n) t ht
  have heps : Tendsto (fun n => (1/2:ℝ)^n/2) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1/2:ℝ) < 1)).div_const 2
  have hid := Asakura.Chapter3Written.ito_limit_identification hu' hv' hQ' heps herr
  linarith

end Asakura.Chapter3Complete
#print axioms Asakura.Chapter3Complete.scalar_ito_from_common_partition
