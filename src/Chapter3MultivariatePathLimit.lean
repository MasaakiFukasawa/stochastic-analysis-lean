import Chapter3MultivariatePartitionTaylor

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter3Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

/-- Pathwise assembly of the multidimensional proof. Taylor control is
derived from C² and compactness. The convergence inputs are the actual
coordinate partition sums, to be supplied by the stochastic theorems. -/
theorem multivariate_ito_path_limit
    {T : EReal} [Fact (0 ≤ T)] {d : ℕ}
    (X : ClosedTime T → (Fin d → ℝ))
    (hX : ∀ s, s < ⊤ → ContinuousAt X s)
    (f : (Fin d → ℝ) → ℝ) (hf : ContDiff ℝ 2 f)
    (τ : ℕ → ℕ → ClosedTime T) (hτ : ∀ n, Monotone (τ n))
    (h0 : ∀ n, τ n 0 = ⊥)
    (hco : ∀ n t, t < ⊤ → ∃ N, t < τ n N)
    (t : ClosedTime T) (ht : t < ⊤)
    (η : ℕ → ℝ) (hη : Tendsto η atTop (𝓝 0))
    (hstep : ∀ n j, ‖X (min (τ n (j+1)) t)-X (min (τ n j) t)‖ ≤ η n)
    (Z : Fin d → ℝ) (J : Fin d → Fin d → ℝ) (Q : Fin d → ℝ)
    (hZ : ∀ i, Tendsto (fun n => partitionLinear (fun s => X s i)
      (fun s => fderiv ℝ f (X s) (Pi.single i 1)) (τ n) t) atTop (𝓝 (Z i)))
    (hJ : ∀ i k, Tendsto (fun n => partitionCross (fun s => X s i) (fun s => X s k)
      (fun s => fderiv ℝ (fderiv ℝ f) (X s) (Pi.single i 1) (Pi.single k 1)) (τ n) t)
      atTop (𝓝 (J i k)))
    (hQ : ∀ i, Tendsto (fun n => partitionCross (fun s => X s i) (fun s => X s i)
      (fun _ => 1) (τ n) t) atTop (𝓝 (Q i))) :
    f (X t) = f (X ⊥)+(∑ i, Z i)+(∑ i, ∑ k, J i k)/2 := by
  have hXs : Continuous (fun s => X (min t s)) := by
    apply continuous_iff_continuousAt.mpr
    intro s
    exact (hX _ ((min_le_left _ _).trans_lt ht)).comp
      (continuous_const.min continuous_id).continuousAt
  let Xs : C(ClosedTime T,Fin d → ℝ) := ⟨_,hXs⟩
  have hball s (hs : s ≤ t) : X s ∈ Metric.closedBall 0 ‖Xs‖ := by
    have h := Xs.norm_coe_le_norm s
    simpa only [Metric.mem_closedBall,dist_zero_right,Xs,ContinuousMap.coe_mk,min_eq_right hs] using h
  have hu := tendsto_finsetSum Finset.univ (fun i _ => hZ i)
  have hv := tendsto_finsetSum Finset.univ (fun i _ =>
    tendsto_finsetSum Finset.univ (fun k _ => hJ i k))
  have hq := tendsto_finsetSum Finset.univ (fun i _ => hQ i)
  have hr := (((tendsto_const_nhds (x := f (X t)-f (X ⊥))).sub hu).sub (hv.div_const 2)).abs
  have hb (ε : ℝ) (hε : 0 < ε) :
      |f (X t)-f (X ⊥)-(∑ i, Z i)-(∑ i, ∑ k, J i k)/2| ≤ (ε/2)*∑ i, Q i := by
    obtain ⟨δ,hδ,hTaylor⟩ := finite_dimensional_uniform_taylor hf ‖Xs‖ ε hε
    have hevent : ∀ᶠ n in atTop, η n ≤ δ :=
      (hη.eventually (gt_mem_nhds hδ)).mono (fun _ hn => hn.le)
    have hbnd := hevent.mono (fun n hn => by
      obtain ⟨N,hN⟩ := hco n t ht
      exact multivariate_partition_taylor_bound X f (τ n) (hτ n) (h0 n) t N hN.le
        ‖Xs‖ ε δ hTaylor hball (fun j => (hstep n j).trans hn))
    exact le_of_tendsto_of_tendsto hr (hq.const_mul (ε/2)) hbnd
  have hp : Tendsto (fun k : ℕ => (1/2:ℝ)^k*(∑ i, Q i)) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1/2:ℝ) < 1)).mul_const (∑ i, Q i)
  have hz : |f (X t)-f (X ⊥)-(∑ i, Z i)-(∑ i, ∑ k, J i k)/2| ≤ 0 := by
    apply ge_of_tendsto hp
    apply Filter.Eventually.of_forall
    intro n
    have h := hb (2*(1/2:ℝ)^n) (mul_pos (by norm_num) (pow_pos (by norm_num) n))
    simpa only [mul_div_cancel_left₀ _ (by norm_num : (2:ℝ) ≠ 0)] using h
  have he := abs_eq_zero.mp (le_antisymm hz (abs_nonneg _))
  linarith

end Asakura.Chapter3Complete
#print axioms Asakura.Chapter3Complete.multivariate_ito_path_limit
