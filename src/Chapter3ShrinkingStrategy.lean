import Chapter3StoppedMartingaleFromLp
import Chapter2BrownianHalfLineCovariance
import Chapter2BrownianSquare
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal
namespace Asakura.Chapter3Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

noncomputable def spikeWidth (n : ℕ) : ℝ := 1/((n:ℝ)+1)
noncomputable def spikeHolding (n : ℕ) (r : ℝ) : ℝ :=
  (Ico 1 (1+spikeWidth n)).indicator (fun _ => 1) r

/-- The integral against a simple holding strategy is the finite gain
formula printed in the definition, with no stochastic limit involved. -/
noncomputable def spikeReverse (X : ℝ → ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  spikeHolding n t*X t-(X (min (1+spikeWidth n) t)-X (min 1 t))

theorem spike_width_positive (n : ℕ) : 0 < spikeWidth n := by unfold spikeWidth; positivity

theorem spike_square_energy (n : ℕ) :
    (∫ r : ℝ, (spikeHolding n r)^2) = spikeWidth n := by
  have he : (fun r => (spikeHolding n r)^2) = (Ico 1 (1+spikeWidth n)).indicator (fun _ : ℝ => (1:ℝ)) := by
    funext r
    by_cases hr : r ∈ Ico 1 (1+spikeWidth n) <;> simp [spikeHolding,hr]
  rw [he,integral_indicator measurableSet_Ico,integral_const]
  simp only [smul_eq_mul,mul_one,Measure.real,Measure.restrict_apply_univ,Real.volume_Ico]
  rw [ENNReal.toReal_ofReal (by linarith [spike_width_positive n])]
  ring

theorem spike_energy_tends_zero : Tendsto (fun n => ∫ r : ℝ, (spikeHolding n r)^2) atTop (𝓝 0) := by
  simp only [spike_square_energy,spikeWidth]
  exact tendsto_one_div_add_atTop_nhds_zero_nat

theorem spike_reverse_at_start (X : ℝ → ℝ) (n : ℕ) : spikeReverse X n 1 = X 1 := by
  have hp := spike_width_positive n
  simp [spikeReverse,spikeHolding,show (1:ℝ) < 1+spikeWidth n by linarith,
    min_eq_right (show (1:ℝ) ≤ 1+spikeWidth n by linarith)]

theorem spike_holding_tends_zero {r : ℝ} (hr : r ≠ 1) :
    Tendsto (fun n => spikeHolding n r) atTop (𝓝 0) := by
  have hw : Tendsto (fun n => spikeWidth n) atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  apply tendsto_const_nhds.congr'
  rcases lt_or_gt_of_ne hr with h | h
  · exact Filter.Eventually.of_forall (fun n => by simp [spikeHolding,not_le.mpr h])
  · have hlim : Tendsto (fun n => 1+spikeWidth n) atTop (𝓝 (1:ℝ)) := by
      simpa using tendsto_const_nhds.add hw
    filter_upwards [hlim.eventually (gt_mem_nhds h)] with n hn
    simp [spikeHolding,not_lt.mpr hn.le]

/-- Actual Stieltjes energy tends to zero on every finite horizon. This
uses atomlessness, so the right-continuous endpoint value at 1 is retained. -/
theorem spike_energy_atomless (μ : Measure ℝ) [IsFiniteMeasure μ] [NullSingletonClass μ] :
    Tendsto (fun n => ∫ r, (spikeHolding n r)^2 ∂μ) atTop (𝓝 0) := by
  have hlim : Tendsto (fun n => ∫ r, (spikeHolding n r)^2 ∂μ) atTop (𝓝 (∫ _ : ℝ, (0:ℝ) ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => (1:ℝ))
    · intro n
      exact ((measurable_const.indicator measurableSet_Ico).pow_const 2).aestronglyMeasurable
    · exact integrable_const _
    · intro n
      apply Filter.Eventually.of_forall
      intro r
      by_cases hr : r ∈ Ico 1 (1+spikeWidth n) <;> simp [spikeHolding,hr]
    · have hne : ∀ᵐ r ∂μ, r ≠ (1:ℝ) := by
        rw [ae_iff]
        simpa using (measure_singleton (1:ℝ) : μ {(1:ℝ)} = 0)
      filter_upwards [hne] with r hr
      simpa using (spike_holding_tends_zero hr).pow 2
  simpa using hlim

theorem spike_energy_actual_stieltjes (d : ℝ) (hd : 0 ≤ d) (A : ℝ → ℝ)
    (hA : MonotoneOn A (Icc 0 d)) (hAc : ContinuousOn A (Icc 0 d)) :
    Tendsto (fun n => ∫ r, (spikeHolding n r)^2
      ∂(intervalStieltjes 0 d hd A hA (fun x hx => (hAc x hx).mono inter_subset_left)).measure)
      atTop (𝓝 0) := by
  let μ := (intervalStieltjes 0 d hd A hA (fun x hx => (hAc x hx).mono inter_subset_left)).measure
  letI : IsFiniteMeasure μ := intervalStieltjes_finite _ _ _ _ _ _
  letI : NullSingletonClass μ := interval_stieltjes_no_atoms_on _ _ _ _ _ _ hAc
  exact spike_energy_atomless μ

/-- The deterministic holding is an H0 generator for every filtration. -/
theorem spike_is_elementary
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (F : ℝ → MeasurableSpace Ω) (n : ℕ) :
    (1:ℝ) < 1+spikeWidth n ∧ Measurable[F 1] (fun _ : Ω => (1:ℝ)) ∧
      MemLp (fun _ : Ω => (1:ℝ)) ∞ P := by
  exact ⟨by linarith [spike_width_positive n],measurable_const,memLp_const _⟩

/-- Although these actual H0 strategies converge to zero in squared
Brownian energy, their reverse integrals fail to converge to zero even
in probability at time one. Nontriviality follows from E[B_1²]=1. -/
theorem brownian_spike_reverse_not_convergent
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (hB : IsPreBrownianReal B P) :
    ¬ TendstoInMeasure P
      (fun n ω => spikeReverse (fun r => B (Real.toNNReal r) ω) n 1) atTop (fun _ => 0) := by
  intro hzero
  have he n ω : spikeReverse (fun r => B (Real.toNNReal r) ω) n 1 = B 1 ω := by
    simpa using spike_reverse_at_start (fun r => B (Real.toNNReal r) ω) n
  have hconst : TendstoInMeasure P
      (fun n ω => spikeReverse (fun r => B (Real.toNNReal r) ω) n 1) atTop (B 1) := by
    intro ε hε
    simp only [he,edist_self,not_le.mpr hε,Set.setOf_false,measure_empty]
    exact tendsto_const_nhds
  have hae := tendstoInMeasure_ae_unique hconst hzero
  have hmean := brownian_square_mean P B hB 1
  have hz : (∫ ω, B 1 ω^2 ∂P) = 0 := by
    calc
      _ = ∫ _ : Ω, (0:ℝ) ∂P := integral_congr_ae (hae.mono (fun ω hω => by simp [hω]))
      _ = 0 := by simp
  norm_num at hmean
  linarith

end Asakura.Chapter3Complete
#print axioms Asakura.Chapter3Complete.spike_width_positive
#print axioms Asakura.Chapter3Complete.spike_square_energy
#print axioms Asakura.Chapter3Complete.spike_energy_tends_zero
#print axioms Asakura.Chapter3Complete.spike_reverse_at_start
#print axioms Asakura.Chapter3Complete.spike_is_elementary
#print axioms Asakura.Chapter3Complete.brownian_spike_reverse_not_convergent

#print axioms Asakura.Chapter3Complete.spike_holding_tends_zero
#print axioms Asakura.Chapter3Complete.spike_energy_atomless
#print axioms Asakura.Chapter3Complete.spike_energy_actual_stieltjes
