import Chapter2Lenglart

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

/-- The epsilon-delta step of Lenglart's argument, keeping the probability
terms as actual event probabilities rather than assumed real bounds. -/
theorem probability_limit_of_arbitrary_remainder
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (E : ℕ → Set Ω) (G : ℝ → ℕ → Set Ω)
    (hG : ∀ δ > 0, Tendsto (fun n => P (G δ n)) atTop (𝓝 0))
    (hb : ∀ η > 0, ∃ δ > 0, ∀ n, P.real (E n) ≤ P.real (G δ n)+η) :
    Tendsto (fun n => P (E n)) atTop (𝓝 0) := by
  have hr : Tendsto (fun n => P.real (E n)) atTop (𝓝 0) := by
    apply tendsto_order.2
    constructor
    · intro a ha
      exact .of_forall (fun n => ha.trans_le ENNReal.toReal_nonneg)
    · intro ε hε
      obtain ⟨δ,hδ,hbδ⟩ := hb (ε/2) (half_pos hε)
      have hg : Tendsto (fun n => P.real (G δ n)) atTop (𝓝 0) := by
        have h := (ENNReal.continuousAt_toReal (by simp : (0:ℝ≥0∞) ≠ ∞)).tendsto.comp (hG δ hδ)
        simpa only [Measure.real,Function.comp_def,ENNReal.toReal_zero] using h
      filter_upwards [hg.eventually (gt_mem_nhds (half_pos hε))] with n hn
      linarith [hbδ n]
  have h := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hr
  simpa only [Function.comp_def,Measure.real,ENNReal.ofReal_toReal (measure_ne_top _ _),ENNReal.ofReal_zero] using h

/-- A sequence of actual continuous local martingales tends locally
uniformly to zero in probability if their actual quadratic variations do.
All stopping/maximal estimates come from the proved Lenglart inequality. -/
theorem local_martingale_probability_of_quadratic_variation
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (X C : ℕ → ClosedTime T → Ω → ℝ)
    (hX : ∀ n, LocalMProcessWitness P F (X n))
    (hC : ∀ n, LocalCovarianceWitness P F (X n) (X n) (C n))
    (σ : Ω → ClosedTime T) (hσ : ∀ t, MeasurableSet[F t] {ω | σ ω ≤ t})
    (hσtop : ∀ ω, σ ω < ⊤)
    (hprob : ∀ δ > 0, Tendsto (fun n => P {ω | δ ≤ C n (σ ω) ω}) atTop (𝓝 0))
    (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n => P {ω | ε ≤ ⨆ t, |X n (min (σ ω) t) ω|}) atTop (𝓝 0) := by
  apply probability_limit_of_arbitrary_remainder P _ (fun δ n => {ω | δ ≤ C n (σ ω) ω}) hprob
  intro η hη
  refine ⟨η*ε^2,mul_pos hη (sq_pos_of_pos hε),?_⟩
  intro n
  have h := (local_lenglart P F hF hle hnull (X n) (C n) (hX n) (hC n)
    σ hσ hσtop ε (η*ε^2) hε (mul_pos hη (sq_pos_of_pos hε))).1
  rw [mul_div_cancel_right₀ η (ne_of_gt (sq_pos_of_pos hε))] at h
  linarith

/-- Conversely, locally uniform probability convergence of actual local
martingales forces their quadratic variations to tend to zero in probability. -/
theorem quadratic_variation_probability_of_local_martingale
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (X C : ℕ → ClosedTime T → Ω → ℝ)
    (hX : ∀ n, LocalMProcessWitness P F (X n))
    (hC : ∀ n, LocalCovarianceWitness P F (X n) (X n) (C n))
    (σ : Ω → ClosedTime T) (hσ : ∀ t, MeasurableSet[F t] {ω | σ ω ≤ t})
    (hσtop : ∀ ω, σ ω < ⊤)
    (hprob : ∀ ε > 0, Tendsto (fun n => P {ω | ε ≤ ⨆ t, |X n (min (σ ω) t) ω|}) atTop (𝓝 0))
    (δ : ℝ) (hδ : 0 < δ) :
    Tendsto (fun n => P {ω | δ ≤ C n (σ ω) ω}) atTop (𝓝 0) := by
  apply probability_limit_of_arbitrary_remainder P _
    (fun ε n => {ω | ε ≤ ⨆ t, |X n (min (σ ω) t) ω|}) hprob
  intro η hη
  refine ⟨Real.sqrt (η*δ),Real.sqrt_pos.2 (mul_pos hη hδ),?_⟩
  intro n
  have h := (local_lenglart P F hF hle hnull (X n) (C n) (hX n) (hC n)
    σ hσ hσtop (Real.sqrt (η*δ)) δ (Real.sqrt_pos.2 (mul_pos hη hδ)) hδ).2
  rw [Real.sq_sqrt (mul_pos hη hδ).le,mul_div_cancel_right₀ η hδ.ne'] at h
  linarith

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.probability_limit_of_arbitrary_remainder
#print axioms Asakura.Chapter2Complete.local_martingale_probability_of_quadratic_variation
#print axioms Asakura.Chapter2Complete.quadratic_variation_probability_of_local_martingale
