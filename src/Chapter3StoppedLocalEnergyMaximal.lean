import Chapter2StoppedM2Equivalence
import Chapter2CovarianceContinuity
import Chapter3SummablePathErrors

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter3Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

/-- Doob's estimate with an actual quadratic-variation bound. Integrability
of the quadratic variation and the measurable continuous path norm are
consequences, not separate inputs. -/
theorem stopped_local_energy_maximal_bound
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (X C : ClosedTime T → Ω → ℝ) (hX : LocalMProcessWitness P F X)
    (hC : LocalCovarianceWitness P F X X C)
    (σ : Ω → ClosedTime T) (hσ : ∀ t, MeasurableSet[F t] {ω | σ ω ≤ t})
    (hσt : ∀ ω, σ ω < ⊤) (V : Ω → ℝ) (hV : Integrable V P)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hbound : ∀ᵐ ω ∂P, 0 ≤ C (σ ω) ω ∧ C (σ ω) ω ≤ δ^2*V ω) :
    ∃ hc : ∀ ω, Continuous (fun t => X (min (σ ω) t) ω),
      AEStronglyMeasurable (continuousPath (fun t ω => X (min (σ ω) t) ω) hc) P ∧
      eLpNorm (continuousPath (fun t ω => X (min (σ ω) t) ω) hc) 2 P ≤
        ENNReal.ofReal (2*δ*Real.sqrt (∫ ω, |V ω| ∂P)) := by
  have hiC : Integrable (fun ω => C (σ ω) ω) P := by
    apply ((hV.abs).const_mul (δ^2)).mono' (by
      have hm := ((hC.stopped_regular P F hF hle hX hX σ hσ hσt).1 ⊤).mono (hle ⊤) le_rfl
      simpa only [min_top_right] using hm.aestronglyMeasurable)
    filter_upwards [hbound] with ω hω
    rw [Real.norm_eq_abs,abs_of_nonneg hω.1]
    exact hω.2.trans (mul_le_mul_of_nonneg_left (le_abs_self _) (sq_nonneg _))
  obtain ⟨hc,hm,hn⟩ := local_stop_path_memLp_of_integrable_variation P F hF hle hnull
    X C hX hC σ hσ hσt hiC
  refine ⟨hc,hm.aestronglyMeasurable,hn.trans ?_⟩
  have hnon : 0 ≤ ∫ ω, C (σ ω) ω ∂P := integral_nonneg_of_ae (hbound.mono (fun _ h => h.1))
  rw [ENNReal.ofReal_rpow_of_nonneg hnon (by norm_num),← Real.sqrt_eq_rpow]
  have htwo : (2:ENNReal) = ENNReal.ofReal (2:ℝ) := by norm_num
  rw [htwo,← ENNReal.ofReal_mul (by norm_num)]
  apply ENNReal.ofReal_le_ofReal
  have hineq : (∫ ω, C (σ ω) ω ∂P) ≤ δ^2*(∫ ω, |V ω| ∂P) := by
    rw [← integral_const_mul]
    apply integral_mono_ae hiC ((hV.abs).const_mul _)
    exact hbound.mono (fun ω hω => hω.2.trans (mul_le_mul_of_nonneg_left (le_abs_self _) (sq_nonneg _)))
  have hs := Real.sqrt_le_sqrt hineq
  rw [Real.sqrt_mul (sq_nonneg δ),Real.sqrt_sq hδ] at hs
  nlinarith

/-- Summable dyadic quadratic-variation errors imply almost sure uniform
convergence on the full finite prefix, without extracting a subsequence. -/
theorem stopped_local_dyadic_energy_ae_uniform
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (X C : ℕ → ClosedTime T → Ω → ℝ) (hX : ∀ n, LocalMProcessWitness P F (X n))
    (hC : ∀ n, LocalCovarianceWitness P F (X n) (X n) (C n))
    (σ : Ω → ClosedTime T) (hσ : ∀ t, MeasurableSet[F t] {ω | σ ω ≤ t})
    (hσt : ∀ ω, σ ω < ⊤) (V : Ω → ℝ) (hV : Integrable V P)
    (hbound : ∀ n, ∀ᵐ ω ∂P, 0 ≤ C n (σ ω) ω ∧ C n (σ ω) ω ≤ ((1/2:ℝ)^n)^2*V ω) :
    ∃ hc : ∀ n ω, Continuous (fun t => X n (min (σ ω) t) ω),
      ∀ᵐ ω ∂P, Tendsto (fun n => continuousPath (fun t ω => X n (min (σ ω) t) ω) (hc n) ω) atTop (𝓝 0) := by
  have h n := stopped_local_energy_maximal_bound P F hF hle hnull (X n) (C n) (hX n) (hC n)
    σ hσ hσt V hV ((1/2:ℝ)^n) (pow_nonneg (by norm_num) n) (hbound n)
  choose hc hm hn using h
  refine ⟨hc,?_⟩
  apply ae_zero_of_dyadic_l2_errors P _ hm (2*Real.sqrt (∫ ω, |V ω| ∂P))
  intro n
  apply (hn n).trans_eq
  congr 1
  ring

end Asakura.Chapter3Complete
#print axioms Asakura.Chapter3Complete.stopped_local_energy_maximal_bound
#print axioms Asakura.Chapter3Complete.stopped_local_dyadic_energy_ae_uniform
