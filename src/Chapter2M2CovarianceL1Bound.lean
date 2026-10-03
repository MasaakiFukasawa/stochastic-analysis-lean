import Chapter2CovarianceContinuity
import Chapter2SquareRootCS
import Chapter2StoppedM2Equivalence
import Chapter2LocalCovarianceCS
import Chapter2M2IncrementEnergy

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
set_option maxHeartbeats 2300000
set_option backward.isDefEq.respectTransparency false

/-- The actual fixed-time covariance defines an L1 random variable, with
the sharp M2 bound used to exchange covariance and a parameter integral. -/
theorem m2_covariance_fixed_time_L1_bound
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)]
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (X Y A B C : ClosedTime T → Ω → ℝ)
    (hX : LocalMProcessWitness P F X) (hY : LocalMProcessWitness P F Y)
    (hX2 : ContinuousM2Witness P F X) (hY2 : ContinuousM2Witness P F Y)
    (hA : LocalCovarianceWitness P F X X A) (hB : LocalCovarianceWitness P F Y Y B)
    (hC : LocalCovarianceWitness P F X Y C) (d : ClosedTime T) (hd : d < ⊤) :
    Integrable (C d) P ∧ (∫ ω, ‖C d ω‖ ∂P) ≤
      ‖(hX2.moment ⊤).toLp (X ⊤)‖ * ‖(hY2.moment ⊤).toLp (Y ⊤)‖ := by
  have hstop : ∀ s, MeasurableSet[F s] {ω : Ω | d ≤ s} := by
    intro s
    by_cases hs : d ≤ s <;> simp [hs]
  obtain ⟨hAi,hAe⟩ := stopped_M2_energy P F hF hle hnull X A hX hA (fun _ => d) hstop
    (fun _ => hd) (continuous_m2_stopped P F hF hle X hX2 (fun _ => d) hstop)
  obtain ⟨hBi,hBe⟩ := stopped_M2_energy P F hF hle hnull Y B hY hB (fun _ => d) hstop
    (fun _ => hd) (continuous_m2_stopped P F hF hle Y hY2 (fun _ => d) hstop)
  have hA0 : ∀ᵐ ω ∂P, 0 ≤ A d ω := by
    filter_upwards [local_quadratic_variation_initial P F X A hX hA,
      local_quadratic_variation_monotone P F hF hle hnull X A hX hA] with ω hz hm
    have hh := hm (bot_lt_of_lt hd) hd bot_le
    simpa only [hz,Pi.zero_apply] using hh
  have hB0 : ∀ᵐ ω ∂P, 0 ≤ B d ω := by
    filter_upwards [local_quadratic_variation_initial P F Y B hY hB,
      local_quadratic_variation_monotone P F hF hle hnull Y B hY hB] with ω hz hm
    have hh := hm (bot_lt_of_lt hd) hd bot_le
    simpa only [hz,Pi.zero_apply] using hh
  obtain ⟨hprod,hcs⟩ := integrable_sqrt_product_bound P (A d) (B d) hAi hBi hA0 hB0
  have hp : ∀ᵐ ω ∂P, ‖C d ω‖ ≤ Real.sqrt (A d ω)*Real.sqrt (B d ω) := by
    filter_upwards [local_covariance_point_cs P F hF hle hnull X Y A B C hX hY hA hB hC] with ω hω
    simpa only [Real.norm_eq_abs] using hω d hd
  have hCi : Integrable (C d) P := hprod.mono'
    ((hC.adapted P F hX hY d hd).mono (hle d) le_rfl).aestronglyMeasurable hp
  refine ⟨hCi,(integral_mono_ae hCi.norm hprod hp).trans (hcs.trans ?_)⟩
  have hEX : (∫ ω, A d ω ∂P) ≤ ∫ ω, X ⊤ ω^2 ∂P := by
    have hh := continuous_martingale_increment_energy P F hle X hX2 d ⊤ le_top
    have hn : 0 ≤ ∫ ω, (X ⊤ ω-X d ω)^2 ∂P := integral_nonneg (fun ω => sq_nonneg _)
    rw [← hAe]
    linarith
  have hEY : (∫ ω, B d ω ∂P) ≤ ∫ ω, Y ⊤ ω^2 ∂P := by
    have hh := continuous_martingale_increment_energy P F hle Y hY2 d ⊤ le_top
    have hn : 0 ≤ ∫ ω, (Y ⊤ ω-Y d ω)^2 ∂P := integral_nonneg (fun ω => sq_nonneg _)
    rw [← hBe]
    linarith
  have hx := real_l2_norm_sq_integral P (X ⊤) (hX2.moment ⊤)
  have hy := real_l2_norm_sq_integral P (Y ⊤) (hY2.moment ⊤)
  have hb := mul_le_mul (Real.sqrt_le_sqrt hEX) (Real.sqrt_le_sqrt hEY)
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  rw [← hx,← hy,Real.sqrt_sq (norm_nonneg _),Real.sqrt_sq (norm_nonneg _)] at hb
  exact hb

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.m2_covariance_fixed_time_L1_bound
