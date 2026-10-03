import Chapter2LocalProcess
import FullAuditMartingalePathNorm

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter5
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 1800000

/-- A continuous local martingale dominated by one integrable path bound
has zero terminal mean. The passage through the actual localizers is
proved by dominated convergence. -/
theorem dominated_local_terminal_mean
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)]
    (F : ClosedTime T → MeasurableSpace Ω) (hle : ∀ t,F t ≤ m)
    (X : ClosedTime T → Ω → ℝ) (hX : LocalMProcessWitness P F X)
    (hc : ∀ w,Continuous (fun t => X t w))
    (B : Ω → ℝ) (hB : Integrable B P)
    (hb : ∀ᵐ w ∂P,∀ t,‖X t w‖ ≤ B w) :
    (∫ w,X ⊤ w ∂P) = 0 := by
  obtain ⟨τ,_,hm,_,hco,hτ⟩ := hX.localizers
  have ht w : Tendsto (fun n => τ n w) atTop (𝓝 ⊤) := by
    apply tendsto_order.mpr
    constructor
    · intro a ha
      obtain ⟨n,hn⟩ := hco w a ha
      exact eventually_atTop.mpr ⟨n,fun k hk => hn.trans_le (hm w hk)⟩
    · intro a ha
      exact (not_lt_of_ge le_top ha).elim
  have hlim : Tendsto (fun n => ∫ w,X (τ n w) w ∂P) atTop (𝓝 (∫ w,X ⊤ w ∂P)) := by
    apply tendsto_integral_of_dominated_convergence B
    · intro n
      simpa only [min_top_right] using ((hτ n).1.moment ⊤).aestronglyMeasurable
    · exact hB
    · intro n
      exact hb.mono fun w hw => hw _
    · exact ae_of_all _ fun w => ((hc w).tendsto ⊤).comp (ht w)
  have hz n : (∫ w,X (τ n w) w ∂P) = 0 := by
    have hh := integral_congr_ae (((hτ n).1.martingale ⊥ ⊤ le_top).trans (hτ n).1.initial)
    rw [integral_condExp (hle ⊥)] at hh
    simpa only [min_top_right,Pi.zero_apply,integral_zero] using hh
  have hzero : Tendsto (fun n => ∫ w,X (τ n w) w ∂P) atTop (𝓝 0) := by
    simpa only [hz] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0:ℝ)) atTop (𝓝 0))
  exact tendsto_nhds_unique hlim hzero

/-- Distinct represented coordinates are orthogonal once their zero
covariance has made the product a local martingale. The required uniform
integrability comes from the proved L² maximal inequality. -/
theorem M2_product_local_orthogonal
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)]
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t ≤ m)
    (X Y : ClosedTime T → Ω → ℝ)
    (hX : ContinuousM2Witness P F X) (hY : ContinuousM2Witness P F Y)
    (hXY : LocalMProcessWitness P F (fun t w => X t w*Y t w)) :
    (∫ w,X ⊤ w*Y ⊤ w ∂P) = 0 := by
  have hx := continuous_martingale_path_memLp P F hF hle X hX.adapted hX.moment hX.path hX.martingale
  have hy := continuous_martingale_path_memLp P F hF hle Y hY.adapted hY.moment hY.path hY.martingale
  apply dominated_local_terminal_mean P F hle _ hXY
    (fun w => (hX.path w).mul (hY.path w))
    (fun w => ‖continuousPath X hX.path w‖*‖continuousPath Y hY.path w‖)
    (hx.norm.integrable_mul hy.norm)
  apply ae_of_all
  intro w t
  rw [norm_mul]
  exact mul_le_mul (ContinuousMap.norm_coe_le_norm (continuousPath X hX.path w) t) (ContinuousMap.norm_coe_le_norm (continuousPath Y hY.path w) t)
    (norm_nonneg _) (norm_nonneg _)

end Asakura.Chapter5
