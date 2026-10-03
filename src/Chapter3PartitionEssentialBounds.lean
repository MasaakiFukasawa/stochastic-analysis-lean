import Chapter3DenseEssentialBound

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter3Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

/-- The literal L-infinity partition condition on the dense set Lambda
implies one common all-time stopped-increment bound. -/
theorem stopped_dense_essential_bound
    {Ω ι : Type*} [MeasurableSpace Ω] [Countable ι] (P : Measure Ω)
    {T : EReal} [Fact (0 ≤ T)]
    (q : ι → Iio (⊤ : ClosedTime T)) (hq : DenseRange q)
    (H : ClosedTime T → Ω → ℝ)
    (hc : ∀ ω t, t < ⊤ → ContinuousAt (fun s => H s ω) t)
    (σ τ : Ω → ClosedTime T) (hστ : ∀ ω, σ ω ≤ τ ω) (hτt : ∀ ω, τ ω < ⊤)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hb : ∀ i, eLpNorm (fun ω => H (min (τ ω) (q i).val) ω-H (min (σ ω) (q i).val) ω) ∞ P ≤ ENNReal.ofReal δ) :
    ∀ᵐ ω ∂P, ∀ t, ‖H (min (τ ω) t) ω-H (min (σ ω) t) ω‖ ≤ δ := by
  let D := fun t ω => H (min (τ ω) t) ω-H (min (σ ω) t) ω
  have hDc ω : Continuous (fun t => D t ω) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact ((hc ω _ ((min_le_left _ _).trans_lt (hτt ω))).comp
      (continuous_const.min continuous_id).continuousAt).sub
      ((hc ω _ ((min_le_left _ _).trans_lt ((hστ ω).trans_lt (hτt ω)))).comp
        (continuous_const.min continuous_id).continuousAt)
  have he := dense_essential_bound_common_path P q hq
    (fun t : Iio (⊤ : ClosedTime T) => D t.val)
    (fun ω => (hDc ω).comp continuous_subtype_val) δ hδ hb
  filter_upwards [he] with ω hω
  intro t
  have h := hω ⟨min (τ ω) t,(min_le_left _ _).trans_lt (hτt ω)⟩
  simpa only [D,← min_assoc,min_self,min_eq_left (hστ ω)] using h

/-- Stopped-increment control also gives the interval oscillation needed
by the deterministic Stieltjes approximation, on a common null set. -/
theorem stopped_bound_interval_oscillation
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {T : EReal} [Fact (0 ≤ T)] (H : ClosedTime T → Ω → ℝ)
    (τ : ℕ → ℕ → Ω → ClosedTime T) (δ : ℕ → ℝ)
    (hb : ∀ n j, ∀ᵐ ω ∂P, ∀ t,
      ‖H (min (τ n (j+1) ω) t) ω-H (min (τ n j ω) t) ω‖ ≤ δ n) :
    ∀ᵐ ω ∂P, ∀ n j t, τ n j ω ≤ t → t ≤ τ n (j+1) ω →
      |H (τ n j ω) ω-H t ω| ≤ δ n := by
  filter_upwards [ae_all_iff.mpr (fun n => ae_all_iff.mpr (hb n))] with ω hω
  intro n j t ht hu
  have h := hω n j t
  simpa only [min_eq_left ht,min_eq_right hu,Real.norm_eq_abs,abs_sub_comm] using h

end Asakura.Chapter3Complete
#print axioms Asakura.Chapter3Complete.stopped_dense_essential_bound
#print axioms Asakura.Chapter3Complete.stopped_bound_interval_oscillation
