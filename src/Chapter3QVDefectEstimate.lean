import Chapter3StoppedIncrement

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter3Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false

/-- Apply the terminal norm estimate to the actual deterministically stopped
bounded martingale, and identify its QV by uniqueness. Thus the estimate is
valid at every time, including the terminal endpoint. -/
theorem bounded_qv_defect_bound_at_time
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (X : boundedMProcess P F) (t : ClosedTime T) :
    eLpNorm (fun ω => X.val t ω^2-boundedQV P F hF hle hnull X t ω) 2 P ≤
      ENNReal.ofReal (2*(eLpNorm (X.val t) ∞ P).toReal*
        Real.sqrt (∫ ω, X.val t ω^2 ∂P)) := by
  have ht : ∀ s, MeasurableSet[F s] {ω : Ω | t ≤ s} := by
    intro s
    by_cases h : t ≤ s <;> simp [h]
  let Y := stopBounded P F hF hle X (fun _ => t) ht
  let Q := boundedQV P F hF hle hnull X
  have hQ := boundedQV_properties P F hF hle hnull X
  have hYQ := boundedQV_properties P F hF hle hnull Y
  have hD := continuous_m2_stopped P F hF hle
    (fun s ω => X.val s ω^2-Q s ω) hQ.2.2.2 (fun _ => t) ht
  have he := qv_uniqueness_written P F hF hle Y.val
    (boundedQV P F hF hle hnull Y) (fun s ω => Q (min t s) ω)
    hYQ.2.2.1 (fun ω => (hQ.2.2.1 ω).comp (monotone_const.min monotone_id))
    hYQ.2.2.2 hD
  have hbound := bounded_qv_defect_terminal_bound P F hF hle hnull Y
  have he' : (fun ω => Y.val ⊤ ω^2-boundedQV P F hF hle hnull Y ⊤ ω) =ᵐ[P]
      (fun ω => X.val t ω^2-Q t ω) := by
    filter_upwards [he] with ω hω
    rw [hω ⊤]
    simp only [Y,stopBounded,min_top_right]
  rw [eLpNorm_congr_ae he'] at hbound
  simpa only [Y,stopBounded,min_top_right] using hbound

/-- The oscillation-partition constant in lem:adiff is 2 times its amplitude.
This statement uses a real square-root energy, equivalent to the L2 norm. -/
theorem bounded_qv_defect_amplitude_bound
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (X : boundedMProcess P F) (t : ClosedTime T)
    (δ : ℝ) (hδ : 0 ≤ δ) (hb : ∀ᵐ ω ∂P, ‖X.val t ω‖ ≤ δ) :
    eLpNorm (fun ω => X.val t ω^2-boundedQV P F hF hle hnull X t ω) 2 P ≤
      ENNReal.ofReal (2*δ*Real.sqrt (∫ ω, X.val t ω^2 ∂P)) := by
  apply (bounded_qv_defect_bound_at_time P F hF hle hnull X t).trans
  apply ENNReal.ofReal_le_ofReal
  apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 2)
  have hn : eLpNorm (X.val t) ∞ P ≤ ENNReal.ofReal δ :=
    by
      rw [eLpNorm_exponent_top (X.property.2 t).aestronglyMeasurable]
      exact eLpNormEssSup_le_of_ae_bound hb
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hn).trans_eq (ENNReal.toReal_ofReal hδ)

end Asakura.Chapter3Complete
#print axioms Asakura.Chapter3Complete.bounded_qv_defect_bound_at_time
#print axioms Asakura.Chapter3Complete.bounded_qv_defect_amplitude_bound
