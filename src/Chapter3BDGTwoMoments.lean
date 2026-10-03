import Chapter3DoobSquareMoment
import Chapter3RunningMaximum

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter3Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

theorem runningMaximum_eq_path_norm
    {Ω : Type*} {T : EReal} [Fact (0 ≤ T)]
    (X : ClosedTime T → Ω → ℝ)
    (hc : ∀ ω t, t < ⊤ → ContinuousAt (fun s => X s ω) t)
    (b : ClosedTime T) (hb : b < ⊤)
    (hx : ∀ ω, Continuous (fun t => X (min b t) ω)) (ω : Ω) :
    runningMaximum X hc b ω = ‖continuousPath (fun t ω => X (min b t) ω) hx ω‖ := by
  rw [runningMaximum_of_lt_top X hc b hb ω]
  rfl

/-- Both squared moment inequalities, with actual finite-time energy and Doob. -/
theorem bdg_two_moments
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (X A : ClosedTime T → Ω → ℝ) (hX : LocalMProcessWitness P F X)
    (hA : LocalCovarianceWitness P F X X A)
    (b : ClosedTime T) (hb : b < ⊤) (hAi : Integrable (A b) P) :
    Integrable (fun ω => runningMaximum X (hX.path P F) b ω^2) P ∧
    (∫ ω, A b ω ∂P) ≤ (∫ ω, runningMaximum X (hX.path P F) b ω^2 ∂P) ∧
    (∫ ω, runningMaximum X (hX.path P F) b ω^2 ∂P) ≤ 4*(∫ ω, A b ω ∂P) := by
  have hstop t : MeasurableSet[F t] {ω : Ω | b ≤ t} := by
    by_cases h : b ≤ t <;> simp [h]
  have hM2 := (stopped_local_M2_equivalences P F hF hle hnull X A hX hA
    (fun _ => b) hstop (fun _ => hb)).2.mp
      ((stopped_local_M2_equivalences P F hF hle hnull X A hX hA
        (fun _ => b) hstop (fun _ => hb)).1.mp hAi)
  have henergy := (stopped_M2_energy P F hF hle hnull X A hX hA
    (fun _ => b) hstop (fun _ => hb) hM2).2
  have hd := continuous_m2_path_square_moment P F hF hle _ hM2
  have he := runningMaximum_eq_path_norm X (hX.path P F) b hb hM2.path
  simp only [min_top_right,← he,henergy] at hd
  refine ⟨hd.1,?_,hd.2⟩
  rw [← henergy]
  have hXi : Integrable (fun ω => X b ω^2) P := by
    simpa only [min_top_right] using
      (memLp_two_iff_integrable_sq (hM2.moment ⊤).aestronglyMeasurable).mp (hM2.moment ⊤)
  apply integral_mono_ae hXi hd.1
  exact Filter.Eventually.of_forall (fun ω => by
    have h := (sq_le_sq₀ (abs_nonneg (X b ω)) (runningMaximum_nonneg X (hX.path P F) b ω)).mpr
      ((runningMaximum_bounds X (hX.path P F) b hb ω).1 b le_rfl)
    simpa only [sq_abs] using h)

end Asakura.Chapter3Complete
#print axioms Asakura.Chapter3Complete.runningMaximum_eq_path_norm
#print axioms Asakura.Chapter3Complete.bdg_two_moments
