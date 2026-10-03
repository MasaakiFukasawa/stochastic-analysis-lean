import Chapter2ProgressiveSpace
import FullAuditBoundedKW

open MeasureTheory Set Filter
open scoped Topology ENNReal Classical
namespace Asakura.Chapter2Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

/-- A single completed sample-null set handles all finite horizons.
Progressive measurability is preserved, so finite-interval constructions
may use everywhere-integrable paths without strengthening the hypothesis. -/
theorem local_integrable_progressive_representative
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω)
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (c : ℕ → ℝ) (κ : ℕ → Ω → Measure ℝ) (H : Ω × ℝ → ℝ)
    (hH : ∀ n, @Measurable _ _
      (progressiveSpace (fun t : Icc (0:ℝ) (c n) => F (realTimeClamp t.val))) inferInstance
      (fun z : Ω × Icc (0:ℝ) (c n) => H (z.1,z.2.val)))
    (hi : ∀ n, ∀ᵐ ω ∂P, Integrable (fun r => H (ω,r)) (κ n ω)) :
    ∃ J : Ω × ℝ → ℝ,
      (∀ n, @Measurable _ _
        (progressiveSpace (fun t : Icc (0:ℝ) (c n) => F (realTimeClamp t.val))) inferInstance
        (fun z : Ω × Icc (0:ℝ) (c n) => J (z.1,z.2.val))) ∧
      (∀ n ω, Integrable (fun r => J (ω,r)) (κ n ω)) ∧
      (∀ᵐ ω ∂P, ∀ r, J (ω,r) = H (ω,r)) := by
  classical
  let bad := {ω | ¬ ∀ n, Integrable (fun r => H (ω,r)) (κ n ω)}
  let N := toMeasurable P bad
  have hNz : P N = 0 := by
    rw [measure_toMeasurable]
    exact ae_iff.mp (ae_all_iff.mpr hi)
  have hNF t := hnull t N (measurableSet_toMeasurable _ _) hNz
  let J := fun z : Ω × ℝ => if z.1 ∈ N then 0 else H z
  refine ⟨J,?_,?_,?_⟩
  · intro n
    apply (measurable_progressive_iff _ _).mpr
    intro t
    exact Measurable.ite ((hNF (realTimeClamp t.val)).preimage measurable_fst) measurable_const
      ((measurable_progressive_iff _ _).mp (hH n) t)
  · intro n ω
    by_cases hω : ω ∈ N
    · simp only [J,if_pos hω]
      refine ⟨aestronglyMeasurable_const,?_⟩
      simp [hasFiniteIntegral_iff_norm]
    · have hg : ∀ n, Integrable (fun r => H (ω,r)) (κ n ω) := by
        by_contra hn
        exact hω (subset_toMeasurable P bad hn)
      simpa only [J,if_neg hω] using hg n
  · have hn : ∀ᵐ ω ∂P, ω ∉ N := by
      rw [ae_iff]
      simpa only [not_not,setOf_mem_eq] using hNz
    exact hn.mono (fun ω hω r => if_neg hω)

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.local_integrable_progressive_representative
