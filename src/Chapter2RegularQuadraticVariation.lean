import Chapter2LocalQuadraticVariation
import Chapter2LocalNullModification

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

/-- The monotone continuous representatives required for Stieltjes measures
are constructed from the local-martingale assumptions. No pathwise
monotonicity premise is added to the manuscript. -/
theorem regular_quadratic_variation_representatives
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (X : ClosedTime T → Ω → ℝ) (hX : LocalMProcessWitness P F X) :
    ∃ X' A : ClosedTime T → Ω → ℝ,
      LocalMProcessWitness P F X' ∧ LocalCovarianceWitness P F X' X' A ∧
      (∀ᵐ ω ∂P, ∀ t, X' t ω = X t ω) ∧
      (∀ ω, MonotoneOn (fun t => A t ω) (Iio ⊤)) ∧
      (∀ ω t, t < ⊤ → ContinuousAt (fun s => A s ω) t) ∧
      (∀ ω, X' ⊥ ω = 0 ∧ A ⊥ ω = 0) := by
  classical
  obtain ⟨C,hC⟩ := local_covariance_witness_exists P F hF hle hnull X X hX hX
  have hgood : ∀ᵐ ω ∂P, MonotoneOn (fun t => C t ω) (Iio ⊤) ∧ X ⊥ ω = 0 ∧ C ⊥ ω = 0 := by
    filter_upwards [local_quadratic_variation_monotone P F hF hle hnull X C hX hC,
      hX.initial P F,local_quadratic_variation_initial P F X C hX hC] with ω hm hx hc
    exact ⟨hm,hx,hc⟩
  let B := {ω | ¬(MonotoneOn (fun t => C t ω) (Iio ⊤) ∧ X ⊥ ω = 0 ∧ C ⊥ ω = 0)}
  have hB : P B = 0 := by simpa only [ae_iff,B] using hgood
  let N := toMeasurable P B
  have hN : P N = 0 := by rw [measure_toMeasurable,hB]
  have hNm t : MeasurableSet[F t] N := hnull t N (measurableSet_toMeasurable P B) hN
  have hn : ∀ᵐ ω ∂P, ω ∉ N := by simpa only [ae_iff,not_not,Set.setOf_mem_eq] using hN
  let X' := fun t ω => if ω ∈ N then 0 else X t ω
  let A := fun t ω => if ω ∈ N then 0 else C t ω
  have hx' : LocalMProcessWitness P F X' := local_martingale_null_modification P F N hNm hN X hX
  have hvar : LocalVariationWitness F A := by
    obtain ⟨τ,ht,hm,htt,hc,hd⟩ := hC.variation.localizers
    refine ⟨τ,ht,hm,htt,hc,?_⟩
    intro n ω
    by_cases hω : ω ∈ N
    · exact ⟨fun _ => 0,fun _ => 0,monotone_const,monotone_const,fun t => by simp [A,hω]⟩
    · simpa only [A,if_neg hω] using hd n ω
  have hcov : LocalCovarianceWitness P F X' X' A := by
    refine ⟨?_,hvar⟩
    have hh := local_martingale_null_modification P F N hNm hN _ hC.defect
    convert hh using 1
    funext t ω
    by_cases hω : ω ∈ N <;> simp [X',A,hω]
  refine ⟨X',A,hx',hcov,hn.mono (fun ω hω t => if_neg hω),?_,?_,?_⟩
  · intro ω
    by_cases hω : ω ∈ N
    · simpa only [A,if_pos hω] using (monotoneOn_const : MonotoneOn (fun _ : ClosedTime T => (0:ℝ)) (Iio ⊤))
    · have hb : ω ∉ B := fun h => hω (subset_toMeasurable P B h)
      exact (by simpa only [A,if_neg hω] using (not_not.mp hb).1)
  · intro ω t ht
    have hh := ((hx'.path P F ω t ht).mul (hx'.path P F ω t ht)).sub (hcov.defect.path P F ω t ht)
    convert hh using 1
    funext s
    dsimp only [Pi.sub_apply,Pi.mul_apply]
    ring
  · intro ω
    by_cases hω : ω ∈ N
    · simp [X',A,hω]
    · have hb : ω ∉ B := fun h => hω (subset_toMeasurable P B h)
      simpa only [X',A,if_neg hω] using (not_not.mp hb).2

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.regular_quadratic_variation_representatives
