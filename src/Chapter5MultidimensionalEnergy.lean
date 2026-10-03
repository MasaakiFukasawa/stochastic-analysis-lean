import Chapter5InfiniteBrownianIntegral
import Chapter5ItoOrthogonality
import Chapter3OrthogonalSum

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter5
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4
set_option maxHeartbeats 3600000
set_option backward.isDefEq.respectTransparency false

/-- Construct the coordinate integrals and derive the sum of energies.
This supplies the multi-dimensional isometry behind the manuscript's
claim that every coordinate integrand is Cauchy. -/
theorem multidimensional_brownian_integral_energy
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t E, MeasurableSet[m] E → P E = 0 → MeasurableSet[F t] E)
    (d : ℕ) (W : Fin d → ClosedTime T → Ω → ℝ) (A : ClosedTime T → Ω → ℝ)
    (hW : ∀ i,LocalMProcessWitness P F (W i))
    (hA : ∀ i,LocalCovarianceWitness P F (W i) (W i) A)
    (hcross : ∀ i j,i ≠ j → LocalCovarianceWitness P F (W i) (W j) (fun _ _ => 0))
    (c : ℕ → ℝ) (hc : ∀ n, 0 < c n) (hcm : StrictMono c) (hcT : ∀ n, (c n:EReal) < T)
    (hct : StrictMono (fun n => realTimeClamp (T := T) (c n)))
    (hcut : ∀ n, realTimeClamp (T := T) (c n) < ⊤)
    (hcc : ∀ t, t < ⊤ → ∃ n, t < realTimeClamp (T := T) (c n))
    (hclock : ∀ n w r, r ∈ Icc 0 (c n) → A (realTimeClamp r) w = r)
    (H : Fin d → Ω × ℝ → ℝ) (hHm : ∀ i,Measurable (H i))
    (hH : ∀ i n,@Measurable _ _ (progressiveSpace (fun t : Icc (0:ℝ) (c n) => F (realTimeClamp t.val))) inferInstance
      (fun z : Ω × Icc (0:ℝ) (c n) => H i (z.1,z.2.val)))
    (hco : ∀ r,∃ n,r ≤ c n)
    (hL2 : ∀ i,MemLp (H i) 2 (P.prod (volume.restrict (Ioi 0)))) :
    ∃ M : Fin d → ClosedTime T → Ω → ℝ,
      (∀ i,ContinuousM2Witness P F (M i)) ∧
      (∀ i,ItoCovarianceFormula P F (W i) (H i) (M i)) ∧
      ContinuousM2Witness P F (fun t w => ∑ i,M i t w) ∧
      (∫ w,(∑ i,M i ⊤ w)^2 ∂P) = ∑ i,∫ w,(∫ r in Ioi 0,(H i (w,r))^2) ∂P := by
  classical
  choose M hM hMl hI hiso hlim using fun i => brownian_infinite_terminal_integral
    P hT F hF hle hnull (W i) A (hW i) (hA i)
    c hc hcm hcT hct hcut hcc hclock (H i) (hHm i) (hH i) hco (hL2 i)
  have ho i j (hij : i ≠ j) : (∫ w,M i ⊤ w*M j ⊤ w ∂P) = 0 :=
    ito_integrals_terminal_orthogonal P hT F hF hle (W i) (W j) (M i) (M j)
      (hW i) (hW j) (hM i) (hM j) (hcross i j hij) (H i) (H j)
      (fun _ => (hHm i).comp measurable_prodMk_left) (fun _ => (hHm j).comp measurable_prodMk_left) (hI i) (hI j)
  refine ⟨M,hM,hI,finite_sum_m2 P F Finset.univ M (fun i _ => hM i),?_⟩
  rw [orthogonal_sum_energy P Finset.univ (fun i => M i ⊤)
    (fun i _ => (hM i).moment ⊤) (fun i _ j _ hij => ho i j hij)]
  apply Finset.sum_congr rfl
  intro i _
  rw [← norm_toLp_square_integral P _ ((hM i).moment ⊤)]
  exact hiso i

end Asakura.Chapter5
