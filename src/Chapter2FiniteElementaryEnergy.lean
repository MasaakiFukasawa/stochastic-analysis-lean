import Chapter2RealElementaryEnergy
import Chapter2AdaptedStepRefinement
import Chapter2StepIndependence

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

/-- The elementary energy identity for arbitrary finite representations,
including overlapping holding intervals. The common grid and its adapted
bounded coefficients are constructed explicitly. -/
theorem finite_elementary_stieltjes_energy
    {Ω ι : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t E, MeasurableSet[m] E → P E = 0 → MeasurableSet[F t] E)
    (X A : ClosedTime T → Ω → ℝ) (hX : LocalMProcessWitness P F X)
    (hA : LocalCovarianceWitness P F X X A)
    (c : ℝ) (hc : 0 ≤ c) (hcT : (c:EReal) < T)
    (hAm : ∀ ω, MonotoneOn (fun r => A (realTimeClamp r) ω) (Icc 0 c))
    (s : Finset ι) (a b : ι → ℝ) (G : ι → Ω → ℝ)
    (hab : ∀ i ∈ s, a i ≤ b i)
    (ha : ∀ i ∈ s, a i ∈ Icc 0 c) (hb : ∀ i ∈ s, b i ∈ Icc 0 c)
    (hGm : ∀ i ∈ s, Measurable[F (realTimeClamp (a i))] (G i))
    (hG : ∀ i ∈ s, MemLp (G i) ∞ P) :
    let Z := fun t ω => ∑ i ∈ s, G i ω*
      stepIncrement (realTimeClamp (a i)) (realTimeClamp (b i)) (fun t => X t ω) t
    LocalMProcessWitness P F Z ∧ ∃ Q, LocalCovarianceWitness P F Z Z Q ∧
      ∀ᵐ ω ∂P, ∀ t, t ∈ Icc 0 c →
        ∃ hr : ∀ r ∈ Icc 0 c, ContinuousWithinAt (fun v => A (realTimeClamp v) ω) (Icc 0 c ∩ Ici r) r,
        Q (realTimeClamp t) ω =
          ∫ r in Iic t, (∑ i ∈ s, (Ico (a i) (b i)).indicator (fun _ => G i ω) r)^2
            ∂(intervalStieltjes 0 c hc (fun v => A (realTimeClamp v) ω) (hAm ω) hr).measure := by
  classical
  intro Z
  obtain ⟨N,u,V,hu,humem,hVm,he⟩ := finite_adapted_step_refinement P
    (fun r => F (realTimeClamp r)) (hF.comp real_time_clamp_mono) (fun r => hle _) s a b G hab hGm hG 0
  have huab (j : ℕ) : u j ∈ Icc 0 c := by
    rcases Finset.mem_insert.1 (humem j) with he|h
    · rw [he]
      exact left_mem_Icc.2 hc
    · rcases Finset.mem_union.1 h with h|h
      · obtain ⟨i,hi,he⟩ := Finset.mem_image.1 h
        rw [← he]
        exact ha i hi
      · obtain ⟨i,hi,he⟩ := Finset.mem_image.1 h
        rw [← he]
        exact hb i hi
  have huinc (j : ℕ) (hj : j ∈ Finset.range N) : u j ≤ u (j+1) := by
    have hjn := Finset.mem_range.1 hj
    exact hu.monotoneOn hjn.le (show j+1 ∈ Iic N by change j+1 ≤ N; omega) (by omega)
  let W := fun t ω => ∑ j ∈ Finset.range N, V j ω*
    stepIncrement (realTimeClamp (u j)) (realTimeClamp (u (j+1))) (fun t => X t ω) t
  have hZW : Z = W := by
    funext t ω
    have h := elementary_integral_representation_independent s (Finset.range N) a b u (fun j => u (j+1))
      hab huinc (fun i => G i ω) (fun j => V j ω) (he ω) (fun r => X (min (realTimeClamp r) t) ω) c
    have hl : (∑ i ∈ s, G i ω *
        (X (min (realTimeClamp (min (b i) c)) t) ω-X (min (realTimeClamp (min (a i) c)) t) ω)) = Z t ω := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [min_eq_left (hb i hi).2,min_eq_left (ha i hi).2]
      rfl
    have hr : (∑ j ∈ Finset.range N, V j ω *
        (X (min (realTimeClamp (min (u (j+1)) c)) t) ω-X (min (realTimeClamp (min (u j) c)) t) ω)) = W t ω := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [min_eq_left (huab (j+1)).2,min_eq_left (huab j).2]
      rfl
    exact hl.symm.trans (h.trans hr)
  obtain ⟨hW,Q,hQ,hQi⟩ := real_elementary_grid_energy P F hF hle hnull X A hX hA c hc hcT hAm
    N u hu (fun j _ => huab j) V (fun j hj => (hVm j hj).1) (fun j hj => (hVm j hj).2)
  change LocalMProcessWitness P F W at hW
  change LocalCovarianceWitness P F W W Q at hQ
  rw [← hZW] at hW hQ
  refine ⟨hW,Q,hQ,?_⟩
  filter_upwards [hQi] with ω hω
  intro t ht
  obtain ⟨hr,heq⟩ := hω t ht
  refine ⟨hr,?_⟩
  rw [heq]
  apply integral_congr_ae
  exact .of_forall (fun r => congrArg (fun z : ℝ => z^2) (he ω r).symm)

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.finite_elementary_stieltjes_energy
