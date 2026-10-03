import Chapter2FiniteElementaryEnergy
import Chapter2StieltjesRestriction

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

/-- Elementary energy on a fixed horizon, even when the elementary
strategy was originally specified on a different horizon. -/
theorem elementary_grid_local_energy
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t E, MeasurableSet[m] E → P E = 0 → MeasurableSet[F t] E)
    (X A : ClosedTime T → Ω → ℝ) (hX : LocalMProcessWitness P F X)
    (hA : LocalCovarianceWitness P F X X A)
    (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n) (hcm : Monotone c) (hcT : ∀ n, (c n:EReal) < T)
    (hAm : ∀ n ω, MonotoneOn (fun r => A (realTimeClamp r) ω) (Icc 0 (c n)))
    (hAc : ∀ n ω, ContinuousOn (fun r => A (realTimeClamp r) ω) (Icc 0 (c n)))
    (N : ℕ → ℕ) (u : ℕ → ℕ → ℝ) (V : ℕ → ℕ → Ω → ℝ)
    (hu : ∀ n, StrictMonoOn (u n) (Iic (N n)))
    (hub : ∀ n i, i ≤ N n → u n i ∈ Icc 0 (c n))
    (hVm : ∀ n i, i < N n → Measurable[F (realTimeClamp (u n i))] (V n i))
    (hVi : ∀ n i, i < N n → MemLp (V n i) ∞ P) (n j : ℕ) :
    let Z := fun t ω => ∑ i ∈ Finset.range (N n), V n i ω*
      stepIncrement (realTimeClamp (u n i)) (realTimeClamp (u n (i+1))) (fun t => X t ω) t
    LocalMProcessWitness P F Z ∧ ∃ Q, LocalCovarianceWitness P F Z Z Q ∧
      ∀ᵐ ω ∂P, Q (realTimeClamp (c j)) ω = ∫ r,
        (∑ i ∈ Finset.range (N n), (Ico (u n i) (u n (i+1))).indicator (fun _ => V n i ω) r)^2
          ∂(intervalStieltjes 0 (c j) (hc j) (fun r => A (realTimeClamp r) ω) (hAm j ω)
            (fun r hr => (hAc j ω r hr).mono inter_subset_left)).measure := by
  classical
  intro Z
  let l := max n j
  have hb i (hi : i ≤ N n) : u n i ∈ Icc 0 (c l) :=
    ⟨(hub n i hi).1,(hub n i hi).2.trans (hcm (le_max_left _ _))⟩
  have hi i (hir : i ∈ Finset.range (N n)) : u n i ≤ u n (i+1) := by
    have hin := Finset.mem_range.1 hir
    exact (hu n).monotoneOn hin.le (show i+1 ∈ Iic (N n) by change i+1 ≤ N n; omega) (by omega)
  obtain ⟨hZ,Q,hQ,hQi⟩ := finite_elementary_stieltjes_energy P F hF hle hnull X A hX hA
    (c l) (hc l) (hcT l) (hAm l) (Finset.range (N n)) (u n) (fun i => u n (i+1)) (V n)
    hi (fun i hir => hb i (Finset.mem_range.1 hir).le)
    (fun i hir => hb (i+1) (by have hh := Finset.mem_range.1 hir; omega))
    (fun i hir => hVm n i (Finset.mem_range.1 hir)) (fun i hir => hVi n i (Finset.mem_range.1 hir))
  refine ⟨hZ,Q,hQ,?_⟩
  filter_upwards [hQi] with ω hω
  obtain ⟨hr,he⟩ := hω (c j) ⟨hc j,hcm (le_max_right _ _)⟩
  rw [he]
  have hrest := interval_stieltjes_restrict_Iic 0 (c l) (c j) (hc j) (hcm (le_max_right _ _))
    (fun r => A (realTimeClamp r) ω) (hAm l ω) hr (hAm j ω)
      (fun r hr => (hAc j ω r hr).mono inter_subset_left)
  rw [← hrest]

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.elementary_grid_local_energy
