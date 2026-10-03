import Chapter2LocalUniformLimit
import Chapter2LocalNullModification

open MeasureTheory Set Filter
open scoped Topology ENNReal Classical
namespace Asakura.Chapter2Complete
open Asakura.FullAudit Asakura.Chapter2Written
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

/-- Almost-sure local uniform convergence suffices: remove the same null
set from every term, preserve all local martingale witnesses, and apply the
pathwise local uniform limit theorem. No adaptedness of the limit is assumed. -/
theorem ae_locally_uniform_limit_local
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (X : ℕ → Ω → C(Iio (⊤ : ClosedTime T),ℝ))
    (Y : Ω → C(Iio (⊤ : ClosedTime T),ℝ))
    (hX : ∀ n, LocalMProcessWitness P F (fun t ω => extendOpenPath (X n ω) t))
    (N : Set Ω) (hN : MeasurableSet[m] N) (hNP : P N = 0)
    (hconv : ∀ ω, ω ∉ N → Tendsto (fun n => X n ω) atTop (𝓝 (Y ω))) :
    ∃ Z : Ω → C(Iio (⊤ : ClosedTime T),ℝ), Z =ᵐ[P] Y ∧
      LocalMProcessWitness P F (fun t ω => extendOpenPath (Z ω) t) := by
  let X' := fun n ω => if ω ∈ N then (0 : C(Iio (⊤ : ClosedTime T),ℝ)) else X n ω
  let Z := fun ω => if ω ∈ N then (0 : C(Iio (⊤ : ClosedTime T),ℝ)) else Y ω
  have hx' (n) : LocalMProcessWitness P F (fun t ω => extendOpenPath (X' n ω) t) := by
    have h := local_martingale_null_modification P F N (fun t => hnull t N hN hNP)
      hNP (fun t ω => extendOpenPath (X n ω) t) (hX n)
    have he : (fun t ω => extendOpenPath (X' n ω) t) =
        (fun t ω => if ω ∈ N then 0 else extendOpenPath (X n ω) t) := by
      funext t ω
      by_cases hω : ω ∈ N
      · simp only [X',ite_eq_left hω,extendOpenPath,ContinuousMap.zero_apply]
        split_ifs <;> rfl
      · simp only [X',ite_eq_right hω]
    rw [he]
    exact h
  have hc (ω) : Tendsto (fun n => X' n ω) atTop (𝓝 (Z ω)) := by
    by_cases hω : ω ∈ N
    · simpa only [X',Z,ite_eq_left hω] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0:C(Iio (⊤ : ClosedTime T),ℝ))) atTop (𝓝 0))
    · simpa only [X',Z,ite_eq_right hω] using hconv ω hω
  refine ⟨Z,?_,pathwise_locally_uniform_limit_local P hT F hF hle X' Z hx' hc⟩
  have hn : ∀ᵐ ω ∂P, ω ∉ N := by rw [ae_iff]; simpa using hNP
  exact hn.mono fun ω hω => by simp only [Z,ite_eq_right hω]

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.ae_locally_uniform_limit_local
