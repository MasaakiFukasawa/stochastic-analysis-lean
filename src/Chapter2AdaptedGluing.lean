import Chapter2LocalGluing
import FullAuditBoundedProcess

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
set_option maxHeartbeats 600000

/-- The stochastic gluing step: a single common null-set modification,
measurability at every time, continuity below T, and recovery of every
stopped piece. Completeness here is exactly condition con:filt. -/
theorem adapted_continuous_stopped_gluing
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω)
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (τ : ℕ → Ω → ClosedTime T)
    (hmono : ∀ ω, Monotone (fun n => τ n ω))
    (htop : ∀ n ω, τ n ω < ⊤)
    (hcofinal : ∀ ω t, t < ⊤ → ∃ n, t < τ n ω)
    (A : ℕ → ClosedTime T → Ω → ℝ)
    (hA : ∀ n t, Measurable[F t] (A n t))
    (hcont : ∀ n ω, Continuous (fun t => A n t ω))
    (hBV : ∀ n ω, ∃ U V : ClosedTime T → ℝ, Monotone U ∧ Monotone V ∧
      ∀ t, A n t ω = U t - V t)
    (hcompat : ∀ᵐ ω ∂P, ∀ n k, n ≤ k → ∀ t,
      A k (min (τ n ω) t) ω = A n t ω) :
    ∃ G : ClosedTime T → Ω → ℝ,
      (∀ t, t < ⊤ → Measurable[F t] (G t)) ∧
      (∀ ω t, t < ⊤ → ContinuousAt (fun s => G s ω) t) ∧
      (∀ᵐ ω ∂P, ∀ n t, G (min (τ n ω) t) ω = A n t ω) ∧
      (∀ᵐ ω ∂P, ∀ t, t < ⊤ → ∀ᶠ n in atTop, A n t ω = G t ω) ∧
      (∀ n t, Measurable[F t] (fun ω => G (min (τ n ω) t) ω)) ∧
      (∀ n ω, Continuous (fun t => G (min (τ n ω) t) ω)) ∧
      (∀ n ω, ∃ U V : ClosedTime T → ℝ, Monotone U ∧ Monotone V ∧
        ∀ t, G (min (τ n ω) t) ω = U t - V t) := by
  classical
  let bad := {ω | ¬ (∀ n k, n ≤ k → ∀ t, A k (min (τ n ω) t) ω = A n t ω)}
  let N := toMeasurable P bad
  have hNm : MeasurableSet[m] N := measurableSet_toMeasurable _ _
  have hNz : P N = 0 := by rw [measure_toMeasurable]; exact ae_iff.mp hcompat
  have hNF (t) := hnull t N hNm hNz
  have hnon : ∀ᵐ ω ∂P, ω ∉ N := by
    rw [ae_iff]
    simpa only [not_not, Set.setOf_mem_eq] using hNz
  let B := fun n t ω => if ω ∈ N then 0 else A n t ω
  have hBm (n t) : Measurable[F t] (B n t) :=
    Measurable.ite (hNF t) measurable_const (hA n t)
  have hBc (n ω) : Continuous (fun t => B n t ω) := by
    by_cases hω : ω ∈ N
    · simpa only [B, if_pos hω] using (continuous_const : Continuous (fun _ : ClosedTime T => (0:ℝ)))
    · simpa only [B, if_neg hω] using hcont n ω
  have hBcompat (ω n k) (hnk : n ≤ k) (t) :
      B k (min (τ n ω) t) ω = B n t ω := by
    by_cases hω : ω ∈ N
    · simp only [B, if_pos hω]
    · have hg : ∀ n k, n ≤ k → ∀ t, A k (min (τ n ω) t) ω = A n t ω := by
        by_contra hn
        exact hω (subset_toMeasurable P bad hn)
      simpa only [B, if_neg hω] using hg n k hnk t
  have hex (ω) := compatible_stops_glue (fun n => τ n ω) (hmono ω)
    (fun n => htop n ω) (fun t ht => (hcofinal ω t ht).imp fun n hn => hn.le)
    (fun n t => B n t ω) (hBcompat ω)
  choose G he hs using hex
  refine ⟨fun t ω => G ω t, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t ht
    exact @glued_value_measurable Ω (F t) (fun n ω => B n t ω)
      (fun n => hBm n t) (fun ω => G ω t) (fun ω => he ω t ht)
  · intro ω t ht
    exact glued_path_continuous_below_terminal (fun n => τ n ω) (hcofinal ω)
      (fun n t => B n t ω) (fun n => hBc n ω) (G ω) (hs ω) t ht
  · filter_upwards [hnon] with ω hω
    intro n t
    simpa only [B, if_neg hω] using hs ω n t
  · filter_upwards [hnon] with ω hω
    intro t ht
    simpa only [B, if_neg hω] using he ω t ht

  · intro n t
    have h : (fun ω => G ω (min (τ n ω) t)) = B n t := funext fun ω => hs ω n t
    rw [h]
    exact hBm n t
  · intro n ω
    have h : (fun t => G ω (min (τ n ω) t)) = (fun t => B n t ω) := funext (hs ω n)
    rw [h]
    exact hBc n ω
  · intro n ω
    by_cases hω : ω ∈ N
    · refine ⟨fun _ => 0, fun _ => 0, monotone_const, monotone_const, ?_⟩
      intro t
      simpa only [B, if_pos hω, sub_self] using hs ω n t
    · obtain ⟨U,V,hU,hV,hUV⟩ := hBV n ω
      refine ⟨U,V,hU,hV,?_⟩
      intro t
      simpa only [B, if_neg hω] using (hs ω n t).trans (by simpa only [B, if_neg hω] using hUV t)

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.adapted_continuous_stopped_gluing
