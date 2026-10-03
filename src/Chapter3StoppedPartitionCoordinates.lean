import Chapter3StieltjesUniformApproximation
import Chapter2FiniteTimeProjection

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter3Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

/-- The real coordinates of a stopping partition cut at a finite horizon
are increasing, start at zero, and actually reach that horizon. -/
theorem stopped_partition_real_coordinates
    {T : EReal} [Fact (0 ≤ T)] (d : ℝ) (hd : 0 ≤ d) (hdT : (d:EReal) < T)
    (τ : ℕ → ClosedTime T) (hτ : Monotone τ) (h0 : τ 0 = ⊥)
    (hcofinal : ∀ b, b < ⊤ → ∃ N, b < τ N) :
    let u := fun j => (finitePrefixTime d hd (τ j)).val
    Monotone u ∧ u 0 = 0 ∧ ∃ N, d ≤ u N := by
  intro u
  refine ⟨fun i j hij => finite_prefix_time_mono d hd (hτ hij),?_,?_⟩
  · dsimp only [u]
    rw [h0]
    change (min (0:EReal) (d:EReal)).toReal = 0
    rw [min_eq_left (by exact_mod_cast hd)]
    rfl
  · have hdt : realTimeClamp (T := T) d < ⊤ := by
      change (realTimeClamp d : EReal) < T
      rw [real_time_clamp_eq d hd hdT.le]
      exact hdT
    obtain ⟨N,hN⟩ := hcofinal (realTimeClamp d) hdt
    refine ⟨N,?_⟩
    have hNd : (d:EReal) ≤ (τ N:EReal) := by
      rw [← real_time_clamp_eq d hd hdT.le]
      exact hN.le
    change d ≤ (min (τ N:EReal) (d:EReal)).toReal
    rw [min_eq_right hNd,EReal.toReal_coe]

/-- Cutting stopping times at d preserves the oscillation condition. No
assumption about intervals past the final finite horizon is introduced. -/
theorem stopped_partition_oscillation_coordinates
    {T : EReal} [Fact (0 ≤ T)] (d : ℝ) (hd : 0 ≤ d) (hdT : (d:EReal) ≤ T)
    (τ : ℕ → ClosedTime T) (H : ClosedTime T → ℝ) (δ : ℝ)
    (hosc : ∀ j t, τ j ≤ t → t ≤ τ (j+1) → |H (τ j)-H t| ≤ δ) :
    let u := fun j => (finitePrefixTime d hd (τ j)).val
    ∀ j x, x ∈ Ioc (u j) (u (j+1)) →
      |H (realTimeClamp (u j))-H (realTimeClamp x)| ≤ δ := by
  intro u j x hx
  have huj : u j < d := hx.1.trans_le (hx.2.trans (finitePrefixTime d hd (τ (j+1))).property.2)
  have hjd : τ j < realTimeClamp d := by
    by_contra hn
    have hge : realTimeClamp d ≤ τ j := le_of_not_gt hn
    have hp := finite_prefix_time_clamp d hd hdT (τ j)
    rw [min_eq_left hge] at hp
    have hu0 := (finitePrefixTime d hd (τ j)).property.1
    have hud := (finitePrefixTime d hd (τ j)).property.2
    have he := congrArg (fun t : ClosedTime T => (t:EReal)) hp
    rw [real_time_clamp_eq _ hu0 ((EReal.coe_le_coe hud).trans hdT),
      real_time_clamp_eq d hd hdT] at he
    have he' : u j = d := EReal.coe_injective he
    exact (ne_of_lt huj) he'
  have hp : realTimeClamp (T := T) (u j) = τ j := by
    exact (finite_prefix_time_clamp d hd hdT (τ j)).trans (min_eq_right hjd.le)
  rw [hp]
  apply hosc
  · rw [← hp]
    exact real_time_clamp_mono hx.1.le
  · exact (real_time_clamp_mono hx.2).trans
      ((finite_prefix_time_clamp d hd hdT (τ (j+1))).le.trans (min_le_right _ _))

end Asakura.Chapter3Complete
#print axioms Asakura.Chapter3Complete.stopped_partition_real_coordinates
#print axioms Asakura.Chapter3Complete.stopped_partition_oscillation_coordinates
