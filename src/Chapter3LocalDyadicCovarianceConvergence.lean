import Chapter3StoppedLocalEnergyMaximal

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter3Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

/-- Localization removes every expectation bound on the dominating
quadratic variation. The same stopping sequence works for all errors. -/
theorem local_dyadic_covariance_ae_uniform
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (X A : ClosedTime T → Ω → ℝ) (hX : LocalMProcessWitness P F X)
    (hA : LocalCovarianceWitness P F X X A)
    (E B : ℕ → ClosedTime T → Ω → ℝ) (hE : ∀ n, LocalMProcessWitness P F (E n))
    (hB : ∀ n, LocalCovarianceWitness P F (E n) (E n) (B n))
    (hbound : ∀ n, ∀ᵐ ω ∂P, ∀ t, t < ⊤ →
      0 ≤ B n t ω ∧ B n t ω ≤ ((1/2:ℝ)^n)^2*A t ω)
    (b : ClosedTime T) (hb : b < ⊤) :
    ∃ hc : ∀ n ω, Continuous (fun t => E n (min b t) ω),
      ∀ᵐ ω ∂P, Tendsto (fun n => continuousPath (fun t ω => E n (min b t) ω) (hc n) ω) atTop (𝓝 0) := by
  obtain ⟨σ,hσ,hσm,hσt,hσc,hXS⟩ := hX.localizers
  have hbs : ∀ t, MeasurableSet[F t] {ω : Ω | b ≤ t} := by
    intro t
    by_cases ht : b ≤ t <;> simp [ht]
  let ρ := fun k ω => min (σ k ω) b
  have hρ k := (written_stopping_min_max F (σ k) (fun _ => b) (hσ k) hbs).1
  have hρt k ω : ρ k ω < ⊤ := (min_le_right _ _).trans_lt hb
  have hXρ k : ContinuousM2Witness P F (fun t ω => X (min (ρ k ω) t) ω) := by
    have h := continuous_m2_stopped P F hF hle _ (hXS k).1 (fun _ => b) hbs
    simpa only [ρ,min_assoc] using h
  have hV k : Integrable (fun ω => A (ρ k ω) ω) P :=
    (stopped_M2_energy P F hF hle hnull X A hX hA (ρ k) (hρ k) (hρt k) (hXρ k)).1
  have hconv k := stopped_local_dyadic_energy_ae_uniform P F hF hle hnull E B hE hB
    (ρ k) (hρ k) (hρt k) (fun ω => A (ρ k ω) ω) (hV k)
    (fun n => (hbound n).mono (fun ω hω => hω _ (hρt k ω)))
  choose hcρ hlim using hconv
  have hc n ω : Continuous (fun t => E n (min b t) ω) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact ((hE n).path P F ω _ ((min_le_left _ _).trans_lt hb)).comp
      (continuous_const.min continuous_id).continuousAt
  refine ⟨hc,?_⟩
  filter_upwards [ae_all_iff.mpr hlim] with ω hω
  obtain ⟨k,hk⟩ := hσc ω b hb
  have he n : continuousPath (fun t ω => E n (min b t) ω) (hc n) ω =
      continuousPath (fun t ω => E n (min (ρ k ω) t) ω) (hcρ k n) ω := by
    apply ContinuousMap.ext
    intro t
    change E n (min b t) ω = E n (min (min (σ k ω) b) t) ω
    rw [min_eq_right hk.le]
  simpa only [he] using hω k

end Asakura.Chapter3Complete
#print axioms Asakura.Chapter3Complete.local_dyadic_covariance_ae_uniform
