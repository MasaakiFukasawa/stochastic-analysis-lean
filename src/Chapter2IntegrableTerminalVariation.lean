import Chapter2M2IncrementEnergy
import Chapter2StoppedM2Equivalence
import Chapter2CovarianceContinuity

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

/-- An integrable terminal limit of the actual quadratic variation gives
an actual continuous M2 extension. The terminal value is constructed by
L2 completeness, never used as a pre-existing value of the local process. -/
theorem local_martingale_extension_of_integrable_variation_limit
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (X C : ClosedTime T → Ω → ℝ) (hX : LocalMProcessWitness P F X)
    (hC : LocalCovarianceWitness P F X X C)
    (u : ℕ → ClosedTime T) (hu : Monotone u) (hut : ∀ n, u n < ⊤)
    (huc : ∀ t, t < ⊤ → ∃ n, t ≤ u n)
    (CT : Ω → ℝ) (hi : Integrable CT P)
    (hb : ∀ n, ∀ᵐ ω ∂P, C (u n) ω ≤ CT ω)
    (hc : ∀ᵐ ω ∂P, Tendsto (fun n => C (u n) ω) atTop (𝓝 (CT ω))) :
    ∃ Y : ClosedTime T → Ω → ℝ, ∃ hY : ContinuousM2Witness P F Y,
      (∀ t, t < ⊤ → Y t =ᵐ[P] X t) ∧
      Tendsto (fun n => eLpNorm ((fun ω => X (u n) ω)-Y ⊤) 2 P) atTop (𝓝 0) ∧
      ‖(hY.moment ⊤).toLp (Y ⊤)‖^2 = ∫ ω, CT ω ∂P := by
  have hnon n : ∀ᵐ ω ∂P, 0 ≤ C (u n) ω := by
    filter_upwards [local_quadratic_variation_monotone P F hF hle hnull X C hX hC,
      local_quadratic_variation_initial P F X C hX hC] with ω hm h0
    have h := hm (show (⊥ : ClosedTime T) ∈ Iio ⊤ from bot_le.trans_lt (hut n)) (hut n) bot_le
    simpa only [h0,Pi.zero_apply] using h
  have hbound n : ∀ᵐ ω ∂P, ‖C (u n) ω‖ ≤ CT ω := by
    filter_upwards [hnon n,hb n] with ω hp hbω
    simpa only [Real.norm_eq_abs,abs_of_nonneg hp] using hbω
  have hmeas n : Measurable (C (u n)) := (hC.adapted P F hX hX _ (hut n)).mono (hle _) le_rfl
  have hCi n : Integrable (C (u n)) P := hi.mono' (hmeas n).aestronglyMeasurable (hbound n)
  have hstop n : ∀ t, MeasurableSet[F t] {ω : Ω | u n ≤ t} := by
    intro t
    by_cases ht : u n ≤ t <;> simp [ht]
  have hM n : ContinuousM2Witness P F (fun t ω => X (min (u n) t) ω) := by
    have he := stopped_local_M2_equivalences P F hF hle hnull X C hX hC
      (fun _ => u n) (hstop n) (fun _ => hut n)
    exact he.2.mp (he.1.mp (hCi n))
  have hsq n : (∫ ω, X (u n) ω^2 ∂P) = ∫ ω, C (u n) ω ∂P :=
    (stopped_M2_energy P F hF hle hnull X C hX hC (fun _ => u n) (hstop n) (fun _ => hut n) (hM n)).2
  have hlim := tendsto_integral_of_dominated_convergence CT
    (fun n => (hmeas n).aestronglyMeasurable) hi hbound hc
  apply terminal_extension_from_stopped_energy P F hF hle hnull X u hu hut huc hM
    (fun n => ∫ ω, C (u n) ω ∂P) (∫ ω, CT ω ∂P) hlim
  · intro n k
    have hn : MemLp (X (u n)) 2 P := by simpa only [min_top_right] using (hM n).moment ⊤
    have hk : MemLp (X (u k)) 2 P := by simpa only [min_top_right] using (hM k).moment ⊤
    simp only [min_top_right]
    change ‖hn.toLp (X (u n))-hk.toLp (X (u k))‖^2 ≤ _
    rw [← hn.toLp_sub hk,norm_toLp_square_integral]
    have hinc a b (hab : a ≤ b) :
        (∫ ω, (X (u b) ω-X (u a) ω)^2 ∂P) =
          (∫ ω, C (u b) ω ∂P)-(∫ ω, C (u a) ω ∂P) := by
      have h := continuous_martingale_increment_energy P F hle _ (hM b) (u a) (u b) (hu hab)
      simp only [min_self,min_eq_right (hu hab)] at h
      rw [hsq a,hsq b] at h
      exact h
    rcases le_total n k with hnk|hkn
    · have he := hinc n k hnk
      have hs : (∫ ω, ((X (u n)-X (u k)) ω)^2 ∂P) = ∫ ω, (X (u k) ω-X (u n) ω)^2 ∂P := by
        apply integral_congr_ae
        exact .of_forall (fun ω => by dsimp only [Pi.sub_apply]; ring)
      rw [hs,he,Real.dist_eq]
      simpa only [neg_sub] using neg_le_abs ((∫ ω, C (u n) ω ∂P)-(∫ ω, C (u k) ω ∂P))
    · change (∫ ω, (X (u n) ω-X (u k) ω)^2 ∂P) ≤ _
      rw [hinc k n hkn,Real.dist_eq]
      exact le_abs_self _
  · intro n
    rw [norm_toLp_square_integral]
    simpa only [min_top_right] using hsq n

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.local_martingale_extension_of_integrable_variation_limit
