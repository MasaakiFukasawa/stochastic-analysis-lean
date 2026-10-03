import Chapter3AbsolutePowerItoMoment
import Chapter3DoobPowerMoment
import Chapter3MomentCancellation

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter3Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

/-- The complete p>2 upper BDG argument at the bounded stage. -/
theorem bdg_upper_large_p_bounded
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (X A : ClosedTime T → Ω → ℝ)
    (hX : LocalMProcessWitness P F X) (hA : LocalCovarianceWitness P F X X A)
    (hAm : ∀ ω, MonotoneOn (fun t => A t ω) (Iio ⊤))
    (hAc : ∀ ω t, t < ⊤ → ContinuousAt (fun s => A s ω) t)
    (hA0 : ∀ ω, A ⊥ ω = 0)
    (p : ℝ) (hp : 2 < p)
    (b : ClosedTime T) (hb : b < ⊤) (K : ℝ) (hK : 0 ≤ K)
    (hbound : ∀ᵐ ω ∂P, A b ω ≤ K)
    (L : ℝ) (hL : 0 ≤ L)
    (hXbound : ∀ᵐ ω ∂P, ∀ s, s ≤ b → |X s ω| ≤ L) :
    ∃ hx : ∀ ω, Continuous (fun t => X (min b t) ω),
      Integrable (fun ω => ‖continuousPath (fun t ω => X (min b t) ω) hx ω‖^p) P ∧
      (∫ ω, ‖continuousPath (fun t ω => X (min b t) ω) hx ω‖^p ∂P) ≤
        ((p/(p-1))^p*(p*(p-1)/2))^(p/2)*(∫ ω, A b ω^(p/2) ∂P) := by
  have hp0 : 0 < p := by linarith
  have hp1 : 0 < p-1 := by linarith
  obtain ⟨hx,hSi,hXi,hito⟩ := absolute_power_ito_moment_bound P hT F hF hle hnull X A hX hA hAm hAc hA0
    p hp b hb K hK hbound L hL hXbound
  have hAp ω : 0 ≤ A b ω := by
    rw [← hA0 ω]
    exact hAm ω hT hb bot_le
  have hAi : Integrable (A b) P := by
    apply (integrable_const K).mono'
      ((hA.adapted P F hX hX b hb).mono (hle b) le_rfl).aestronglyMeasurable
    filter_upwards [hbound] with ω hω
    simpa only [Real.norm_eq_abs,abs_of_nonneg (hAp ω)] using hω
  have hstop t : MeasurableSet[F t] {ω : Ω | b ≤ t} := by
    by_cases h : b ≤ t <;> simp [h]
  have hM2 := (stopped_local_M2_equivalences P F hF hle hnull X A hX hA
    (fun _ => b) hstop (fun _ => hb)).2.mp
      ((stopped_local_M2_equivalences P F hF hle hnull X A hX hA
        (fun _ => b) hstop (fun _ => hb)).1.mp hAi)
  have hd := continuous_m2_path_power_moment P F hF hle _ hM2 p (by linarith) hSi
    (by simpa only [min_top_right] using hXi)
  simp only [min_top_right] at hd
  let N := ∫ ω, ‖continuousPath (fun t ω => X (min b t) ω) hx ω‖^p ∂P
  let M := ∫ ω, A b ω^(p/2) ∂P
  have hNp : 0 ≤ N := integral_nonneg (fun ω => Real.rpow_nonneg (norm_nonneg _) _)
  have hMp : 0 ≤ M := integral_nonneg (fun ω => Real.rpow_nonneg (hAp ω) _)
  have hC : 0 ≤ (p/(p-1))^p*(p*(p-1)/2) := by positivity
  have he : (p-2)/p = 1-2/p := by field_simp <;> ring
  have hineq : N ≤ ((p/(p-1))^p*(p*(p-1)/2))*M^(2/p)*N^(1-2/p) := by
    have h := hd.trans (mul_le_mul_of_nonneg_left hito
      (Real.rpow_nonneg (by positivity : 0 ≤ p/(p-1)) p))
    change N ≤ (p/(p-1))^p*((p*(p-1)/2)*N^((p-2)/p)*M^(2/p)) at h
    rw [he] at h
    nlinarith [h]
  have ha : 0 < 2/p := by positivity
  have ha1 : 2/p < 1 := (div_lt_one hp0).mpr hp
  have hcancel := fractional_moment_cancel hNp hMp hC ha ha1 hineq
  have he' : 1/(2/p) = p/2 := by field_simp
  rw [he'] at hcancel
  exact ⟨hx,hSi,hcancel⟩

end Asakura.Chapter3Complete
#print axioms Asakura.Chapter3Complete.bdg_upper_large_p_bounded
