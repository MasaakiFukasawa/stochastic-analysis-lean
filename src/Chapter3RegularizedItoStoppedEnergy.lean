import Chapter3RegularizedItoEnergy
import Chapter3BDGTwo

open MeasureTheory Set Filter
open scoped Topology ENNReal Classical
namespace Asakura.Chapter3Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

/-- In the bounded-bracket stage of BDG, the actual regularized integral
is an M₂ martingale and has precisely the expected energy in the manuscript. -/
theorem regularized_ito_stopped_energy
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (X A Y : ClosedTime T → Ω → ℝ)
    (hX : LocalMProcessWitness P F X) (hA : LocalCovarianceWitness P F X X A)
    (hAm : ∀ ω, MonotoneOn (fun t => A t ω) (Iio ⊤))
    (hAc : ∀ ω t, t < ⊤ → ContinuousAt (fun s => A s ω) t)
    (hA0 : ∀ ω, A ⊥ ω = 0)
    (ε p : ℝ) (hε : 0 < ε) (hp : 0 < p)
    (hY : LocalMProcessWitness P F Y)
    (hYI : ItoCovarianceFormula P F X
      (fun z => (ε+A (realTimeClamp z.2) z.1)^((p-2)/4)) Y)
    (b : ClosedTime T) (hb : b < ⊤) (K : ℝ) (hK : 0 ≤ K)
    (hbound : ∀ᵐ ω ∂P, A b ω ≤ K) :
    ContinuousM2Witness P F (fun t ω => Y (min b t) ω) ∧
      (∫ ω, Y b ω^2 ∂P) = (2/p)*(∫ ω, (ε+A b ω)^(p/2)-ε^(p/2) ∂P) := by
  obtain ⟨B,hB,he⟩ := regularized_ito_energy P hT F hF hle hnull X A Y hX hA hAm hAc hA0 ε p hε hp hY hYI
  have hAp ω : 0 ≤ A b ω := by
    rw [← hA0 ω]
    exact hAm ω hT hb bot_le
  have hcoeff : 0 ≤ 2/p := by positivity
  have hR : ∀ᵐ ω ∂P, 0 ≤ B b ω ∧ B b ω ≤ (2/p)*(ε+K)^(p/2) := by
    filter_upwards [he,hbound] with ω heω hbω
    rw [heω b hb]
    have hlow : ε^(p/2) ≤ (ε+A b ω)^(p/2) :=
      Real.rpow_le_rpow hε.le (by linarith [hAp ω]) (by positivity)
    have hupp : (ε+A b ω)^(p/2) ≤ (ε+K)^(p/2) :=
      Real.rpow_le_rpow (by linarith [hAp ω]) (by linarith) (by positivity)
    constructor
    · exact mul_nonneg hcoeff (sub_nonneg.mpr hlow)
    · apply mul_le_mul_of_nonneg_left _ hcoeff
      linarith [Real.rpow_nonneg hε.le (p/2)]
  have hBi : Integrable (B b) P := by
    apply (integrable_const ((2/p)*(ε+K)^(p/2))).mono'
      ((hB.adapted P F hY hY b hb).mono (hle b) le_rfl).aestronglyMeasurable
    filter_upwards [hR] with ω hω
    simpa only [Real.norm_eq_abs,abs_of_nonneg hω.1] using hω.2
  have hstop t : MeasurableSet[F t] {ω : Ω | b ≤ t} := by
    by_cases h : b ≤ t <;> simp [h]
  have hm := (stopped_local_M2_equivalences P F hF hle hnull Y B hY hB
    (fun _ => b) hstop (fun _ => hb)).2.mp
      ((stopped_local_M2_equivalences P F hF hle hnull Y B hY hB
        (fun _ => b) hstop (fun _ => hb)).1.mp hBi)
  refine ⟨hm,?_⟩
  have henergy := (stopped_M2_energy P F hF hle hnull Y B hY hB
    (fun _ => b) hstop (fun _ => hb) hm).2
  rw [henergy]
  calc
    _ = ∫ ω, (2/p)*((ε+A b ω)^(p/2)-ε^(p/2)) ∂P := integral_congr_ae (he.mono (fun ω hω => hω b hb))
    _ = _ := integral_const_mul _ _

end Asakura.Chapter3Complete
#print axioms Asakura.Chapter3Complete.regularized_ito_stopped_energy
