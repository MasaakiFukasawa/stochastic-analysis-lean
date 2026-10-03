import Chapter3InverseWeightPathBound
import Chapter3RegularizedItoStoppedEnergy

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter3Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false

/-- The complete stochastic construction in the p<2 upper BDG argument:
actual regularized Ito integral, stopped M₂ membership, energy, and path bound. -/
theorem regularized_bdg_upper_construction
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (X A : ClosedTime T → Ω → ℝ)
    (hX : LocalMProcessWitness P F X) (hA : LocalCovarianceWitness P F X X A)
    (hAm : ∀ ω, MonotoneOn (fun t => A t ω) (Iio ⊤))
    (hAc : ∀ ω t, t < ⊤ → ContinuousAt (fun s => A s ω) t)
    (hA0 : ∀ ω, A ⊥ ω = 0)
    (ε p : ℝ) (hε : 0 < ε) (hp : 0 < p) (hp2 : p < 2)
    (b : ClosedTime T) (hb : b < ⊤) (K : ℝ) (hK : 0 ≤ K)
    (hbound : ∀ᵐ ω ∂P, A b ω ≤ K) :
    ∃ Y : ClosedTime T → Ω → ℝ,
      LocalMProcessWitness P F Y ∧
      ItoCovarianceFormula P F X (fun z => (ε+A (realTimeClamp z.2) z.1)^((p-2)/4)) Y ∧
      ContinuousM2Witness P F (fun t ω => Y (min b t) ω) ∧
      (∫ ω, Y b ω^2 ∂P) = (2/p)*(∫ ω, (ε+A b ω)^(p/2)-ε^(p/2) ∂P) ∧
      (∀ᵐ ω ∂P, ∀ t, t < ⊤ → ∀ L : ℝ, 0 ≤ L →
        (∀ s, s ≤ t → |Y s ω| ≤ L) →
        ∀ s, s ≤ t → |X s ω| ≤ 2*L*(ε+A t ω)^((2-p)/4)) := by
  have hAp ω t (ht : t < ⊤) : 0 ≤ A t ω := by
    rw [← hA0 ω]
    exact hAm ω hT ht bot_le
  have hG := shifted_power_process_regularity F A (hA.adapted P F hX hX) hAc hAp ε ((p-2)/4) hε
  have hV := shifted_power_process_regularity F A (hA.adapted P F hX hX) hAc hAp ε ((2-p)/4) hε
  have hVm := shifted_power_process_monotone A hAm hAp ε ((2-p)/4) hε.le (by linarith)
  obtain ⟨Y,hY,hy,hpath⟩ := inverse_increasing_weight_path_bound P hT F hF hle hnull
    X (fun t ω => (ε+A t ω)^((p-2)/4)) (fun t ω => (ε+A t ω)^((2-p)/4)) hX
    hG.1 hG.2.1 hV.1 hV.2.1 hVm (fun ω t ht => (hV.2.2 ω t ht).le)
    (fun ω t ht => Asakura.Chapter3Written.regularized_inverse_weights hε (hAp ω t ht))
  have henergy := regularized_ito_stopped_energy P hT F hF hle hnull X A Y hX hA hAm hAc hA0
    ε p hε hp hY hy b hb K hK hbound
  exact ⟨Y,hY,hy,henergy.1,henergy.2,hpath⟩

end Asakura.Chapter3Complete
#print axioms Asakura.Chapter3Complete.regularized_bdg_upper_construction
