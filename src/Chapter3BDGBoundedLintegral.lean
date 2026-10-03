import Chapter3BDGConstants

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter3Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

/-- Bounded BDG in extended moments, ready for monotone convergence. -/
theorem bounded_bdg_lintegrals
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (X A : ClosedTime T → Ω → ℝ)
    (hX : LocalMProcessWitness P F X) (hA : LocalCovarianceWitness P F X X A)
    (hAm : ∀ ω, MonotoneOn (fun t => A t ω) (Iio ⊤))
    (hAc : ∀ ω t, t < ⊤ → ContinuousAt (fun s => A s ω) t)
    (hA0 : ∀ ω, A ⊥ ω = 0)
    (p : ℝ) (hp : 0 < p) (b : ClosedTime T) (hb : b < ⊤)
    (K L : ℝ) (hK : 0 ≤ K) (hL : 0 ≤ L)
    (hbound : ∀ᵐ ω ∂P, A b ω ≤ K)
    (hXbound : ∀ᵐ ω ∂P, ∀ s, s ≤ b → |X s ω| ≤ L) :
    (∫⁻ ω, (ENNReal.ofReal (runningMaximum X (hX.path P F) b ω))^p ∂P) ≤
      ENNReal.ofReal (bdgUpperMomentConstant p)*(∫⁻ ω, (ENNReal.ofReal (A b ω))^(p/2) ∂P) ∧
    (∫⁻ ω, (ENNReal.ofReal (A b ω))^(p/2) ∂P) ≤
      ENNReal.ofReal (bdgReverseMomentConstant p)*(∫⁻ ω, (ENNReal.ofReal (runningMaximum X (hX.path P F) b ω))^p ∂P) := by
  obtain ⟨hSi,hQi,hu,hl⟩ := bounded_bdg_moments P hT F hF hle hnull X A hX hA hAm hAc hA0 p hp b hb K L hK hL hbound hXbound
  have hAp ω : 0 ≤ A b ω := by rw [← hA0 ω]; exact hAm ω hT hb bot_le
  have hS ω : 0 ≤ runningMaximum X (hX.path P F) b ω := runningMaximum_nonneg X (hX.path P F) b ω
  have hSexp : ENNReal.ofReal (∫ ω, runningMaximum X (hX.path P F) b ω^p ∂P) =
      ∫⁻ ω, (ENNReal.ofReal (runningMaximum X (hX.path P F) b ω))^p ∂P := by
    rw [ofReal_integral_eq_lintegral_ofReal hSi (Filter.Eventually.of_forall (fun ω => Real.rpow_nonneg (hS ω) p))]
    apply lintegral_congr
    intro ω
    exact (ENNReal.ofReal_rpow_of_nonneg (hS ω) hp.le).symm
  have hQexp : ENNReal.ofReal (∫ ω, A b ω^(p/2) ∂P) =
      ∫⁻ ω, (ENNReal.ofReal (A b ω))^(p/2) ∂P := by
    rw [ofReal_integral_eq_lintegral_ofReal hQi (Filter.Eventually.of_forall (fun ω => Real.rpow_nonneg (hAp ω) _))]
    apply lintegral_congr
    intro ω
    exact (ENNReal.ofReal_rpow_of_nonneg (hAp ω) (by positivity)).symm
  have hcu := (bdg_moment_constants_positive p hp).1.le
  have hcl := (bdg_moment_constants_positive p hp).2.le
  have hu' := ENNReal.ofReal_le_ofReal hu
  have hl' := ENNReal.ofReal_le_ofReal hl
  rw [ENNReal.ofReal_mul hcu,hSexp,hQexp] at hu'
  rw [ENNReal.ofReal_mul hcl,hSexp,hQexp] at hl'
  exact ⟨hu',hl'⟩

end Asakura.Chapter3Complete
#print axioms Asakura.Chapter3Complete.bounded_bdg_lintegrals
