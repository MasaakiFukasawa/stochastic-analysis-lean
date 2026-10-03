import Chapter5ZeroIto
import Chapter3VariationIntegratorCongruence

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter5
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete

/-- A past observation, measurable at the left endpoint of an interval,
is an actual constant semimartingale on that interval. It may be random
and unbounded. This is the legitimate way to substitute random past
coordinates in the heat-kernel Ito formula. -/
theorem frozen_coordinate_semimartingale
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F)
    (U : Ω → ℝ) (hU : Measurable[F ⊥] U) :
    SemimartingaleDecomposition P F (fun _ => U) (fun _ => U) (fun _ _ => 0) := by
  have hv : AdaptedVariationWitness F (fun _ => U) := by
    refine ⟨(fun _ => U),(fun _ _ => 0),?_,?_,?_,?_⟩
    · intro t; exact ⟨hU.mono (hF bot_le) le_rfl,measurable_const⟩
    · intro w; exact ⟨monotone_const,monotone_const⟩
    · intro w t; exact ⟨continuousWithinAt_const,continuousWithinAt_const⟩
    · intro t w; simp
  exact ⟨global_variation_localized hT F hF _ hv,zero_local_process P hT F,
    (fun _ _ _ => continuousAt_const),(fun _ _ _ => by simp)⟩

/-- Both integrals with respect to a frozen coordinate vanish, on one
common probability-one event for all times. No exceptional event is
chosen separately for each value of the random parameter. -/
theorem frozen_coordinate_integral_zero
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (U : Ω → ℝ) (I : ClosedTime T → Ω → ℝ) (H : Ω × ℝ → ℝ)
    (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n) (hcT : ∀ n, (c n:EReal) < T)
    (hcc : ∀ t, t < ⊤ → ∃ n, t < realTimeClamp (T := T) (c n))
    (hI : SemimartingaleIntegralFormula P F c hc (fun _ => U) (fun _ _ => 0) H I) :
    ∀ᵐ w ∂P, ∀ t, t < ⊤ → I t w = 0 := by
  obtain ⟨D,N,hDN,hD,hN⟩ := hI
  have hd : VariationIntegralFormula P c hc (fun _ _ => 0) H D :=
    variation_integral_integrator_increments_congr P (fun _ => U) (fun _ _ => 0) D H c hc hcT hD
      (ae_of_all _ fun _ _ _ _ _ => by simp)
  have hd0 := hd.unique P c hc hcc _ D (fun _ _ => 0) H (zero_variation_integral P c hc H)
  have hn0 := integral_against_zero_martingale P hT F hF hle hnull N H hDN.martingale hN
  filter_upwards [hd0,hn0] with w hdw hnw
  intro t ht
  rw [hDN.decomposition t ht w,hdw t ht,hnw t ht,zero_add]

end Asakura.Chapter5
