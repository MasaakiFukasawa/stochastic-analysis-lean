import Chapter2SemimartingaleDecomposition
import Chapter3IncreasingAdaptedVariation

open MeasureTheory Set
namespace Asakura.Chapter10
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete
set_option backward.isDefEq.respectTransparency false

theorem SemimartingaleDecomposition.linear_combination {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {T : EReal} [Fact (0≤T)]
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (X Y A D M N : ClosedTime T → Ω → ℝ)
    (hX : SemimartingaleDecomposition P F X A M) (hY : SemimartingaleDecomposition P F Y D N)
    (a b : ℝ) : SemimartingaleDecomposition P F
      (fun t w => a*X t w+b*Y t w) (fun t w => a*A t w+b*D t w) (fun t w => a*M t w+b*N t w) := by
  refine ⟨(hX.variation.smul a).add (hY.variation.smul b) hF,
    (hX.martingale.smul P F a).add P F hF hle (hY.martingale.smul P F b),?_,?_⟩
  · intro w t ht
    exact ((hX.continuous w t ht).const_mul a).add ((hY.continuous w t ht).const_mul b)
  · intro t ht w
    rw [hX.decomposition t ht w,hY.decomposition t ht w]
    ring

/-- Subtracting the price from an initially known value gives the actual
error semimartingale used in the profit calculation. -/
theorem SemimartingaleDecomposition.initial_sub {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {T : EReal} [Fact (0≤T)] (hT : 0<T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F)
    (X A M : ClosedTime T → Ω → ℝ) (hX : SemimartingaleDecomposition P F X A M)
    (V : Ω → ℝ) (hV : Measurable[F ⊥] V) :
    SemimartingaleDecomposition P F (fun t w => V w-X t w)
      (fun t w => V w-A t w) (fun t w => -M t w) := by
  have hconst := continuous_increasing_adapted_variation hT F hF (fun _ w => V w)
    (fun _ _ => hV.mono (hF bot_le) le_rfl) (fun _ _ _ _ _ _ => le_rfl)
    (fun _ _ _ => continuousAt_const)
  refine ⟨?_,?_,?_,?_⟩
  · simpa only [neg_one_mul,← sub_eq_add_neg] using hconst.add (hX.variation.smul (-1)) hF
  · simpa only [neg_one_mul] using hX.martingale.smul P F (-1)
  · intro w t ht
    exact continuousAt_const.sub (hX.continuous w t ht)
  · intro t ht w
    rw [hX.decomposition t ht w]
    ring

end Asakura.Chapter10
