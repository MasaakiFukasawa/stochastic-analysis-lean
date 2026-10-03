import Chapter5ClippedClockDensity
import Chapter5ConstructedMultivariateIto

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter5
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false

/-- Add the deterministic clock as an actual semimartingale coordinate.
Every covariance involving this coordinate is constructed as zero. -/
theorem clock_augmented_family
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0<T) {d : ℕ}
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F)
    (X A M : Fin d → ClosedTime T → Ω → ℝ)
    (C : Fin d → Fin d → ClosedTime T → Ω → ℝ)
    (hX : ∀ i,SemimartingaleDecomposition P F (X i) (A i) (M i))
    (hC : ∀ i j,LocalCovarianceWitness P F (M i) (M j) (C i j))
    (R : ℝ) (hR : 0≤R) :
    let K := fun t (_ : Ω) => (finitePrefixTime (T := T) R hR t).val
    let XX := Fin.cons K X
    let AA := Fin.cons K A
    let MM := Fin.cons (fun _ _ => (0:ℝ)) M
    let CC := fun i j => Fin.cases (fun _ => (fun _ _ => (0:ℝ)))
      (fun k => Fin.cases (fun _ _ => (0:ℝ)) (C k)) i j
    (∀ i,SemimartingaleDecomposition P F (XX i) (AA i) (MM i)) ∧
      (∀ i j,LocalCovarianceWitness P F (MM i) (MM j) (CC i j)) := by
  dsimp only
  have hK := clipped_clock_semimartingale P hT F hF R hR
  have hzero : LocalVariationWitness F (fun _ : ClosedTime T => fun _ : Ω => (0:ℝ)) := by
    simpa only [zero_mul] using hK.variation.toPathwise.smul F 0
  have hz (N : ClosedTime T → Ω → ℝ) : LocalCovarianceWitness P F (fun _ _ => 0) N (fun _ _ => 0) := by
    refine ⟨?_,hzero⟩
    simpa only [zero_mul,sub_zero] using zero_local_process P hT F
  constructor
  · intro i
    exact Fin.cases hK hX i
  · intro i j
    refine Fin.cases ?_ (fun k => ?_) i
    · exact hz _
    · exact Fin.cases ((hz (M k)).symm P F) (hC k) j

end Asakura.Chapter5
