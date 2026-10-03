import Chapter3SemimartingaleFiniteSums
import Chapter2LocalCovarianceRules

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter4
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

variable {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
  {T : EReal} [Fact (0≤T)] (hT : 0<T)
  (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)

include hT hF hle

lemma local_martingale_finset_sum {ι : Type*} (s : Finset ι)
    (X : ι → ClosedTime T → Ω → ℝ) (hX : ∀ i∈s,LocalMProcessWitness P F (X i)) :
    LocalMProcessWitness P F (fun t w => ∑ i∈s,X i t w) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using zero_local_process P hT F
  | @insert i s hi ih =>
    simpa only [Finset.sum_insert hi] using (hX i (Finset.mem_insert_self _ _)).add P F hF hle
      (ih (fun j hj => hX j (Finset.mem_insert_of_mem hj)))

lemma zero_covariance_left (X : ClosedTime T → Ω → ℝ) :
    LocalCovarianceWitness P F (fun _ _ => 0) X (fun _ _ => 0) := by
  refine ⟨?_,?_⟩
  · simpa only [zero_mul,sub_zero] using zero_local_process P hT F
  · exact (continuous_increasing_adapted_variation hT F hF (fun _ _ => (0:ℝ))
      (fun _ _ => measurable_const) (fun _ => monotoneOn_const) (fun _ _ _ => continuousAt_const)).toPathwise

lemma weighted_covariance_finset_left {ι : Type*} (s : Finset ι)
    (X C : ι → ClosedTime T → Ω → ℝ) (Z : ClosedTime T → Ω → ℝ)
    (u : ι → ℝ) (hC : ∀ i∈s,LocalCovarianceWitness P F (X i) Z (C i)) :
    LocalCovarianceWitness P F (fun t w => ∑ i∈s,u i*X i t w) Z
      (fun t w => ∑ i∈s,u i*C i t w) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using zero_covariance_left P hT F hF hle Z
  | @insert i s hi ih =>
    simpa only [Finset.sum_insert hi] using (hC i (Finset.mem_insert_self _ _)).bilinear P F hF hle
      (ih (fun j hj => hC j (Finset.mem_insert_of_mem hj))) (u i)

lemma weighted_covariance_sum {dim : ℕ}
    (X : Fin dim → ClosedTime T → Ω → ℝ) (C : Fin dim → Fin dim → ClosedTime T → Ω → ℝ)
    (u v : Fin dim → ℝ) (hC : ∀ i j,LocalCovarianceWitness P F (X i) (X j) (C i j)) :
    LocalCovarianceWitness P F (fun t w => ∑ i,u i*X i t w) (fun t w => ∑ j,v j*X j t w)
      (fun t w => ∑ j,v j*(∑ i,u i*C i j t w)) := by
  have hh j := weighted_covariance_finset_left P hT F hF hle Finset.univ X
    (fun i => C i j) (X j) u (fun i _ => hC i j)
  exact (weighted_covariance_finset_left P hT F hF hle Finset.univ X
    (fun j t w => ∑ i,u i*C i j t w) (fun t w => ∑ i,u i*X i t w) v
    (fun j _ => (hh j).symm P F)).symm P F

end Asakura.Chapter4
