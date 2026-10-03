import Chapter10SemimartingaleAlgebra
import Chapter3SemimartingaleFiniteSums
import Chapter4FiniteItoSum

open MeasureTheory Set
open scoped BigOperators
namespace Asakura.Chapter10
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

theorem semimartingale_weighted_sum {Ω ι : Type*} [m : MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) [IsProbabilityMeasure P] {T : EReal} [Fact (0≤T)] (hT : 0<T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (X A M : ι → ClosedTime T → Ω → ℝ) (q : ι → ℝ)
    (h : ∀ i,SemimartingaleDecomposition P F (X i) (A i) (M i)) :
    SemimartingaleDecomposition P F (fun t w => ∑ i,q i*X i t w)
      (fun t w => ∑ i,q i*A i t w) (fun t w => ∑ i,q i*M i t w) := by
  refine ⟨adapted_variation_finset_sum hT F hF Finset.univ _ (fun i _ => (h i).variation.smul (q i)),
    local_martingale_finset_sum P hT F hF hle Finset.univ _ (fun i _ => (h i).martingale.smul P F (q i)),?_,?_⟩
  · intro w t ht
    exact tendsto_finset_sum _ (fun i _ => ((h i).continuous w t ht).const_mul _)
  · intro t ht w
    simp_rw [(h _).decomposition t ht w,mul_add,Finset.sum_add_distrib]

theorem ito_weighted_sum {Ω ι : Type*} [m : MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) [IsProbabilityMeasure P] {T : EReal} [Fact (0≤T)] (hT : 0<T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t Q,MeasurableSet[m] Q → P Q=0 → MeasurableSet[F t] Q)
    (B : ClosedTime T → Ω → ℝ) (hB : LocalMProcessWitness P F B)
    (N : ι → ClosedTime T → Ω → ℝ) (H : ι → Ω × ℝ → ℝ) (q : ι → ℝ)
    (hI : ∀ i,ItoCovarianceFormula P F B (H i) (N i)) :
    ItoCovarianceFormula P F B (fun z => ∑ i,q i*H i z) (fun t w => ∑ i,q i*N i t w) := by
  apply finite_ito_sum P hT F hF hle hnull B hB Finset.univ
  intro i _
  have hz := constant_ito_integral P hT F hF hle hnull B hB 0
  have hh := (hI i).add_smul P F hF hle B (N i) (fun t w => 0*B t w) (H i) (fun _ => 0) hz (q i)
  simpa only [zero_mul,add_zero] using hh

end Asakura.Chapter10
