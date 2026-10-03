import Chapter10DeterministicNoisePath
import Chapter4VectorPaths

open MeasureTheory Set
open scoped BigOperators ENNReal
namespace Asakura.Chapter10
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter8
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

/-- Bundle the actual scalar noise integrals into the vector forcing path;
its L2 path moment is derived, not part of the SDE assumptions. -/
theorem deterministic_vector_noise_path {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d n : ℕ} (B : BrownianSystem P n)
    (G : Fin d → Fin n → ℝ → ℝ) (hG : ∀ i j,Continuous (G i j))
    (N : Fin d → Fin n → HalfClosedTime → Ω → ℝ)
    (hN : ∀ i j,LocalMProcessWitness P B.F (N i j))
    (hNI : ∀ i j,ItoCovarianceFormula P B.F (B.W j) (fun z => G i j z.2) (N i j))
    (T : ℝ) (hT : 0≤T) :
    ∃ W : Ω → C(Icc (0:ℝ) T,Fin d → ℝ),Measurable W ∧ MemLp W 2 P ∧
      ∀ w t i,W w t i=∑ j,N i j (realTimeClamp t.val) w := by
  have hex i j := deterministic_noise_path P B j (G i j) (hG i j) (N i j) (hN i j) (hNI i j) T hT
  choose Z hm hi he hb using hex
  let Y := fun i w => ∑ j,Z i j w
  have hYm i : Measurable (Y i) := Finset.measurable_sum _ (fun j _ => hm i j)
  have hYi i : MemLp (Y i) 2 P := by
    exact memLp_finsetSum (f := fun j w => Z i j w) Finset.univ (fun j _ => hi i j)
  refine ⟨fun w => bundleRealPaths (fun i => Y i w),bundle_path_measurable Y hYm,
    bundle_path_memLp P Y hYm hYi,?_⟩
  intro w t i
  change (∑ j,Z i j w) t=∑ j,N i j (realTimeClamp t.val) w
  simp only [ContinuousMap.sum_apply,he]

end Asakura.Chapter10
