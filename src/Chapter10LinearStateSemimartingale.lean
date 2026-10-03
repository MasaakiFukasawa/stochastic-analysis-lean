import Chapter10AdaptedLinearState
import Chapter10SDEDecomposition

open MeasureTheory Set
open scoped BigOperators NNReal ENNReal
namespace Asakura.Chapter10
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter8
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

/-- Every coordinate of the constructed adapted linear state has the actual
finite-horizon semimartingale decomposition, and its entire path is in L2. -/
theorem linear_state_semimartingale {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d n : ℕ} (B : BrownianSystem P n)
    (A : ℝ → (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)) (hA : Continuous A)
    (K : ℝ≥0) (hAK : ∀ t, ‖A t‖ ≤ K)
    (G : Fin d → Fin n → ℝ → ℝ) (hG : ∀ i j, Continuous (G i j))
    (ξ : Ω → Fin d → ℝ) (hξ : Measurable[B.F ⊥] ξ) (hξ2 : MemLp ξ 2 P)
    (T : ℝ) (hT : 0 ≤ T) :
    ∃ (N : Fin d → Fin n → HalfClosedTime → Ω → ℝ)
      (X : Ω → C(Icc (0:ℝ) T, Fin d → ℝ)),
      (∀ i j, LocalMProcessWitness P B.F (N i j)) ∧
      (∀ i j, ItoCovarianceFormula P B.F (B.W j) (fun z => G i j z.2) (N i j)) ∧
      Measurable X ∧ MemLp X 2 P ∧
      (∀ i, SemimartingaleDecomposition P B.F
        (fun t w => X w (finitePrefixTime T hT t) i)
        (fun t w => ξ w i + ∫ s in 0..(finitePrefixTime T hT t).val,
          (A s (X w (projIcc 0 T hT s))) i)
        (fun t w => ∑ j, N i j (min (realTimeClamp T) t) w)) := by
  letI : MeasurableSpace Ω := m
  obtain ⟨N,X,hN,hNI,hm,hi,ha,he⟩ := adapted_linear_state P B A hA K hAK G hG ξ hξ hξ2 T hT
  refine ⟨N,X,hN,hNI,hm,hi,?_⟩
  intro i
  let U := fun s w => X w (projIcc 0 T hT s)
  have hp s (hs : s ∈ Icc (0:ℝ) T) : projIcc 0 T hT s=⟨s,hs⟩ :=
    Subtype.ext (by simp [projIcc,hs.1,hs.2])
  have hc w : Continuous (fun s => U s w) := (X w).continuous.comp continuous_projIcc
  have hac w : Continuous (fun s => (A s (U s w)) i) :=
    (continuous_apply i).comp (hA.clm_apply (hc w))
  have had s (hs : s ∈ Icc (0:ℝ) T) :
      Measurable[B.F (realTimeClamp s)] (fun w => (A s (U s w)) i) := by
    letI : MeasurableSpace Ω := B.F (realTimeClamp s)
    have hu : Measurable (U s) := by simpa only [U,hp s hs] using ha ⟨s,hs⟩
    exact (measurable_pi_apply i).comp ((A s).continuous.measurable.comp hu)
  have hei w r (hr : r ∈ Icc (0:ℝ) T) :
      U r w i=ξ w i+(∫ s in 0..r,(A s (U s w)) i)+∑ j,N i j (realTimeClamp r) w := by
    have hh := congrArg (fun x : Fin d → ℝ => x i) (he w ⟨r,hr⟩)
    have hInt : IntervalIntegrable (fun s => A s (U s w)) volume 0 r :=
      (hA.clm_apply (hc w)).intervalIntegrable _ _
    have hEval := (ContinuousLinearMap.proj i : (Fin d → ℝ) →L[ℝ] ℝ).intervalIntegral_comp_comm hInt
    change (∫ s in 0..r,(A s (U s w)) i) = (∫ s in 0..r,A s (U s w)) i at hEval
    simpa only [U,hp r hr,Pi.add_apply,←hEval] using hh
  have hh := finite_sde_decomposition P B.F B.mono B.le (N i) (hN i)
    (fun s w => U s w i) (fun s w => (A s (U s w)) i) (fun w => ξ w i)
    ((measurable_pi_apply i).comp hξ) T hT
    (fun w => ((continuous_apply i).comp (hc w)).continuousOn) had
    (fun w => (hac w).continuousOn) hei
  have heq : (fun (t : HalfClosedTime) w => U (finitePrefixTime T hT t).val w i) =
      (fun t w => X w (finitePrefixTime T hT t) i) := by
    funext t w
    simp only [U,hp _ (finitePrefixTime T hT t).property]
  rw [heq] at hh
  exact hh

end Asakura.Chapter10
