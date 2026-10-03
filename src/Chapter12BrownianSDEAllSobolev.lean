import Chapter12SmoothSolutionAllSobolev
import Chapter12FiniteBrownianPathMoments

open MeasureTheory ProbabilityTheory Set ENNReal Filter
open scoped ContDiff NNReal Topology
namespace Asakura.Chapter12
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false

theorem brownian_sde_all_sobolev {Ω : Type*} {E : Type} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P] (d : ℕ) (T : ℝ≥0) (hT : 0<T)
    (W : FiniteWienerHilbert d T →ₗᵢ[ℝ] Lp ℝ 2 P)
    (hW : ∀u,HasLaw (W u : Ω → ℝ) (gaussianReal 0 ⟨‖u‖^2,sq_nonneg _⟩) P)
    (B : Fin (d+1) → ℝ≥0 → Ω → ℝ)
    (hB : ∀i,IsPreBrownianReal (B i) P) (hm : ∀i t,Measurable (B i t))
    (hcB : ∀i w,Continuous (fun t => B i t w))
    (hcoord : ∀(i : Fin (d+1)) (t : Icc (0:ℝ) T),
      B i ⟨t.val,t.property.1⟩=ᵐ[P] (W (brownianTimeDirection (i,t)) : Ω → ℝ))
    (v : Fin (d+1) → E) (x : E) (b : E → E) (hb : ContDiff ℝ ∞ b)
    (hbound : ∀k:ℕ,1≤k → ∃C:ℝ≥0,∀x,‖iteratedFDeriv ℝ k b x‖≤(C:ℝ)) :
    letI := finite_horizon_L2_nontrivial T hT
    let H := finiteWienerHilbertData d T
    let hc := fun u (_ : u∈(univ : Set H)) => hW u
    (∀(q:ℝ≥0∞) [Fact (1≤q)] (hq:q≠⊤),
      DenseRange (fun c : SmoothCylinder H => c.valueLp P W univ dense_univ hc q hq)) →
    ∃S : C(Icc (0:ℝ) T,E) → C(Icc (0:ℝ) T,E),ContDiff ℝ ∞ S ∧
      (∀a t,S a t=a t+∫s in 0..t.val,b (S a (projIcc (0:ℝ) (T:ℝ) (show (0:ℝ)≤T from hT.le) s))) ∧
      ∀(ell : E →L[ℝ] ℝ) (t : Icc (0:ℝ) T),
        HasAllSobolevJets H P W univ dense_univ hc
          (fun w => ell (S (ContinuousMap.const _ x+(columnOperator v).compLeftContinuous ℝ (Icc (0:ℝ) T) (finiteBrownianCompactPath B hcB T w)) t)) := by
  intro H hc hdense
  letI := finite_horizon_L2_nontrivial T hT
  let Y := finiteBrownianCompactPath B hcB T
  have hYm : Measurable Y := by
    apply ContinuousMap.measurable_iff_eval.mpr
    intro t
    exact Measurable.of_eval (fun i => hm i _)
  exact smooth_solution_all_sobolev P d T hT W hW
    (fun z w => B z.1 ⟨z.2.val,z.2.property.1⟩ w) (fun z => hcoord z.1 z.2)
    Y hYm (fun _ _ _ => rfl) (finite_brownian_path_memLp P B hB hm hcB T)
    v x b hb hbound hdense
end Asakura.Chapter12
#print axioms Asakura.Chapter12.brownian_sde_all_sobolev
