import Chapter12SmoothSolutionFullApproximation
import Chapter12FiniteBrownianPathMoments

open MeasureTheory ProbabilityTheory Set ENNReal Filter
open scoped ContDiff NNReal Topology
namespace Asakura.Chapter12
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

theorem brownian_sde_full_approximation {Ω : Type*} {E : Type} [MeasurableSpace Ω]
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
    ∃S : C(Icc (0:ℝ) T,E) → C(Icc (0:ℝ) T,E),ContDiff ℝ ∞ S ∧
      (∀a t,S a t=a t+∫s in 0..t.val,b (S a (projIcc (0:ℝ) (T:ℝ) (show (0:ℝ)≤T from hT.le) s))) ∧
      ∀ (p q : ℝ≥0∞) [Fact (1≤p)] [Fact (1≤q)] [HolderConjugate p q]
        (hp : p≠⊤) (hq : q≠⊤),
        DenseRange (fun c : SmoothCylinder H => c.valueLp P W univ dense_univ hc 2 (by simp)) →
        DenseRange (fun c : SmoothCylinder H => c.valueLp P W univ dense_univ hc q hq) →
        ∃V : ℕ → Lp C(Icc (0:ℝ) T,E) p P,∃Z : Lp C(Icc (0:ℝ) T,E) p P,
        (∀i,(V i : Ω → C(Icc (0:ℝ) T,E))=ᵐ[P]
          (fun w => S (ContinuousMap.const _ x+brownianPolygonalForcing d T (show (0:ℝ)≤T from hT.le) (fun z w => B z.1 ⟨z.2.val,z.2.property.1⟩ w) v (T/(i+1:ℕ)) (i+1) w))) ∧
        (Z : Ω → C(Icc (0:ℝ) T,E))=ᵐ[P]
          (fun w => S (ContinuousMap.const _ x+(columnOperator v).compLeftContinuous ℝ (Icc (0:ℝ) T) (finiteBrownianCompactPath B hcB T w))) ∧
        Tendsto V atTop (𝓝 Z) ∧
        ∀ell : E →L[ℝ] ℝ,
        ∃N : ℕ → ℕ,∃e : ∀i,Fin (N i) → H,∃X : ∀i,(Fin (N i) → ℝ) → C(Icc (0:ℝ) T,ℝ),
        (∀i,ContDiff ℝ ∞ (X i)) ∧ (∀i t,∃f : GaussianJet (N i),f.f=fun z => X i z t) ∧
        (∀i,(fun w => X i (fun j => W (e i j) w))=ᵐ[P]
          (fun w => ell.compLeftContinuous ℝ (Icc (0:ℝ) T) (V i w))) ∧
        ∃U : ∀k:ℕ,ℕ → Lp C(Icc (0:ℝ) T,positiveMalliavinTensorPower H k) p P,
        ∃A : ∀k:ℕ,Lp C(Icc (0:ℝ) T,positiveMalliavinTensorPower H k) p P,
        (∀k,Tendsto (U k) atTop (𝓝 (A k))) ∧
        (∀k i,(U k i : Ω → C(Icc (0:ℝ) T,positiveMalliavinTensorPower H k))=ᵐ[P]
          (fun w => gaussianPathTensor H (e i) (X i) k (fun j => W (e i j) w))) ∧
        ∀t : Icc (0:ℝ) T,
          let J : ∀j:ℕ,Lp (malliavinTensorOrder H j) p P
            | 0 => (ell.comp (ContinuousMap.evalCLM ℝ t)).compLp Z
            | j+1 => (ContinuousMap.evalCLM ℝ t).compLp (A j)
          ∀k:ℕ,∃F : malliavinSobolevJetSpace H P W univ dense_univ hc p hp k,
            ∀j:Fin (k+1),F.val j=J j.val := by
  intro H hc
  letI := finite_horizon_L2_nontrivial T hT
  let Y := finiteBrownianCompactPath B hcB T
  have hYm : Measurable Y := by
    apply ContinuousMap.measurable_iff_eval.mpr
    intro t
    exact Measurable.of_eval (fun i => hm i _)
  obtain ⟨S,hS,hEq,hfull⟩ := smooth_solution_full_approximation P d T hT W hW
    (fun z w => B z.1 ⟨z.2.val,z.2.property.1⟩ w) (fun z => hcoord z.1 z.2)
    Y hYm (fun _ _ _ => rfl) v x b hb hbound
  refine ⟨S,hS,hEq,?_⟩
  intro p q _ _ _ hp hq hD2 hDq
  exact hfull p q hp hq hD2 hDq (finite_brownian_path_memLp P B hB hm hcB T p hp)
end Asakura.Chapter12
#print axioms Asakura.Chapter12.brownian_sde_full_approximation
