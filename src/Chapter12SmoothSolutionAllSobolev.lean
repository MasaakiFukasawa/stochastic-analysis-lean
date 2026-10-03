import Chapter12SmoothSolutionSobolev
import Chapter12AllSobolevFromEven

open MeasureTheory ProbabilityTheory Set ENNReal Filter
open scoped ContDiff NNReal Topology
namespace Asakura.Chapter12
set_option maxHeartbeats 2800000
set_option backward.isDefEq.respectTransparency false

theorem smooth_solution_all_sobolev {Ω : Type*} {E : Type} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P] (d : ℕ) (T : ℝ) (hT : 0<T)
    (W : FiniteWienerHilbert d T →ₗᵢ[ℝ] Lp ℝ 2 P)
    (hW : ∀u,HasLaw (W u : Ω → ℝ) (gaussianReal 0 ⟨‖u‖^2,sq_nonneg _⟩) P)
    (B : BrownianTimeCoordinates d T → Ω → ℝ)
    (hB : ∀z,B z=ᵐ[P] (W (brownianTimeDirection z) : Ω → ℝ))
    (Y : Ω → C(Icc (0:ℝ) T,Fin (d+1) → ℝ)) (hYm : Measurable Y)
    (hY : ∀w t i,Y w t i=B (i,t) w)
    (hYp : ∀p:ℝ≥0∞,p≠⊤ → MemLp Y p P)
    (v : Fin (d+1) → E) (x : E) (b : E → E) (hb : ContDiff ℝ ∞ b)
    (hbound : ∀k:ℕ,1≤k → ∃C:ℝ≥0,∀x,‖iteratedFDeriv ℝ k b x‖≤(C:ℝ)) :
    letI := finite_horizon_L2_nontrivial T hT
    let H := finiteWienerHilbertData d T
    let hc := fun u (_ : u∈(univ : Set H)) => hW u
    (∀(q:ℝ≥0∞) [Fact (1≤q)] (hq:q≠⊤),
      DenseRange (fun c : SmoothCylinder H => c.valueLp P W univ dense_univ hc q hq)) →
    ∃S : C(Icc (0:ℝ) T,E) → C(Icc (0:ℝ) T,E),ContDiff ℝ ∞ S ∧
      (∀a t,S a t=a t+∫s in 0..t.val,b (S a (projIcc 0 T hT.le s))) ∧
      ∀(ell : E →L[ℝ] ℝ) (t : Icc (0:ℝ) T),
        HasAllSobolevJets H P W univ dense_univ hc
          (fun w => ell (S (ContinuousMap.const _ x+(columnOperator v).compLeftContinuous ℝ (Icc (0:ℝ) T) (Y w)) t)) := by
  intro H hc hdense
  letI := finite_horizon_L2_nontrivial T hT
  obtain ⟨S,hS,hSeq,hjet⟩ := smooth_solution_sobolev P d T hT W hW B hB Y hYm hY v x b hb hbound
  refine ⟨S,hS,hSeq,?_⟩
  intro ell t
  apply all_sobolev_from_even H P W univ dense_univ hc
  intro n hn k
  letI : Fact (1≤((2*n:ℕ):ℝ≥0∞)) := ⟨by exact_mod_cast (show 1≤2*n by omega)⟩
  let q := ENNReal.conjExponent (2*n:ℕ)
  obtain ⟨hq1,hq⟩ := even_conjugate_properties n hn
  letI : Fact (1≤q) := ⟨hq1⟩
  exact hjet (2*n:ℕ) q (ENNReal.natCast_ne_top _) hq (hdense q hq)
    (hYp _ (ENNReal.natCast_ne_top _)) ell t k
end Asakura.Chapter12
#print axioms Asakura.Chapter12.smooth_solution_all_sobolev
