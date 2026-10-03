import Chapter9OULaw

open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators RealInnerProductSpace
namespace Asakura.Chapter9
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter8
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

/-- Construct the stochastic integrals, verify the Chapter-9 SDE, and
identify the law of this same constructed solution. -/
theorem standard_ou_constructed {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (B : BrownianSystem P d) :
    ∃ N : Fin d → Fin d → HalfClosedTime → Ω → ℝ,
      (∀ i j,LocalMProcessWitness P B.F (N i j)) ∧
      (∀ i j,ItoCovarianceFormula P B.F (B.W j)
        (fun z => ((Real.sqrt 2) • (1 : Matrix (Fin d) (Fin d) ℝ)) i j*Real.exp z.2) (N i j)) ∧
      (∀ x : Fin d → ℝ,∀ᵐ w ∂P,∀ t≥0,∀ i,
        Real.exp (-t)*(x i+∑ j,N i j (realTimeClamp t) w)=x i-
          (∫ s in 0..t,Real.exp (-s)*(x i+∑ j,N i j (realTimeClamp s) w))+
          Real.sqrt 2*B.W i (realTimeClamp t) w) ∧
      ∀ (μ : Measure (EuclideanSpace ℝ (Fin d))),IsProbabilityMeasure μ → ∀ t≥0,
        flowLaw μ P (fun x w => Real.exp (-t) • x+
          WithLp.toLp 2 (fun i => Real.exp (-t)*(∑ j,N i j (realTimeClamp t) w)))=
          gaussianAffineLaw μ (Real.exp (-t)) (Real.sqrt (1-Real.exp (-2*t))) := by
  obtain ⟨N,hN,hNI,hsol⟩ := vector_ou_constructed P B
    ((Real.sqrt 2) • (1 : Matrix (Fin d) (Fin d) ℝ))
  refine ⟨N,hN,hNI,?_,?_⟩
  · intro x
    filter_upwards [hsol x] with w hw
    intro t ht i
    have hh := hw t ht i
    have hs : (∑ j,((Real.sqrt 2) • (1 : Matrix (Fin d) (Fin d) ℝ)) i j*
        B.W j (realTimeClamp t) w)=Real.sqrt 2*B.W i (realTimeClamp t) w := by
      change (((Real.sqrt 2) • (1 : Matrix (Fin d) (Fin d) ℝ)) *ᵥ
        (fun j => B.W j (realTimeClamp t) w)) i=_
      rw [smul_mulVec,one_mulVec]
      rfl
    rw [hs] at hh
    exact hh
  · intro μ hμ t ht
    letI := hμ
    exact standard_ou_affine_law P B N hN hNI t ht μ
end Asakura.Chapter9
