import Chapter12GreekTransfer
import Chapter12MalliavinC1Chain

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

theorem closed_malliavin_greek_transfer {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [Nontrivial H]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : H →ₗᵢ[ℝ] Lp ℝ 2 P) (S : Set H) (hS : Dense S)
    (hcore : ∀ h ∈ S, HasLaw (W h : Ω → ℝ) (gaussianReal 0 ⟨‖h‖^2,sq_nonneg _⟩) P)
    (D : Lp ℝ 2 P →ₗ.[ℝ] Lp H 2 P) (hD : D.IsClosed)
    (hgraph : (D.graph : Set _) = closure (range (cylinderPair P W S hS hcore 2 (by simp))))
    (F : Lp ℝ 2 P) (U : Lp H 2 P) (hFU : (F,U) ∈ D.graph)
    (v : Lp H 2 P) (Z : Lp ℝ 2 P) (hdiv : IsDivergence D v Z)
    (Fθ : Ω → ℝ) (he : ∀ᵐ w ∂P, inner ℝ (U w) (v w) = Fθ w)
    (ψ dψ : ℝ → ℝ) (hd : ∀ x, HasDerivAt ψ (dψ x) x) (hdc : Continuous dψ)
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ x, |dψ x| ≤ C) :
    (∫ w,dψ (F w)*Fθ w ∂P) = ∫ w,ψ (F w)*Z w ∂P := by
  obtain ⟨hi,hchain⟩ := closed_malliavin_C1_chain P W S hS hcore 2 (by simp)
    D hD hgraph F U hFU ψ dψ hd hdc C hC hb
  let V := lipschitzCompositionLp P 2 (bounded_derivative_lipschitz ψ dψ hd C hC hb) F
  have hV : MemLp (fun w => ψ (F w)) 2 P :=
    (Lp.memLp V).ae_eq (lipschitzCompositionLp_coe P 2 _ F)
  have hVe : hV.toLp _ = V := by
    apply Lp.ext
    exact hV.coeFn_toLp.trans (lipschitzCompositionLp_coe P 2 _ F).symm
  have hch : (hV.toLp _,hi.toLp _) ∈ D.graph := by
    rw [hVe]
    exact hchain
  apply greek_derivative_transfer P D F Fθ U v ψ dψ Z hV hi (Lp.memLp v) (Lp.memLp Z) hch he
  simpa only [Lp.toLp_coeFn] using hdiv

end Asakura.Chapter12
