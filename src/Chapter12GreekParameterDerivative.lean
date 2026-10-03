import Chapter12ClosedGreekTransfer

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace ContDiff
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

/-- The manuscript explicitly assumes differentiation under expectation.
With that hypothesis, the closed Malliavin chain rule and divergence
identity give the derivative itself, not merely an equality of weights. -/
theorem greek_parameter_derivative {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [Nontrivial H]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : H →ₗᵢ[ℝ] Lp ℝ 2 P) (S : Set H) (hS : Dense S)
    (hcore : ∀ h∈S,HasLaw (W h : Ω → ℝ) (gaussianReal 0 ⟨‖h‖^2,sq_nonneg _⟩) P)
    (D : Lp ℝ 2 P →ₗ.[ℝ] Lp H 2 P) (hD : D.IsClosed)
    (hg : (D.graph : Set _)=closure (range (cylinderPair P W S hS hcore 2 (by simp))))
    (F : ℝ → Lp ℝ 2 P) (θ : ℝ) (U v : Lp H 2 P) (Z : Lp ℝ 2 P)
    (hFU : (F θ,U)∈D.graph) (hdiv : IsDivergence D v Z)
    (Fθ : Ω → ℝ) (he : ∀ᵐ w ∂P,inner ℝ (U w) (v w)=Fθ w)
    (ψ dψ : ℝ → ℝ) (hd : ∀ x,HasDerivAt ψ (dψ x) x) (hdc : Continuous dψ)
    (C : ℝ) (hC : 0≤C) (hb : ∀ x,|dψ x|≤C)
    (hexchange : HasDerivAt (fun t => ∫ w,ψ (F t w) ∂P)
      (∫ w,dψ (F θ w)*Fθ w ∂P) θ) :
    HasDerivAt (fun t => ∫ w,ψ (F t w) ∂P) (∫ w,ψ (F θ w)*Z w ∂P) θ := by
  rw [closed_malliavin_greek_transfer P W S hS hcore D hD hg (F θ) U hFU v Z hdiv
    Fθ he ψ dψ hd hdc C hC hb] at hexchange
  exact hexchange

/-- Smooth compactly supported test functions automatically satisfy the
bounded-derivative condition in the closed chain rule. -/
theorem greek_compact_test_derivative {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [Nontrivial H]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : H →ₗᵢ[ℝ] Lp ℝ 2 P) (S : Set H) (hS : Dense S)
    (hcore : ∀ h∈S,HasLaw (W h : Ω → ℝ) (gaussianReal 0 ⟨‖h‖^2,sq_nonneg _⟩) P)
    (D : Lp ℝ 2 P →ₗ.[ℝ] Lp H 2 P) (hD : D.IsClosed)
    (hg : (D.graph : Set _)=closure (range (cylinderPair P W S hS hcore 2 (by simp))))
    (F : ℝ → Lp ℝ 2 P) (θ : ℝ) (U v : Lp H 2 P) (Z : Lp ℝ 2 P)
    (hFU : (F θ,U)∈D.graph) (hdiv : IsDivergence D v Z)
    (Fθ : Ω → ℝ) (he : ∀ᵐ w ∂P,inner ℝ (U w) (v w)=Fθ w)
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ)
    (hexchange : HasDerivAt (fun t => ∫ w,ψ (F t w) ∂P)
      (∫ w,deriv ψ (F θ w)*Fθ w ∂P) θ) :
    HasDerivAt (fun t => ∫ w,ψ (F t w) ∂P) (∫ w,ψ (F θ w)*Z w ∂P) θ := by
  have hdc : Continuous (deriv ψ) := hψ.continuous_deriv (by simp)
  obtain ⟨C,hC⟩ := hcψ.deriv.exists_bound_of_continuous hdc
  exact greek_parameter_derivative P W S hS hcore D hD hg F θ U v Z hFU hdiv Fθ he
    ψ (deriv ψ) (fun x => (hψ.differentiable (by simp) x).hasDerivAt) hdc
    (max C 0) (le_max_right _ _) (fun x => (hC x).trans (le_max_left C 0)) hexchange

end Asakura.Chapter12
