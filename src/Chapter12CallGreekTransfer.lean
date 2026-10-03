import Chapter12MalliavinCallChain
import Chapter12GreekTransfer

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

/-- Greek transfer for the nonsmooth call payoff: the chain rule is
obtained by smoothing and closure; the only exceptional level is excluded
by the no-atom statement proved for the Asian average. -/
theorem call_greek_transfer {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [Nontrivial H] [CompleteSpace H]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : H →ₗᵢ[ℝ] Lp ℝ 2 P) (S : Set H) (hS : Dense S)
    (hcore : ∀ h ∈ S, HasLaw (W h : Ω → ℝ) (gaussianReal 0 ⟨‖h‖^2,sq_nonneg _⟩) P)
    (D : Lp ℝ 2 P →ₗ.[ℝ] Lp H 2 P) (hD : D.IsClosed)
    (hg : (D.graph : Set _) = closure (range (cylinderPair P W S hS hcore 2 (by simp))))
    (F Fθ : Ω → ℝ) (U v : Ω → H) (Z : Ω → ℝ)
    (hF : MemLp F 2 P) (hU : MemLp U 2 P) (hFU : (hF.toLp _,hU.toLp _) ∈ D.graph)
    (hv : MemLp v 2 P) (hZ : MemLp Z 2 P)
    (hd : IsDivergence D (hv.toLp _) (hZ.toLp _))
    (he : ∀ᵐ w ∂P, inner ℝ (U w) (v w) = Fθ w)
    (K : ℝ) (hno : P {w | F w = K} = 0) :
    (∫ w,(if K < F w then (1:ℝ) else 0)*Fθ w ∂P) =
      ∫ w,max (F w-K) 0*Z w ∂P := by
  have hn : P {w | hF.toLp F w = K} = 0 := by
    have hs : {w | hF.toLp F w = K} =ᵐ[P] {w | F w = K} := by
      filter_upwards [hF.coeFn_toLp] with w hw
      simp only [mem_setOf_eq,hw]
    rwa [measure_congr hs]
  obtain ⟨hi,hdi,hchain⟩ := closed_malliavin_call_chain P W S hS hcore 2 (by simp) D hD hg
    (hF.toLp _) (hU.toLp _) hFU K hn
  have hdir : ∀ᵐ w ∂P, inner ℝ (hU.toLp U w) (v w) = Fθ w := by
    filter_upwards [hU.coeFn_toLp,he] with w hw hh
    rwa [hw]
  have hh := greek_derivative_transfer P D (hF.toLp F) Fθ (hU.toLp U) v
    (fun x => max (x-K) 0) (fun x => if K < x then (1:ℝ) else 0) Z hi hdi hv hZ hchain hdir hd
  have hl : (∫ w,(if K < hF.toLp F w then (1:ℝ) else 0)*Fθ w ∂P) =
      ∫ w,(if K < F w then (1:ℝ) else 0)*Fθ w ∂P := by
    apply integral_congr_ae
    filter_upwards [hF.coeFn_toLp] with w hw
    rw [hw]
  have hr : (∫ w,max (hF.toLp F w-K) 0*Z w ∂P) =
      ∫ w,max (F w-K) 0*Z w ∂P := by
    apply integral_congr_ae
    filter_upwards [hF.coeFn_toLp] with w hw
    rw [hw]
  exact hl.symm.trans (hh.trans hr)

end Asakura.Chapter12
