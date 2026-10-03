import Chapter12DivergenceDuality
import Mathlib.MeasureTheory.Function.L2Space

open MeasureTheory Filter
open scoped RealInnerProductSpace
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false

/-- The Greek transfer formula in the actual L2 spaces: the chain rule,
the direction equation and divergence duality move the payoff derivative
onto the weight. Parameter differentiation is a separate stated hypothesis. -/
theorem greek_derivative_transfer {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : Lp ℝ 2 P →ₗ.[ℝ] Lp H 2 P)
    (F Fθ : Ω → ℝ) (DF v : Ω → H) (ψ dψ : ℝ → ℝ) (δv : Ω → ℝ)
    (hψ : MemLp (fun w => ψ (F w)) 2 P)
    (hchainLp : MemLp (fun w => dψ (F w) • DF w) 2 P)
    (hv : MemLp v 2 P) (hδv : MemLp δv 2 P)
    (hchain : (hψ.toLp _,hchainLp.toLp _) ∈ D.graph)
    (hdirection : ∀ᵐ w ∂P, ⟪DF w,v w⟫ = Fθ w)
    (hdiv : IsDivergence D (hv.toLp _) (hδv.toLp _)) :
    (∫ w, dψ (F w)*Fθ w ∂P) = ∫ w, ψ (F w)*δv w ∂P := by
  obtain ⟨f,hf,hdf⟩ := D.mem_graph_iff.mp hchain
  have he := hdiv f
  rw [hf,hdf,L2.inner_def,L2.inner_def] at he
  have hl : (∫ w, ⟪hchainLp.toLp _ w,hv.toLp _ w⟫ ∂P) =
      ∫ w, dψ (F w)*Fθ w ∂P := by
    apply integral_congr_ae
    filter_upwards [hchainLp.coeFn_toLp,hv.coeFn_toLp,hdirection] with w h1 h2 h3
    rw [h1,h2,real_inner_smul_left,h3]
  have hr : (∫ w, inner ℝ (hψ.toLp _ w) (hδv.toLp _ w) ∂P) =
      ∫ w, ψ (F w)*δv w ∂P := by
    apply integral_congr_ae
    filter_upwards [hψ.coeFn_toLp,hδv.coeFn_toLp] with w h1 h2
    rw [h1,h2]
    exact mul_comm _ _
  exact hl.symm.trans (he.trans hr)

end Asakura.Chapter12
