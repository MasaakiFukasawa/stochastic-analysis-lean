import Chapter12ClosedProductRaw

open MeasureTheory Set
open scoped ENNReal
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false

theorem scale_derivative_graph_raw {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (P : Measure Ω) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (D : Lp ℝ p P →ₗ.[ℝ] Lp H p P)
    (F : Ω → ℝ) (U : Ω → H) (hF : MemLp F p P) (hU : MemLp U p P)
    (hFU : (hF.toLp _,hU.toLp _) ∈ D.graph) (c : ℝ) :
    ∃ hi : MemLp (fun w => c*F w) p P,
    ∃ hdi : MemLp (fun w => c • U w) p P,
      (hi.toLp _,hdi.toLp _) ∈ D.graph := by
  have hi : MemLp (fun w => c*F w) p P := hF.const_mul c
  have hdi : MemLp (fun w => c • U w) p P := hU.const_smul c
  have hg := D.graph.smul_mem c hFU
  have hv : c • hF.toLp _ = hi.toLp _ := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_smul c (hF.toLp _),hF.coeFn_toLp,hi.coeFn_toLp] with w h1 h2 h3
    rw [h1,Pi.smul_apply,h2,h3]
    rfl
  have hu : c • hU.toLp _ = hdi.toLp _ := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_smul c (hU.toLp _),hU.coeFn_toLp,hdi.coeFn_toLp] with w h1 h2 h3
    rw [h1,Pi.smul_apply,h2,h3]
  refine ⟨hi,hdi,?_⟩
  change (c • hF.toLp _,c • hU.toLp _) ∈ D.graph at hg
  rwa [hv,hu] at hg

end Asakura.Chapter12
