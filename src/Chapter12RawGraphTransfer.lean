import Chapter12ScaleGraphRaw

open MeasureTheory
open scoped ENNReal
namespace Asakura.Chapter12

theorem derivative_graph_raw_ae_transfer {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (P : Measure Ω) (p : ℝ≥0∞) [Fact (1≤p)]
    (D : Lp ℝ p P →ₗ.[ℝ] Lp H p P)
    (F G : Ω → ℝ) (U V : Ω → H) (hF : MemLp F p P) (hU : MemLp U p P)
    (hg : (hF.toLp _,hU.toLp _) ∈ D.graph)
    (hFG : F =ᵐ[P] G) (hUV : U =ᵐ[P] V) :
    ∃ hG : MemLp G p P,∃ hV : MemLp V p P,(hG.toLp _,hV.toLp _) ∈ D.graph := by
  have hG := MemLp.ae_eq hFG hF
  have hV := MemLp.ae_eq hUV hU
  refine ⟨hG,hV,?_⟩
  have he : hG.toLp G=hF.toLp F := Lp.ext (hG.coeFn_toLp.trans (hF.coeFn_toLp.trans hFG).symm)
  have hv : hV.toLp V=hU.toLp U := Lp.ext (hV.coeFn_toLp.trans (hU.coeFn_toLp.trans hUV).symm)
  rw [he,hv]
  exact hg

end Asakura.Chapter12
