import Chapter12VectorPolygonalLp
import Mathlib.MeasureTheory.Function.LpSpace.Complete

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter12
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

theorem compact_polygonal_Lp {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E]
    (P : Measure Ω) [IsFiniteMeasure P] (T : ℝ) (hT : 0≤T)
    (X : Ω → C(Icc (0:ℝ) T,E)) (hXm : Measurable X)
    (n : ℕ → ℕ) (h : ℕ → ℝ) (hn : ∀i,0<n i) (hh : ∀i,0<h i)
    (hnT : ∀i,(n i:ℝ)*h i=T) (hlim : Tendsto h atTop (𝓝 0))
    (p : ℝ≥0∞) [Fact (1≤p)] (hp : p≠⊤) (hX : MemLp X p P) :
    ∃V : ℕ → Lp C(Icc (0:ℝ) T,E) p P,
      (∀i,(V i : Ω → C(Icc (0:ℝ) T,E))=ᵐ[P]
        (fun w => polygonalCompact (fun s => X w (projIcc 0 T hT s)) T (h i) (n i))) ∧
      Tendsto V atTop (𝓝 (hX.toLp X)) := by
  let f := fun s w => X w (projIcc 0 T hT s)
  have hfm s : Measurable (f s) := (ContinuousMap.measurable_eval _).comp hXm
  have he w (t : Icc (0:ℝ) T) : X w t=f t w := by
    dsimp only [f]
    rw [projIcc_of_mem hT t.property]
  let Q := fun i w => polygonalCompact (f · w) T (h i) (n i)
  have hQ i : MemLp (Q i) p P := hX.of_le
    (polygonalCompact_measurable_vector f hfm T (h i) (n i)).aestronglyMeasurable
    (ae_of_all _ (fun w => constructed_polygonal_norm_bound (f · w) T (h i) (hh i)
      (n i) (hn i) (hnT i) (X w) (he w)))
  refine ⟨fun i => (hQ i).toLp (Q i),fun i => (hQ i).coeFn_toLp,?_⟩
  apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' Q (fun i => hQ i) X hX).mpr
  exact constructed_polygonal_Lp_vector P f hfm T X he h n hh hn hnT hlim p (Fact.out : 1≤p) hp hX
end Asakura.Chapter12
#print axioms Asakura.Chapter12.compact_polygonal_Lp
