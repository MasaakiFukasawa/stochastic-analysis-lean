import Chapter12BrownianForcingProjection
import Chapter12CompactPolygonalLp
import Chapter12LpLipschitzComposition
import Chapter12ForcingPathLipschitz

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace Asakura.Chapter12
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

theorem brownian_forcing_solution_Lp {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P] (d : ℕ) (T : ℝ) (hT : 0≤T)
    (B : BrownianTimeCoordinates d T → Ω → ℝ)
    (Y : Ω → C(Icc (0:ℝ) T,Fin (d+1) → ℝ)) (hYm : Measurable Y)
    (hY : ∀w t i,Y w t i=B (i,t) w)
    (p : ℝ≥0∞) [Fact (1≤p)] (hp : p≠⊤) (hYp : MemLp Y p P)
    (v : Fin (d+1) → E) (x : E) (b : E → E) (K : ℝ≥0) (hb : LipschitzWith K b)
    (S : C(Icc (0:ℝ) T,E) → C(Icc (0:ℝ) T,E))
    (hSeq : ∀a t,S a t=a t+∫s in 0..t.val,b (S a (projIcc 0 T hT s)))
    (n : ℕ → ℕ) (h : ℕ → ℝ) (hn : ∀i,0<n i) (hh : ∀i,0<h i)
    (hnT : ∀i,(n i:ℝ)*h i=T) (hlim : Tendsto h atTop (𝓝 0)) :
    ∃V : ℕ → Lp C(Icc (0:ℝ) T,E) p P,∃Z : Lp C(Icc (0:ℝ) T,E) p P,
      (∀i,(V i : Ω → C(Icc (0:ℝ) T,E))=ᵐ[P]
        (fun w => S (ContinuousMap.const _ x+brownianPolygonalForcing d T hT B v (h i) (n i) w))) ∧
      (Z : Ω → C(Icc (0:ℝ) T,E))=ᵐ[P]
        (fun w => S (ContinuousMap.const _ x+(columnOperator v).compLeftContinuous ℝ (Icc (0:ℝ) T) (Y w))) ∧
      Tendsto V atTop (𝓝 Z) := by
  obtain ⟨Q,hQ,hlimQ⟩ := compact_polygonal_Lp P T hT Y hYm n h hn hh hnT hlim p hp hYp
  let L := (columnOperator v).compLeftContinuous ℝ (Icc (0:ℝ) T)
  let a := ContinuousMap.const (Icc (0:ℝ) T) x
  have ha : LipschitzWith ‖L‖₊ (fun q => a+L q) := by
    apply LipschitzWith.of_dist_le_mul
    intro q r
    simpa only [dist_add_left] using L.lipschitz.dist_le_mul q r
  have hs := forcing_path_lipschitz b K hb T hT S hSeq
  let g := fun q => S (a+L q)
  have hg : LipschitzWith (⟨Real.exp (((K:ℝ)+1)*T),(Real.exp_pos _).le⟩*‖L‖₊) g := hs.comp ha
  let A := finiteLpComposition P p g _ hg
  refine ⟨fun i => A (Q i),A (hYp.toLp Y),?_,?_,?_⟩
  · intro i
    filter_upwards [finiteLpComposition_coe P p g _ hg (Q i),hQ i] with w hw hqw
    rw [hw,hqw]
    dsimp only [g,a,L]
    rw [brownian_forcing_projection]
    have he : (fun s => Y w (projIcc 0 T hT s))=(fun s i => B (i,projIcc 0 T hT s) w) := by
      funext s j
      exact hY w (projIcc 0 T hT s) j
    rw [he]
  · filter_upwards [finiteLpComposition_coe P p g _ hg (hYp.toLp Y),hYp.coeFn_toLp] with w hw hyw
    rw [hw,hyw]
  · exact ((finiteLpComposition_continuous P p g _ hg).tendsto _).comp hlimQ
end Asakura.Chapter12
#print axioms Asakura.Chapter12.brownian_forcing_solution_Lp
