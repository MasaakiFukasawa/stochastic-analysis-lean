import Chapter12BrownianForcingProjection

open MeasureTheory Set Filter
open scoped Topology
namespace Asakura.Chapter12
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

theorem brownian_forcing_path_convergence {Ω E:Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (d:ℕ) (T:ℝ) (hT:0≤T) (B:BrownianTimeCoordinates d T → Ω → ℝ)
    (Y:Ω → C(Icc (0:ℝ) T,Fin (d+1) → ℝ))
    (hY:∀w t i,Y w t i=B (i,t) w) (v:Fin (d+1) → E)
    (n:ℕ → ℕ) (h:ℕ → ℝ) (hn:∀i,0<n i) (hh:∀i,0<h i)
    (hnT:∀i,(n i:ℝ)*h i=T) (hl:Tendsto h atTop (𝓝 0)) (w:Ω) :
    Tendsto (fun i => brownianPolygonalForcing d T hT B v (h i) (n i) w) atTop
      (𝓝 ((columnOperator v).compLeftContinuous ℝ (Icc (0:ℝ) T) (Y w))) := by
  have he:∀t:Icc (0:ℝ) T,Y w t=(fun s i => B (i,projIcc 0 T hT s) w) t := by
    intro t
    ext i
    change Y w t i=B (i,projIcc 0 T hT t.val) w
    rw [projIcc_of_mem hT t.property,hY]
  have ht := constructed_polygonal_convergence (fun s i => B (i,projIcc 0 T hT s) w)
    T (Y w) he h n hh hn hnT hl
  have hv := (((columnOperator v).compLeftContinuous ℝ (Icc (0:ℝ) T)).continuous.tendsto (Y w)).comp ht
  simpa only [brownian_forcing_projection,Function.comp_def] using hv
end Asakura.Chapter12
#print axioms Asakura.Chapter12.brownian_forcing_path_convergence
