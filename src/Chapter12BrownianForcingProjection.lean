import Chapter12BrownianForcingFrames
import Chapter12LinearPolygonalCommutation

open Set
namespace Asakura.Chapter12
set_option maxHeartbeats 1800000

noncomputable def columnOperator {J E : Type*} [Fintype J]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (v : J → E) : (J → ℝ) →L[ℝ] E :=
  ∑j,(ContinuousLinearMap.proj j : (J → ℝ) →L[ℝ] ℝ).smulRight (v j)

theorem columnOperator_apply {J E : Type*} [Fintype J]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (v : J → E) (z : J → ℝ) :
    columnOperator v z=∑j,z j • v j := by simp [columnOperator]

theorem brownian_forcing_projection {Ω E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (d : ℕ) (T : ℝ) (hT : 0≤T) (B : BrownianTimeCoordinates d T → Ω → ℝ)
    (v : Fin (d+1) → E) (h : ℝ) (n : ℕ) (w : Ω) :
    brownianPolygonalForcing d T hT B v h n w=
      (columnOperator v).compLeftContinuous ℝ (Icc (0:ℝ) T)
        (polygonalCompact (fun s i => B (i,projIcc 0 T hT s) w) T h n) := by
  classical
  ext t
  simp only [brownianPolygonalForcing,ContinuousMap.sum_apply,ContinuousMap.coe_mk]
  change (∑i : Fin (d+1),polygonalPath (fun s => B (i,projIcc 0 T hT s) w) h n t.val • v i) = columnOperator v (polygonalPath (fun s i => B (i,projIcc 0 T hT s) w) h n t.val)
  rw [columnOperator_apply]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  exact (linear_polygonal_commutation (ContinuousLinearMap.proj i : (Fin (d+1) → ℝ) →L[ℝ] ℝ)
    (fun s i => B (i,projIcc 0 T hT s) w) h n t.val).symm
end Asakura.Chapter12
#print axioms Asakura.Chapter12.brownian_forcing_projection
