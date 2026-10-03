import Chapter12ConcreteCylinderOperator

open MeasureTheory
open scoped BigOperators RealInnerProductSpace
namespace Asakura.Chapter12
set_option maxHeartbeats 1400000

theorem scalar_linear_coordinate_sum {N:ℕ} (L:(Fin N → ℝ) →L[ℝ] ℝ) (z:Fin N → ℝ) :
    ∑i,L (Pi.single i 1)*z i=L z := by
  classical
  have hz:(∑i,z i • (Pi.single i 1:Fin N → ℝ))=z := by
    ext j
    simp [Pi.single_apply]
  rw [←hz,map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [map_smul,smul_eq_mul]
  simp only [hz]
  ring

theorem cylinder_gradient_direction {Ω H:Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (P:Measure Ω) (W:H →ₗᵢ[ℝ] Lp ℝ 2 P) (c:SmoothCylinder H) (w:Ω) (u:H) :
    inner ℝ (c.gradient P W w) u=
      c.df (fun j => W (c.direction j) w) (fun j => inner ℝ (c.direction j) u) := by
  rw [SmoothCylinder.gradient,sum_inner]
  simp only [real_inner_smul_left]
  exact scalar_linear_coordinate_sum _ _
end Asakura.Chapter12
#print axioms Asakura.Chapter12.cylinder_gradient_direction
