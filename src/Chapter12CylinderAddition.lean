import Chapter12CylinderCoordinateBlocks

open MeasureTheory
open scoped ContDiff
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

noncomputable def addSmoothCylinder {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (c d : SmoothCylinder H) : SmoothCylinder H :=
  smoothCylinderOfFunction (Fin.append c.direction d.direction)
    (fun z => c.f (cylinderLeftBlock c.dim d.dim z)+d.f (cylinderRightBlock c.dim d.dim z))
    ((c.smooth.comp (cylinderLeftBlock c.dim d.dim).contDiff).add
      (d.smooth.comp (cylinderRightBlock c.dim d.dim).contDiff))
    (iterated_polynomial_growth_add _ _
      (c.smooth.comp (cylinderLeftBlock c.dim d.dim).contDiff)
      (d.smooth.comp (cylinderRightBlock c.dim d.dim).contDiff)
      (iterated_polynomial_growth_comp_linear c.f c.smooth _ c.all_derivatives_growth)
      (iterated_polynomial_growth_comp_linear d.f d.smooth _ d.all_derivatives_growth))

theorem addSmoothCylinder_df {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (c d : SmoothCylinder H) (z : Fin (c.dim+d.dim) → ℝ) :
    (addSmoothCylinder c d).df z =
      (c.df (cylinderLeftBlock c.dim d.dim z)).comp (cylinderLeftBlock c.dim d.dim)+
      (d.df (cylinderRightBlock c.dim d.dim z)).comp (cylinderRightBlock c.dim d.dim) := by
  exact (((c.derivative _).comp z (cylinderLeftBlock c.dim d.dim).hasFDerivAt).add
    ((d.derivative _).comp z (cylinderRightBlock c.dim d.dim).hasFDerivAt)).fderiv

theorem addSmoothCylinder_value {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (P : Measure Ω) (W : H →ₗᵢ[ℝ] Lp ℝ 2 P) (c d : SmoothCylinder H) :
    (addSmoothCylinder c d).value P W = fun w => c.value P W w+d.value P W w := by
  funext w
  simp [SmoothCylinder.value,addSmoothCylinder,smoothCylinderOfFunction,
    cylinderLeftBlock,cylinderRightBlock,Fin.append_left,Fin.append_right]

theorem addSmoothCylinder_gradient {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (P : Measure Ω) (W : H →ₗᵢ[ℝ] Lp ℝ 2 P) (c d : SmoothCylinder H) :
    (addSmoothCylinder c d).gradient P W = fun w => c.gradient P W w+d.gradient P W w := by
  funext w
  unfold SmoothCylinder.gradient
  change (∑ j : Fin (c.dim+d.dim), (addSmoothCylinder c d).df
    (fun i => W (Fin.append c.direction d.direction i) w) (Pi.single j 1) •
      Fin.append c.direction d.direction j) = _
  rw [Fin.sum_univ_add]
  simp only [addSmoothCylinder_df,ContinuousLinearMap.add_apply,ContinuousLinearMap.comp_apply,
    cylinderLeftBlock_left,cylinderLeftBlock_right,cylinderRightBlock_left,cylinderRightBlock_right,
    map_zero,add_zero,zero_add,Fin.append_left,Fin.append_right]
  dsimp only [addSmoothCylinder,smoothCylinderOfFunction]
  simp only [cylinderLeftBlock_left,cylinderLeftBlock_right,cylinderRightBlock_left,
    cylinderRightBlock_right,map_zero,add_zero,zero_add]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro j _
  · simp [cylinderLeftBlock,Fin.append_left]
  · simp [cylinderRightBlock,Fin.append_right]

end Asakura.Chapter12
