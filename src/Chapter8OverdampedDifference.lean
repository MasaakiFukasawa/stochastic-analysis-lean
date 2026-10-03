import Chapter8NewtonPositionFormula

open MeasureTheory
namespace Asakura.Chapter8
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

/-- The two equations use the same initial position and Brownian forcing;
they cancel exactly, leaving the force difference and the finite-mass remainder. -/
theorem overdamped_position_difference {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E]
    (M : E →L[ℝ] E) (Q X : ℝ → E) (g : E → E)
    (hQ : Continuous Q) (hX : Continuous X) (hg : Continuous g)
    (q W R : E) (t : ℝ)
    (hq : Q t=q-M (∫ s in 0..t,g (Q s))+M W+R)
    (hx : X t=q-M (∫ s in 0..t,g (X s))+M W) :
    Q t-X t=R+∫ s in 0..t,(-M) (g (Q s)-g (X s)) := by
  have hqi : IntervalIntegrable (fun s => g (Q s)) volume 0 t := (hg.comp hQ).intervalIntegrable 0 t (μ := volume)
  have hxi : IntervalIntegrable (fun s => g (X s)) volume 0 t := (hg.comp hX).intervalIntegrable 0 t (μ := volume)
  have hi : IntervalIntegrable (fun s => g (Q s)-g (X s)) volume 0 t := hqi.sub hxi
  have hc := (-M).intervalIntegral_comp_comm hi
  rw [hc,intervalIntegral.integral_sub hqi hxi,ContinuousLinearMap.neg_apply,map_sub,hq,hx]
  abel
end Asakura.Chapter8
