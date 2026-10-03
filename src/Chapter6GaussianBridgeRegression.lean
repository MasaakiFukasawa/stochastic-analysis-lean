import Chapter6WeightedConditionalRegression

open MeasureTheory ProbabilityTheory Set Filter Finset
open scoped Topology BigOperators
namespace Asakura.Chapter6
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

/-- Gaussian regression for a grid increment conditioned on the
intermediate Brownian point and the final point, including all coordinates. -/
theorem gaussian_bridge_increment_regression {Ω ι : Type*} {m : MeasurableSpace Ω}
    [Fintype ι] [DecidableEq ι] (P : Measure Ω)
    (X : Ω → ℝ) (Y : Ω → (Bool × ι) → ℝ) (j : ι)
    (hXY : HasGaussianLaw (fun w => (X w,Y w)) P)
    (hXm : Measurable X) (hYm : Measurable Y)
    (s t h : ℝ) (hst : s<t) (hX0 : ∫ w,X w ∂P=0) (hY0 : ∀ k,∫ w,Y w k ∂P=0)
    (hYY : ∀ p q,cov[(fun w => Y w p),(fun w => Y w q);P]=
      if p.2=q.2 then (if p.1 && q.1 then t else s) else 0)
    (hXYc : ∀ p,cov[X,(fun w => Y w p);P]=if p.1 && decide (p.2=j) then h else 0) :
    P[X|MeasurableSpace.comap Y inferInstance]=ᵐ[P]
      fun w => h/(t-s)*(Y w (true,j)-Y w (false,j)) := by
  let a := fun p : Bool × ι => if p.2=j then (if p.1 then h/(t-s) else -(h/(t-s))) else 0
  have hc q : cov[X,(fun w => Y w q);P]=∑ p,a p*cov[(fun w => Y w p),(fun w => Y w q);P] := by
    simp only [hXYc,hYY,a,Fintype.sum_prod_type]
    rcases q with ⟨b,k⟩
    cases b <;> by_cases hk : k=j
    · subst k
      simp
    · simp [hk,Ne.symm hk]
    · subst k
      simp
      field_simp [(sub_pos.mpr hst).ne']
      <;> ring
    · simp [hk,Ne.symm hk]
  have hr := finite_gaussian_regression_residual P hXY hXm hYm a hX0 hY0 hc
  convert hr using 1
  funext w
  simp [a,Fintype.sum_prod_type]
  ring

end Asakura.Chapter6
