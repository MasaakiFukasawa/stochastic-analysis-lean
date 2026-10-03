import Chapter12PiIsometry

open scoped ENNReal
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false

noncomputable def finitePiInjection {ι E : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (i : ι) : E →L[ℝ] PiLp 2 (fun _ : ι => E) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι => E)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun j => if j=i then ContinuousLinearMap.id ℝ E else 0))

theorem finitePiInjection_apply {ι E : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (i j : ι) (u : E) :
    finitePiInjection i u j=if j=i then u else 0 := by
  by_cases h : j=i <;> simp [finitePiInjection,h]

end Asakura.Chapter12
