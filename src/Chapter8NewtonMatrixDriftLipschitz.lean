import Chapter8PhaseLinearEquiv
import Chapter8LipschitzGrowthData

open scoped BigOperators NNReal
namespace Asakura.Chapter8
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

/-- The physical phase drift is globally Lipschitz whenever the force is;
this supplies finite-time SDE moments without any extra manuscript assumption. -/
theorem newton_matrix_drift_lipschitz {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (e : (Fin d → ℝ) ≃L[ℝ] E) (g : E → E) (K : ℝ≥0) (hg : LipschitzWith K g) (Γ : E →L[ℝ] E) :
    ∃ L : ℝ,0≤L ∧ ∀ x y : Fin (d+d) → ℝ,
      (∑ i,((Fin.addCases (fun j z => velocityProjection d z j)
        (fun j z => e.symm (-g (e (positionProjection d z))-Γ (e (velocityProjection d z))) j) i x)-
        (Fin.addCases (fun j z => velocityProjection d z j)
        (fun j z => e.symm (-g (e (positionProjection d z))-Γ (e (velocityProjection d z))) j) i y))^2)≤L*∑ i,(x i-y i)^2 := by
  let A := phaseLinearEquiv e
  let f := fun z : E × E => (z.2,-g z.1-Γ z.2)
  have hf : LipschitzWith (max 1 (K+‖Γ‖₊)) f := by
    simpa only [mul_one,f,Function.comp_def,Pi.neg_apply] using LipschitzWith.prod_snd.prodMk (((hg.comp LipschitzWith.prod_fst).neg).sub
      (Γ.lipschitz.comp LipschitzWith.prod_snd))
  have hcomp := A.symm.toContinuousLinearMap.lipschitz.comp (hf.comp A.toContinuousLinearMap.lipschitz)
  let b := fun z => A.symm (f (A z))
  have hb : LipschitzWith (‖A.symm.toContinuousLinearMap‖₊*((max 1 (K+‖Γ‖₊))*‖A.toContinuousLinearMap‖₊)) b := hcomp
  let C := ‖A.symm.toContinuousLinearMap‖₊*((max 1 (K+‖Γ‖₊))*‖A.toContinuousLinearMap‖₊)
  refine ⟨((d+d:ℕ):ℝ)*(C:ℝ)^2,by positivity,?_⟩
  intro x y
  have he (z : Fin (d+d) → ℝ) (i : Fin (d+d)) : b z i=
      (Fin.addCases (motive := fun _ : Fin (d+d) => (Fin (d+d) → ℝ) → ℝ)
        (fun j z => velocityProjection d z j)
        (fun j z => e.symm (-g (e (positionProjection d z))-Γ (e (velocityProjection d z))) j) i z) := by
    change Fin.addCases (motive := fun _ : Fin (d+d) => ℝ) (e.symm (e (velocityProjection d z)))
      (e.symm (-g (e (positionProjection d z))-Γ (e (velocityProjection d z)))) i=_
    refine Fin.addCases ?_ ?_ i <;> intro j <;>
      simp only [Fin.addCases_left,Fin.addCases_right,e.symm_apply_apply]
  simpa only [he] using lipschitz_square_coordinates b C hb x y

end Asakura.Chapter8
