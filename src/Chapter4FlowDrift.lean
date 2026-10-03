import Chapter4FlowDerivative

open MeasureTheory Set Filter
open scoped Topology
namespace Asakura.Chapter4
open Asakura.Chapter5
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

lemma flow_second_derivative
    (φ : (Fin 2 → ℝ) → ℝ) (hφ : ContDiff ℝ 2 φ) (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f)
    (hflow : ∀ x y,fderiv ℝ φ ![x,y] (Pi.single 0 1)=f (φ ![x,y])) (x y : ℝ) :
    fderiv ℝ (fderiv ℝ φ) ![x,y] (Pi.single 0 1) (Pi.single 0 1)=
      deriv f (φ ![x,y])*f (φ ![x,y]) := by
  have hd := fin2_partial_time_derivative φ hφ x y 0
  have he : (fun r => fderiv ℝ φ ![r,y] (Pi.single 0 1))=(fun r => f (φ ![r,y])) :=
    funext (fun r => hflow r y)
  rw [he] at hd
  have hx := ((hφ.differentiable (by norm_num)) ![x,y]).hasFDerivAt.comp_hasDerivAt x
    (fin2_time_slice_derivative x y)
  rw [hflow x y] at hx
  exact hd.unique (((hf.differentiable (by norm_num)) _).hasDerivAt.comp x hx)

/-- The random ODE's denominator cannot vanish; along any continuous pair
of paths its right-hand side is continuous, and the chain-rule drift cancels
exactly to g. -/
theorem flow_drift_continuous_and_cancellation
    (φ : (Fin 2 → ℝ) → ℝ) (hφ : ContDiff ℝ 2 φ) (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f)
    (hflow : ∀ x y,fderiv ℝ φ ![x,y] (Pi.single 0 1)=f (φ ![x,y]))
    (hinit : ∀ y,φ ![0,y]=y) (g : ℝ → ℝ) (hg : Continuous g) :
    Continuous (fun z : Fin 2 → ℝ => g (φ z)/fderiv ℝ φ z (Pi.single 1 1)) ∧
      ∀ z : Fin 2 → ℝ, fderiv ℝ φ z (Pi.single 1 1)*
        (g (φ z)/fderiv ℝ φ z (Pi.single 1 1))=g (φ z) := by
  have hn z : fderiv ℝ φ z (Pi.single 1 1)≠0 := by
    have hz : z=![z 0,z 1] := by ext i; fin_cases i <;> rfl
    rw [hz]
    exact (flow_initial_derivative_positive φ hφ f hf hflow hinit _ _).2.ne'
  refine ⟨(hg.comp hφ.continuous).div
    ((hφ.continuous_fderiv (by norm_num)).clm_apply continuous_const) hn,?_⟩
  intro z
  field_simp [hn z]

end Asakura.Chapter4
