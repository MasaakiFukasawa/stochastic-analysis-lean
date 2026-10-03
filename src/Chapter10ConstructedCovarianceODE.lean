import Chapter10CovarianceDerivative
import Chapter10OperatorCrossMoment

open MeasureTheory Set Filter Matrix
open scoped Topology BigOperators NNReal Matrix.Norms.Elementwise
namespace Asakura.Chapter10
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

/-- The actual state covariance is a continuous positive-semidefinite solution
of the Lyapunov ODE, derived from the original Brownian system. -/
theorem constructed_covariance_ode {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d n : ℕ} (B : BrownianSystem P n)
    (A : ℝ → (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)) (hA : Continuous A)
    (K : ℝ≥0) (hAK : ∀ t,‖A t‖≤K)
    (G : Fin d → Fin n → ℝ → ℝ) (hG : ∀ i j,Continuous (G i j))
    (ξ : Ω → Fin d → ℝ) (hξ : Measurable[B.F ⊥] ξ) (hξ2 : MemLp ξ 2 P)
    (T : ℝ) (hT : 0≤T) :
    ∃ (N : Fin d → Fin n → HalfClosedTime → Ω → ℝ)
      (X : Ω → C(Icc (0:ℝ) T,Fin d → ℝ)),LinearStateWitness P B A G ξ T hT N X ∧
      let V : ℝ → Matrix (Fin d) (Fin d) ℝ := fun t i j =>
        ∫ w,X w (projIcc 0 T hT t) i*X w (projIcc 0 T hT t) j ∂P
      let a : ℝ → Matrix (Fin d) (Fin d) ℝ := fun t i j => (A t (Pi.single j 1)) i
      let Q : ℝ → Matrix (Fin d) (Fin d) ℝ := fun t i j => ∑ k,G i k t*G j k t
      Continuous V ∧ (∀ t,(V t).PosSemidef) ∧
        V 0=(fun i j => ∫ w,ξ w i*ξ w j ∂P) ∧
        ∀ t∈Ico 0 T,HasDerivWithinAt V (a t*V t+V t*(a t).transpose+Q t) (Ici t) t := by
  letI : MeasurableSpace Ω := m
  obtain ⟨N,X,hState,hinit,he⟩ := constructed_covariance_equation P B A hA K hAK G hG ξ hξ hξ2 T hT
  let U := fun t w => X w (projIcc 0 T hT t)
  have hm t i : Measurable (fun w => U t w i) :=
    (measurable_pi_apply i).comp ((continuous_eval_const _).measurable.comp hState.measurable)
  have hi t i : MemLp (fun w => U t w i) 2 P := by
    apply hState.moment.norm.of_le (hm t i).aestronglyMeasurable
    exact ae_of_all _ fun w => by
      simpa only [norm_norm] using (norm_le_pi_norm (U t w) i).trans ((X w).norm_coe_le_norm _)
  have hc i w : Continuous (fun t => U t w i) :=
    (continuous_apply i).comp ((X w).continuous.comp continuous_projIcc)
  have hv i j : Continuous (fun t => ∫ w,U t w i*U t w j ∂P) := by
    apply continuousOn_univ.mp
    exact covariance_continuous_on P univ (fun t i w => U t w i)
      (fun t _ i => (hm t i).aestronglyMeasurable)
      (fun i => ae_of_all _ fun w => (hc i w).continuousOn)
      (fun w => ‖X w‖) hState.moment.norm (fun t _ i => ae_of_all _ fun w =>
        (norm_le_pi_norm _ i).trans ((X w).norm_coe_le_norm _)) i j
  refine ⟨N,X,hState,?_,?_,?_,?_⟩
  · exact continuous_pi (fun i => continuous_pi (fun j => hv i j))
  · intro t
    exact error_covariance_positive P (fun i w => U t w i) (hi t)
  · ext i j
    have hp : projIcc 0 T hT 0=⟨0,le_rfl,hT⟩ := Subtype.ext (by simp [projIcc,hT])
    apply integral_congr_ae
    filter_upwards [hinit] with w hw
    change X w ⟨0,le_rfl,hT⟩=ξ w at hw
    simp only [hp,hw]
  · intro t ht
    apply hasDerivWithinAt_pi.mpr
    intro i
    apply hasDerivWithinAt_pi.mpr
    intro j
    have hd := linear_covariance_derivative P T hT X hState.measurable hState.moment A hA K hAK i j
      (fun s => ∑ k,G i k s*G j k s)
      (continuous_finsetSum _ (fun k _ => (hG i k).mul (hG j k)))
      (∫ w,ξ w i*ξ w j ∂P) (he i j) t ht
    have hid := operator_covariance_drift P (U t) (hi t) (A t) i j
    dsimp only at hid
    dsimp only [U] at hid
    rw [hid] at hd
    exact hd

end Asakura.Chapter10
