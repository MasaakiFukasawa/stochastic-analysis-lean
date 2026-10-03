import Chapter4EulerStrongFinite
import Chapter4ClassicalSolutionData
import Chapter4VectorGlobalRestriction
import Chapter4VectorGlobalPowerMoment

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter4
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete
set_option maxHeartbeats 3500000
set_option backward.isDefEq.respectTransparency false

/-- Strong Euler error for any actual global SDE solution. Its finite-horizon
L2 path moment and clipped Ito equation are derived from the SDE data. -/
theorem euler_strong_error_global
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0≤T)] (hT : 0<T) (hTinf : T=⊤) {dim noise : ℕ}
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t E,MeasurableSet[m] E → P E=0 → MeasurableSet[F t] E)
    (W A : Fin noise → ClosedTime T → Ω → ℝ)
    (hW : ∀ j,LocalMProcessWitness P F (W j))
    (hA : ∀ j,LocalCovarianceWitness P F (W j) (W j) (A j))
    (hclock : ∀ j w (r : ℝ),0≤r → (r:EReal)<T → A j (realTimeClamp r) w=r)
    (μ : Fin dim → (Fin dim → ℝ) → ℝ) (σ : Fin dim → Fin noise → (Fin dim → ℝ) → ℝ)
    (L : ℝ) (hL : 0≤L)
    (hμ : ∀ i x y,(μ i x-μ i y)^2≤L*‖x-y‖^2)
    (hσ : ∀ i j x y,(σ i j x-σ i j y)^2≤L*‖x-y‖^2)
    (ξ : Ω → Fin dim → ℝ) (hξa : Measurable[F ⊥] ξ) (hξ : MemLp ξ 2 P)
    (h : ℝ) (hh : 0≤h)
    (n : ℕ) (hnT : (((n:ℝ)*h : ℝ):EReal)<T)
    (K : ℝ) (hK : 0≤K)
    (hμg : ∀ i x,(μ i x)^2≤K*(1+‖x‖^2))
    (hσg : ∀ i j x,(σ i j x)^2≤K*(1+‖x‖^2))

    (X : ClosedTime T → Ω → Fin dim → ℝ) (hX : VectorSDESolution P F W μ σ ξ X) :
    ∃ V : Ω → C(Icc (0:ℝ) ((n:ℝ)*h),Fin dim → ℝ),
      Measurable[m] V ∧ MemLp V 2 P ∧
      (∀ r,Measurable[F (realTimeClamp r.val)] (fun w => V w r)) ∧
      (∀ w r,V w r=eulerInterpolation μ σ (fun j r => W j (realTimeClamp r)) ξ h n r.val w) ∧
      (∫ w,‖Vector.realVectorPath X hX.path ((n:ℝ)*h) hnT w-V w‖^2 ∂P)≤
        eulerStrongStepConstant ((n:ℝ)*h) L K dim noise*(1+∫ w,‖ξ w‖^2 ∂P)*h := by
  let R := (n:ℝ)*h
  have hR : 0≤R := by dsimp only [R];positivity
  let Y := Vector.realVectorPath X hX.path R hnT
  have hYm : Measurable[m] Y := ContinuousMap.measurable_iff_eval.mpr (fun r =>
    (hX.adapted _ (real_time_below r.val r.property.1 ((EReal.coe_le_coe r.property.2).trans_lt hnT))).mono (hle _) le_rfl)
  have hYa r : Measurable[F (realTimeClamp r.val)] (fun w => Y w r) :=
    hX.adapted _ (real_time_below r.val r.property.1 ((EReal.coe_le_coe r.property.2).trans_lt hnT))
  have hμc i := Vector.coordinate_continuous_of_square_lipschitz (μ i) L hL (hμ i)
  have hσc i j := Vector.coordinate_continuous_of_square_lipschitz (σ i j) L hL (hσ i j)
  obtain ⟨N,hN,hNI,hNe⟩ := hX.integrals
  have hYi : MemLp Y 2 P := by
    simpa only [ENNReal.ofReal_ofNat] using
      Vector.global_sde_power_moment P hT hTinf F hF hle hnull W A hW hA hclock μ σ
        (fun i => (hμc i).measurable) (fun i j => (hσc i j).measurable) K hK hμg hσg
        2 (by norm_num) ξ (hξa.mono (hle ⊥) le_rfl) (by simpa using hξ) X hX.adapted hX.path N hN hNI hNe R hR hnT
  obtain ⟨J,hJ,hJI,hJe⟩ := Vector.global_sde_finite_restriction P hT F hF hle hnull W A hW hA hclock
    μ σ hσc ξ X hX.adapted hX.path N hN hNI hNe R hR hnT
  exact euler_strong_error_finite P hT F hF hle hnull W A hW hA hclock μ σ L hL hμ hσ ξ hξa hξ h hh n hnT
    K hK hμg hσg Y hYm hYi hYa J hJ hJI hJe

end Asakura.Chapter4
