import Chapter4EulerCellGrowth
import Chapter4EulerPathMoment
import Chapter4PathEvaluationMoment

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter4
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

/-- Within-cell L2 error for the actual constructed Euler path. -/
theorem euler_interpolation_cell_moment
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0≤T)] (hT : 0<T) {dim noise : ℕ}
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
    (V : Ω → C(Icc (0:ℝ) ((n:ℝ)*h),Fin dim → ℝ))
    (hVm : Measurable[m] V) (hVi : MemLp V 2 P)
    (hV : ∀ w r,V w r=eulerInterpolation μ σ (fun j r => W j (realTimeClamp r)) ξ h n r.val w)
    (k : ℕ) (hk : k<n) (r : Icc (0:ℝ) ((n:ℝ)*h))
    (hr : r.val∈Icc ((k:ℝ)*h) (((k:ℝ)+1)*h)) :
    let Y := eulerGrid μ σ (fun j r => W j (realTimeClamp r)) ξ h
    MemLp (fun w => V w r-Y k w) 2 P ∧
    (∫ w,‖V w r-Y k w‖^2 ∂P)≤
      (2*(dim:ℝ)*((n:ℝ)*h+(noise:ℝ)^2)*K)*(1+∫ w,‖V w‖^2 ∂P)*h := by
  let Wr := fun j r => W j (realTimeClamp r)
  let Y := eulerGrid μ σ Wr ξ h
  have hkn : k+1≤n := hk
  have htk : (k:ℝ)*h∈Icc 0 ((n:ℝ)*h) :=
    ⟨by positivity,mul_le_mul_of_nonneg_right (by exact_mod_cast hk.le) hh⟩
  have hkT : (((k:ℝ)*h : ℝ):EReal)<T := (EReal.coe_le_coe htk.2).trans_lt hnT
  have hY := euler_grid_adapted_memLp P hT F hF hle hnull W A hW hA hclock μ σ L hL hμ hσ ξ hξa hξ h hh k hkT
  have hhR : h≤(n:ℝ)*h := by
    have hn : (1:ℝ)≤n := by exact_mod_cast (Nat.zero_le k |>.trans_lt hk)
    nlinarith
  have he : (fun w => V w r-Y k w)=fun w i => μ i (Y k w)*(r.val-(k:ℝ)*h)+
      ∑ j,σ i j (Y k w)*(W j (realTimeClamp r.val) w-W j (realTimeClamp ((k:ℝ)*h)) w) := by
    funext w i
    rw [hV,euler_interpolation_on_cell μ σ Wr ξ h hh n k hk r.val hr]
    simp only [Pi.sub_apply]
    dsimp only [Y,Wr]
    ring
  have hgrid : (fun w => V w ⟨(k:ℝ)*h,htk⟩)=Y k := by
    funext w
    rw [hV,euler_interpolation_past μ σ Wr ξ h hh k n hk.le _ le_rfl,euler_interpolation_grid μ σ Wr ξ h hh k]
  have hm := random_path_evaluation_square_moment P V hVm hVi ⟨(k:ℝ)*h,htk⟩
  simp_rw [show ∀ w,V w ⟨(k:ℝ)*h,htk⟩=Y k w from fun w => congrFun hgrid w] at hm
  have hb := brownian_cell_growth_bound P hT F hF hle hnull W A hW hA hclock
    r.val r.property.1 ((EReal.coe_le_coe r.property.2).trans_lt hnT) ((k:ℝ)*h) ⟨htk.1,hr.1⟩
    (Y k) hY.1 hY.2 μ σ L hL hμ hσ K hK hμg hσg ((n:ℝ)*h) h hh hhR (by linarith [hr.2])
  change MemLp (fun w => V w r-Y k w) 2 P ∧
    (∫ w,‖V w r-Y k w‖^2 ∂P)≤(2*(dim:ℝ)*((n:ℝ)*h+(noise:ℝ)^2)*K)*(1+∫ w,‖V w‖^2 ∂P)*h
  simp_rw [show ∀ w,V w r-Y k w=(fun i => μ i (Y k w)*(r.val-(k:ℝ)*h)+
      ∑ j,σ i j (Y k w)*(W j (realTimeClamp r.val) w-W j (realTimeClamp ((k:ℝ)*h)) w)) from fun w => congrFun he w]
  refine ⟨hb.1,hb.2.trans ?_⟩
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (add_le_add (le_refl (1:ℝ)) hm)
    (by positivity)) hh

end Asakura.Chapter4
