import Chapter4EulerErrorVolterra
import Chapter4EulerFinalBounds
import Chapter4VectorVolterraLimit

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter4
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete
set_option maxHeartbeats 3500000
set_option backward.isDefEq.respectTransparency false

noncomputable def eulerStrongStepConstant (R L K : ℝ) (dim noise : ℕ) : ℝ :=
  let c := (dim:ℝ)*(2*R+8*(noise:ℝ)^2)*(2*L)+1
  (c*R*Real.exp (c*R))*(2*(dim:ℝ)*(R+(noise:ℝ)^2)*K)*(1+eulerSecondMomentConstant R K dim noise)

lemma euler_strong_step_constant_nonneg (R L K : ℝ) (hR : 0≤R) (hL : 0≤L) (hK : 0≤K) (dim noise : ℕ) :
    0≤eulerStrongStepConstant R L K dim noise := by
  have hm := euler_second_moment_constant_nonneg R K hR hK dim noise
  unfold eulerStrongStepConstant
  positivity

/-- The grid recursion, interpolation, uniform moment estimate, local
increment bound, and final Gronwall argument are connected. -/
theorem euler_strong_error_finite
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
    (X : Ω → C(Icc (0:ℝ) ((n:ℝ)*h),Fin dim → ℝ))
    (hXm : Measurable[m] X) (hXi : MemLp X 2 P)

    (hXa : ∀ r,Measurable[F (realTimeClamp r.val)] (fun w => X w r))
    (NX : Fin dim → Fin noise → ClosedTime T → Ω → ℝ)
    (hNX : ∀ i j,LocalMProcessWitness P F (NX i j))
    (hXI : ∀ i j,ItoCovarianceFormula P F (W j)
      (fun z => σ i j (X z.1 (finitePrefixTime (T:=T) ((n:ℝ)*h) (mul_nonneg (Nat.cast_nonneg n) hh) (realTimeClamp z.2)))) (NX i j))
    (hXe : ∀ᵐ w ∂P,∀ r i,X w r i=ξ w i+
      (∫ s in 0..r.val,μ i (X w (projIcc 0 ((n:ℝ)*h) (mul_nonneg (Nat.cast_nonneg n) hh) s)))+
      ∑ j,NX i j (realTimeClamp r.val) w)
 :
    ∃ V : Ω → C(Icc (0:ℝ) ((n:ℝ)*h),Fin dim → ℝ),
      Measurable[m] V ∧ MemLp V 2 P ∧
      (∀ r,Measurable[F (realTimeClamp r.val)] (fun w => V w r)) ∧
      (∀ w r,V w r=eulerInterpolation μ σ (fun j r => W j (realTimeClamp r)) ξ h n r.val w) ∧
      (∫ w,‖X w-V w‖^2 ∂P)≤eulerStrongStepConstant ((n:ℝ)*h) L K dim noise*(1+∫ w,‖ξ w‖^2 ∂P)*h := by
  obtain ⟨V,hVm,hVi,hVa,hV,hVbound⟩ := euler_interpolation_uniform_second_moment P hT F hF hle hnull W A hW hA hclock
    μ σ L hL hμ hσ ξ hξa hξ h hh n hnT K hK hμg hσg
  refine ⟨V,hVm,hVi,hVa,hV,?_⟩
  let R := (n:ℝ)*h
  have hR : 0≤R := by dsimp only [R];positivity
  let D := (dim:ℝ)*(2*R+8*(noise:ℝ)^2)
  let c := D*(2*L)+1
  let Ccell := 2*(dim:ℝ)*(R+(noise:ℝ)^2)*K
  let M := ∫ w,‖ξ w‖^2 ∂P
  let HV := ∫ w,‖V w‖^2 ∂P
  let B := Ccell*(1+HV)*h
  let q := fun r => ∫ w,‖Vector.prefixPath hR (X w-V w) r‖^2 ∂P
  have hq : Continuous q := Vector.prefix_square_moment_continuous P hR (fun w => X w-V w) (hXm.sub hVm) (hXi.sub hVi)
  have hq0 r : 0≤q r := integral_nonneg (fun w => sq_nonneg _)
  have hD : 0≤D := by dsimp only [D];positivity
  have hA0 : 0≤Ccell := by dsimp only [Ccell];positivity
  have hHV : 0≤HV := integral_nonneg (fun w => sq_nonneg _)
  have hM : 0≤M := integral_nonneg (fun w => sq_nonneg _)
  have hB : 0≤B := by dsimp only [B];positivity
  have hv := euler_moment_bound_linear_initial P R K hR hK ξ hξ HV hVbound
  have hineq t (ht : t∈Icc 0 R) : q t≤D*(∫ r in 0..t,2*L*(q r+B)) :=
    euler_actual_error_volterra P hT F hF hle hnull W A hW hA hclock μ σ L hL hμ hσ ξ hξa hξ h hh n hnT
      K hK hμg hσg V hVm hVi hV X hXm hXi hXa NX hNX hXI hXe t ht
  have hb := euler_volterra_final_bound q R D L B hR hD hL hB hq hq0 hineq
  have hlin : 1+HV≤(1+eulerSecondMomentConstant R K dim noise)*(1+M) := by nlinarith only [hv,hM]
  have hscaled := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlin hA0) hh
  have hf : 0≤c*R*Real.exp (c*R) := by dsimp only [c];positivity
  have hfinal := hb.trans (mul_le_mul_of_nonneg_left hscaled hf)
  simp only [q,Vector.prefix_path_endpoint] at hfinal
  convert hfinal using 1 <;> dsimp only [eulerStrongStepConstant,D,c,Ccell,B,M,HV] <;> ring

end Asakura.Chapter4
