import Chapter4EulerIntegralEquation
import Chapter4StepDriftPath
import Chapter4VectorPaths

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter4
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete
set_option maxHeartbeats 4200000
set_option backward.isDefEq.respectTransparency false

/-- The finite Euler interpolation is an actual adapted continuous random
path with finite L2 supremum norm. No uniform-in-n estimate is assumed. -/
theorem euler_interpolation_path_memLp
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
    (n : ℕ) (hnT : (((n:ℝ)*h : ℝ):EReal)<T) :
    ∃ V : Ω → C(Icc (0:ℝ) ((n:ℝ)*h),Fin dim → ℝ),
      Measurable[m] V ∧ MemLp V 2 P ∧
      (∀ r,Measurable[F (realTimeClamp r.val)] (fun w => V w r)) ∧
      (∀ w r,V w r=eulerInterpolation μ σ (fun j r => W j (realTimeClamp r)) ξ h n r.val w) := by
  classical
  let R := (n:ℝ)*h
  let Wr := fun j r => W j (realTimeClamp r)
  let Y := eulerGrid μ σ Wr ξ h
  obtain ⟨N,hN2,hN,hNI,hEq⟩ := euler_interpolation_ito_equation P hT F hF hle hnull W A hW hA hclock
    μ σ L hL hμ hσ ξ hξa hξ h hh n hnT
  have hR : 0≤R := by dsimp only [R];positivity
  have hY := euler_grid_adapted_memLp P hT F hF hle hnull W A hW hA hclock μ σ L hL hμ hσ ξ hξa hξ h hh
  have hkT k (hk : k∈Finset.range n) : (((k:ℝ)*h : ℝ):EReal)<T := by
    apply lt_of_le_of_lt _ hnT
    apply EReal.coe_le_coe
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast (Finset.mem_range.mp hk).le) hh
  let Pn := fun i j => finiteRealPath (N i j) R
    (fun w => (hN2 i j).path w |>.comp (continuous_const.min continuous_id))
  have hPnm i j : Measurable[m] (Pn i j) := finite_real_path_measurable F hle (N i j) R hnT _
    (fun t _ => (hN2 i j).adapted t)
  have hPni i j : MemLp (Pn i j) 2 P := m2_finite_path_memLp P F hF hle (N i j) (hN2 i j) R hnT _
  let G := fun k i w => μ i (Y k w)
  have hGa k (hk : k∈Finset.range n) i : Measurable[F (realTimeClamp ((k:ℝ)*h))] (G k i) :=
    (Vector.coordinate_continuous_of_square_lipschitz (μ i) L hL (hμ i)).measurable.comp (hY k (hkT k hk)).1
  have hGi k (hk : k∈Finset.range n) i : MemLp (G k i) 2 P :=
    square_lipschitz_coefficient_memLp P (μ i) L hL (hμ i) (Y k) (hY k (hkT k hk)).2
  let D := fun i w => ContinuousMap.const (Icc (0:ℝ) R) (ξ w i)+
    (∑ k∈Finset.range n,G k i w • stepTimePath ((k:ℝ)*h) (((k:ℝ)+1)*h) R)+∑ j,Pn i j w
  have hξm i : Measurable[m] (fun w => ξ w i) := (measurable_pi_apply i).comp (hξa.mono (hle ⊥) le_rfl)
  have hDm i : Measurable[m] (D i) := by
    apply Measurable.add
    · apply Measurable.add
      · exact ContinuousMap.measurable_iff_eval.mpr (fun _ => hξm i)
      · exact Finset.measurable_sum _ fun k hk => random_step_path_measurable (G k i)
          ((hGa k hk i).mono (hle _) le_rfl) _ _ R
    · exact Finset.measurable_sum _ fun j _ => hPnm i j
  have hDi i : MemLp (D i) 2 P := by
    let C0 := fun w => ContinuousMap.const (Icc (0:ℝ) R) (ξ w i)
    let S1 := fun w => ∑ k∈Finset.range n,G k i w • stepTimePath ((k:ℝ)*h) (((k:ℝ)+1)*h) R
    let S2 := fun w => ∑ j,Pn i j w
    have h0 : MemLp C0 2 P := constant_path_memLp (D:=Icc (0:ℝ) R) P (fun w => ξ w i) (hξm i) 2 (memLp_pi_iff.mp hξ i)
    have hd : MemLp S1 2 P :=
      memLp_finsetSum (p := (2 : ℝ≥0∞)) (μ := P)
        (f := fun k w => G k i w • stepTimePath ((k:ℝ)*h) (((k:ℝ)+1)*h) R)
        (Finset.range n) (fun k hk => scalar_random_path_memLp P (G k i) (hGi k hk i) (stepTimePath ((k:ℝ)*h) (((k:ℝ)+1)*h) R))
    have hz : MemLp S2 2 P :=
      memLp_finsetSum (p := (2 : ℝ≥0∞)) (μ := P) (f := fun j => Pn i j)
        Finset.univ (fun j _ => hPni i j)
    have ha : MemLp (fun w => C0 w+S1 w) 2 P := MemLp.add (f:=C0) (g:=S1) h0 hd
    exact MemLp.add (f:=fun w => C0 w+S1 w) (g:=S2) ha hz
  let V := fun w => bundleRealPaths (fun i => D i w)
  refine ⟨V,bundle_path_measurable D hDm,bundle_path_memLp P D hDm hDi,?_,?_⟩
  · intro r
    letI : MeasurableSpace Ω := F (realTimeClamp r.val)
    apply measurable_pi_iff.mpr
    intro i
    change Measurable (fun w => (D i w) r)
    dsimp only [D]
    simp only [ContinuousMap.add_apply,ContinuousMap.const_apply,ContinuousMap.sum_apply,ContinuousMap.smul_apply,
      stepTimePath,ContinuousMap.coe_mk,smul_eq_mul,Pn,finiteRealPath]
    apply Measurable.add
    · apply Measurable.add
      · exact (measurable_pi_apply i).comp (hξa.mono (hF bot_le) le_rfl)
      · exact Finset.measurable_sum _ fun k hk => step_drift_adapted F hF _ _ _ (by nlinarith) (G k i) (hGa k hk i)
    · exact Finset.measurable_sum _ fun j _ => (hN2 i j).adapted _
  · intro w r
    ext i
    change (D i w) r=_
    have he := hEq w r.val r.property.1 i
    have hi (k : ℕ) : IntervalIntegrable (fun a => (Ioc ((k:ℝ)*h) (((k:ℝ)+1)*h)).indicator (fun _ => μ i (Y k w)) a) volume 0 r.val :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le r.property.1).mpr ((integrable_const _).indicator measurableSet_Ioc)
    rw [intervalIntegral.integral_finsetSum (fun k _ => hi k)] at he
    have ht (k : ℕ) := interval_indicator_constant_integral ((k:ℝ)*h) (((k:ℝ)+1)*h) r.val
      (μ i (Y k w)) (by positivity) (by nlinarith) r.property.1
    simp_rw [ht] at he
    simpa only [D,G,ContinuousMap.add_apply,ContinuousMap.const_apply,ContinuousMap.sum_apply,ContinuousMap.smul_apply,
      stepTimePath,ContinuousMap.coe_mk,smul_eq_mul,Pn,finiteRealPath] using he.symm

end Asakura.Chapter4
