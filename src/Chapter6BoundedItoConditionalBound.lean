import Chapter6ContinuousItoGridLimit
import Chapter6FiniteSumL1Limit
import Chapter6BrownianBridgeSumBound
import Chapter6ConditionalBoundLimit

open MeasureTheory ProbabilityTheory Set Filter Finset
open scoped Topology BigOperators ENNReal
namespace Asakura.Chapter6
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter7
set_option maxHeartbeats 4200000
set_option backward.isDefEq.respectTransparency false

/-- The exact conditional estimate for the actual Ito integral, obtained
from Brownian regression, left-step approximation and L1 continuity. -/
theorem bounded_ito_conditional_bound {Ω : Type*} {m : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (B : BrownianSystem P d)
    (H N : Fin d → HalfClosedTime → Ω → ℝ)
    (hHa : ∀ j t,Measurable[B.F t] (H j t)) (hHc : ∀ j w,Continuous (fun t => H j t w))
    (hN : ∀ j,LocalMProcessWitness P B.F (N j))
    (hNI : ∀ j,ItoCovarianceFormula P B.F (B.W j) (fun z => H j (realTimeClamp z.2) z.1) (N j))
    (R : ℝ) (hR : 0<R) (b : ℝ → (Fin d → ℝ) → (Fin d → ℝ))
    (hb : ∀ r,Measurable (b r)) (K : ℝ) (hK : 0≤K)
    (hbb : ∀ r x,‖WithLp.toLp 2 (b r x)‖≤K)
    (hrep : ∀ j w r,r∈Icc 0 R → H j (realTimeClamp r) w=b r (fun i => B.W i (realTimeClamp r) w) j) :
    let V := fun w i => B.W i (realTimeClamp R) w
    let Z := fun w => ∑ j,N j (realTimeClamp R) w
    Integrable Z P ∧ ∀ᵐ w ∂P,|P[Z|MeasurableSpace.comap V inferInstance] w|
      ≤K*(‖WithLp.toLp 2 (V w)‖+2*Real.sqrt ((d:ℝ)*R)) := by
  let V := fun w i => B.W i (realTimeClamp R) w
  let Z := fun w => ∑ j,N j (realTimeClamp R) w
  let h := fun n : ℕ => R/((n:ℝ)+1)
  have hh n : 0<h n := div_pos hR (by positivity)
  have hend n : ((n+1:ℕ):ℝ)*h n=R := by dsimp [h]; push_cast; field_simp
  let Sj := fun n j w => ∑ k∈range (n+1),H j (realTimeClamp ((k:ℝ)*h n)) w*
      (B.W j (realTimeClamp (((k:ℝ)+1)*h n)) w-B.W j (realTimeClamp ((k:ℝ)*h n)) w)
  let S := fun n w => ∑ j,Sj n j w
  have hHbj j w r (hr : r∈Icc 0 R) : |H j (realTimeClamp r) w|≤K := by
    rw [hrep j w r hr]
    exact (PiLp.norm_apply_le (WithLp.toLp 2 (b r (fun i => B.W i (realTimeClamp r) w))) j).trans (hbb _ _)
  have hL j := continuous_ito_grid_square_limit P B j (H j) (N j) (hHa j) (hHc j) (hN j) (hNI j) R hR K hK (hHbj j)
  have hL' j : (∀ n,MemLp (fun w => N j (realTimeClamp R) w-Sj n j w) 2 P) ∧
      Tendsto (fun n => ∫ w,(N j (realTimeClamp R) w-Sj n j w)^2 ∂P) atTop (𝓝 0) := by
    simpa only [Sj,h,Nat.cast_add,Nat.cast_one] using hL j
  have hl := finite_sum_L1_limit P (fun n j w => N j (realTimeClamp R) w-Sj n j w)
    (fun n j => ((hL' j).1 n).integrable (by norm_num))
    (fun j => square_mean_zero_implies_L1_zero P _ (hL' j).1 (hL' j).2)
  have heS n w : S n w=∑ k∈range (n+1),∑ j,b ((k:ℝ)*h n) (fun i => B.W i (realTimeClamp ((k:ℝ)*h n)) w) j*
      (B.W j (realTimeClamp (((k:ℝ)+1)*h n)) w-B.W j (realTimeClamp ((k:ℝ)*h n)) w) := by
    dsimp [S,Sj]
    rw [sum_comm]
    apply sum_congr rfl
    intro k hk
    have hr : (k:ℝ)*h n∈Icc 0 R := by
      refine ⟨mul_nonneg (Nat.cast_nonneg _) (hh n).le,?_⟩
      rw [←hend n]
      exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (mem_range.mp hk).le) (hh n).le
    apply sum_congr rfl
    intro j _
    rw [hrep j w _ hr]
  have hgrid n := brownian_bridge_grid_sum_bound P B (Nat.succ_pos n) (h n) (hh n)
    (fun k => b ((k:ℝ)*h n)) (fun k => hb _) K hK (fun k x => hbb _ x)
  have hSi n : Integrable (S n) P := by
    rw [funext (heS n)]
    exact (hgrid n).1
  have hSb n : ∀ᵐ w ∂P,|P[S n|MeasurableSpace.comap V inferInstance] w|≤K*(‖WithLp.toLp 2 (V w)‖+2*Real.sqrt ((d:ℝ)*R)) := by
    have ht := (hgrid n).2
    rw [hend n,←funext (heS n)] at ht
    exact ht
  have hZi : Integrable Z P := by
    have hd := integrable_finsetSum univ (fun j _ => ((hL' j).1 0).integrable (by norm_num))
    have ha := hd.add (hSi 0)
    convert ha using 1
    funext w
    simp only [Z,S,sum_sub_distrib,Pi.add_apply,sub_add_cancel]
  have hgauss := (brownian_grid_samples_gaussian (n := 1) P B R hR.le
    (fun _ : Fin d => 1) (fun _ => le_rfl) id).1
  have hVg : HasGaussianLaw V P := by simpa only [Nat.cast_one,one_mul,id_eq] using hgauss
  have hVe : HasGaussianLaw (fun w => WithLp.toLp 2 (V w)) P :=
    hVg.map_equiv (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).symm
  have hKi : Integrable (fun w => K*(‖WithLp.toLp 2 (V w)‖+2*Real.sqrt ((d:ℝ)*R))) P :=
    (hVe.integrable.norm.add (integrable_const _)).const_mul K
  refine ⟨hZi,conditional_bound_L1_limit P (MeasurableSpace.comap V inferInstance) S Z _ hSi hZi hKi hSb ?_⟩
  simpa only [Z,S,sum_sub_distrib,Real.norm_eq_abs] using hl

end Asakura.Chapter6
