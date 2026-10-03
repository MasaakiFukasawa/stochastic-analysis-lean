import Chapter6BrownianStepIntegral
import Chapter6ItoTerminalErrorBound
import Chapter6UniformStepRandomEnergy
import Chapter4ContinuousStepDomain

open MeasureTheory Set Filter Finset
open scoped Topology BigOperators ENNReal
namespace Asakura.Chapter6
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter7
set_option maxHeartbeats 4200000
set_option backward.isDefEq.respectTransparency false

/-- Actual uniform left-endpoint sums converge in mean square to the
constructed Ito integral of a bounded continuous adapted coefficient. -/
theorem continuous_ito_grid_random_square_limit {Ω : Type*} {m : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (B : BrownianSystem P d) (j : Fin d)
    (H N : HalfClosedTime → Ω → ℝ)
    (hHa : ∀ t,Measurable[B.F t] (H t)) (hHc : ∀ w,Continuous (fun t => H t w))
    (hN : LocalMProcessWitness P B.F N)
    (hNI : ItoCovarianceFormula P B.F (B.W j) (fun z => H (realTimeClamp z.2) z.1) N)
    (R : ℝ) (hR : 0<R) (K : Ω → ℝ) (hK : MemLp K 2 P)
    (hHb : ∀ w r,r∈Icc 0 R → |H (realTimeClamp r) w|≤K w) :
    let S := fun n w => ∑ k∈range (n+1),H (realTimeClamp ((k:ℝ)*(R/(n+1)))) w*
      (B.W j (realTimeClamp (((k:ℝ)+1)*(R/(n+1)))) w-B.W j (realTimeClamp ((k:ℝ)*(R/(n+1)))) w)
    (∀ n,MemLp (fun w => N (realTimeClamp R) w-S n w) 2 P) ∧
    Tendsto (fun n => ∫ w,(N (realTimeClamp R) w-S n w)^2 ∂P) atTop (𝓝 0) := by
  let h := fun n : ℕ => R/((n:ℝ)+1)
  have hh n : 0<h n := div_pos hR (by positivity)
  have hend n : ((n+1:ℕ):ℝ)*h n=R := by dsimp [h]; push_cast; field_simp
  let G := fun (n k : ℕ) => H (realTimeClamp ((k:ℝ)*h n))
  have hGa n k (_ : k∈range (n+1)) : Measurable[B.F (realTimeClamp ((k:ℝ)*h n))] (G n k) := hHa _
  have hG2 n k (hk : k∈range (n+1)) : MemLp (G n k) 2 P := by
    apply hK.mono' (((hGa n k hk).mono (B.le _) le_rfl).aestronglyMeasurable)
    apply ae_of_all
    intro w
    rw [Real.norm_eq_abs]
    apply hHb
    refine ⟨mul_nonneg (Nat.cast_nonneg _) (hh n).le,?_⟩
    rw [←hend n]
    exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (mem_range.mp hk).le) (hh n).le
  let J := fun n t w => ∑ k∈range (n+1),G n k w*
    (B.W j (min (realTimeClamp (((k:ℝ)+1)*h n)) t) w-B.W j (min (realTimeClamp ((k:ℝ)*h n)) t) w)
  have hJ n := brownian_step_integral P B j (n+1) (h n) (hh n).le (G n) (hGa n) (hG2 n)
  let D := fun n (z : Ω × ℝ) => H (realTimeClamp z.2) z.1-uniformLeftStep R n (fun r => H (realTimeClamp r) z.1) z.2
  let E := fun n t w => N t w-J n t w
  have hHr w : Continuous (fun r => H (realTimeClamp r) w) := (hHc w).comp real_time_clamp_continuous
  have hHm : Measurable (fun z : Ω × ℝ => H (realTimeClamp z.2) z.1) := by
    have hm r : Measurable (H (realTimeClamp r)) := (hHa _).mono (B.le _) le_rfl
    simpa only [Function.comp_def,Function.uncurry_def,Prod.swap] using
      (measurable_uncurry_of_continuous_of_measurable hHr hm).comp measurable_swap
  obtain ⟨hD2,hDlim⟩ := uniform_step_random_energy_limit P R hR _ hHm (fun w => (hHr w).continuousOn) K hK hHb
  have hEp n : LocalMProcessWitness P B.F (E n) := by
    simpa only [E,J,sub_eq_add_neg,neg_one_mul] using hN.add P B.F B.mono B.le ((hJ n).2.1.smul P B.F (-1))
  have hEI n : ItoCovarianceFormula P B.F (B.W j) (D n) (E n) := by
    have hi := ItoCovarianceFormula.add_smul P B.F B.mono B.le (B.W j) (J n) N _ _ (hJ n).2.2.1 hNI (-1)
    simpa only [D,E,J,G,uniformLeftStep,h,Nat.cast_add,Nat.cast_one,neg_one_mul,sub_eq_neg_add] using hi
  have hDi n := continuous_minus_step_domain B.F B.mono B.le H hHa hHc (range (n+1))
    (fun k => (k:ℝ)*h n) (fun k => ((k:ℝ)+1)*h n) (G n) (hGa n)
  have hEi n := brownian_ito_terminal_square_bound P B j (E n) (D n) (hEp n) (hEI n)
    (by simpa only [D,uniformLeftStep,G,h,Nat.cast_add,Nat.cast_one] using (hDi n).1)
    (fun r hr => ae_of_all _ (fun w => by simpa only [D,uniformLeftStep,G,h,Nat.cast_add,Nat.cast_one] using (hDi n).2 w r hr))
    R hR.le (hD2 n)
  have hlim : Tendsto (fun n => ∫ w,(E n (realTimeClamp R) w)^2 ∂P) atTop (𝓝 0) := by
    apply squeeze_zero (fun _ => integral_nonneg (fun _ => sq_nonneg _)) (fun n => (hEi n).2)
    simpa using hDlim.const_mul 4
  have he n w : J n (realTimeClamp R) w =
      ∑ k∈range (n+1),H (realTimeClamp ((k:ℝ)*(R/(n+1)))) w*
        (B.W j (realTimeClamp (((k:ℝ)+1)*(R/(n+1)))) w-B.W j (realTimeClamp ((k:ℝ)*(R/(n+1)))) w) := by
    have hx := (hJ n).2.2.2 w
    rw [hend n] at hx
    simpa only [J,G,h,Nat.cast_add,Nat.cast_one] using hx
  refine ⟨?_,?_⟩
  · intro n
    simpa only [E,he] using (hEi n).1
  · simpa only [E,he] using hlim

end Asakura.Chapter6
