import Chapter6BrownianBridgeRegression
import Chapter6VectorL2Regression

open MeasureTheory ProbabilityTheory Set Filter Finset
open scoped Topology BigOperators
namespace Asakura.Chapter6
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter7
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

theorem brownian_L2_weighted_grid_regression {Ω : Type*} {m : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] {d n : ℕ} (B : BrownianSystem P d)
    (h : ℝ) (hh : 0<h) (k : ℕ) (hk : k<n)
    (b : (Fin d → ℝ) → (Fin d → ℝ)) (hb : Measurable b)
    (hbound : ∀ i, MemLp (fun w => b (fun j => B.W j (realTimeClamp ((k:ℝ)*h)) w) i) 2 P) :
    let U := fun w i => B.W i (realTimeClamp ((k:ℝ)*h)) w
    let V := fun w i => B.W i (realTimeClamp ((n:ℝ)*h)) w
    P[(fun w => ∑ i,b (U w) i*(B.W i (realTimeClamp (((k:ℝ)+1)*h)) w-U w i))|MeasurableSpace.comap V inferInstance]=ᵐ[P]
      P[(fun w => ∑ i,b (U w) i*(h/((n:ℝ)*h-(k:ℝ)*h)*(V w i-U w i)))|MeasurableSpace.comap V inferInstance] := by
  let U := fun w i => B.W i (realTimeClamp ((k:ℝ)*h)) w
  let V := fun w i => B.W i (realTimeClamp ((n:ℝ)*h)) w
  let Y := fun w (p : Bool × Fin d) => B.W p.2 (realTimeClamp (if p.1 then (n:ℝ)*h else (k:ℝ)*h)) w
  let H := MeasurableSpace.comap Y inferInstance
  let G := MeasurableSpace.comap V inferInstance
  letI : MeasurableSpace Ω := m
  have hWa (i : Fin d) (a : ℕ) : Measurable (B.W i (realTimeClamp ((a:ℝ)*h))) :=
    ((B.martingale i).adapted P B.F _ (changed_time_finite _ (mul_nonneg (Nat.cast_nonneg a) hh.le))).mono (B.le _) le_rfl
  have hYm : Measurable Y := by
    apply measurable_pi_iff.mpr
    rintro ⟨a,i⟩
    cases a
    · exact hWa i k
    · exact hWa i n
  have hYH : Measurable[H] Y := Measurable.of_comap_le le_rfl
  have hUH : Measurable[H] U := by
    letI : MeasurableSpace Ω := H
    exact measurable_pi_iff.mpr (fun i => (measurable_pi_apply (false,i)).comp hYH)
  have hVH : Measurable[H] V := by
    letI : MeasurableSpace Ω := H
    exact measurable_pi_iff.mpr (fun i => (measurable_pi_apply (true,i)).comp hYH)
  have hGH : G≤H := hVH.comap_le
  have hH : H≤m := hYm.comap_le
  let times : Fin 3 × Fin d → ℕ := fun p => if p.1=0 then k else if p.1=1 then k+1 else n
  have ht p : times p≤n := by dsimp [times]; split_ifs <;> omega
  obtain ⟨hg,_,_⟩ := brownian_grid_samples_gaussian P B h hh.le times ht (fun p => p.2)
  have hXi i : MemLp (fun w => B.W i (realTimeClamp (((k:ℝ)+1)*h)) w-U w i) 2 P := by
    simpa [times,U,Nat.cast_add,Nat.cast_one,Pi.sub_def] using (hg.eval (1,i)).memLp_two.sub (hg.eval (0,i)).memLp_two
  have hYi i : MemLp (fun w => h/((n:ℝ)*h-(k:ℝ)*h)*(V w i-U w i)) 2 P := by
    simpa [times,U,V] using ((hg.eval (2,i)).memLp_two.sub (hg.eval (0,i)).memLp_two).const_mul (h/((n:ℝ)*h-(k:ℝ)*h))
  have hbi i : Measurable[H] (fun w => b (U w) i) := (measurable_pi_apply i).comp (hb.comp hUH)
  exact vector_L2_weighted_conditional_regression P _ _ _ hXi hYi G H hGH hH hbi hbound
    (fun i => brownian_bridge_grid_regression P B h hh k hk i)

end Asakura.Chapter6
