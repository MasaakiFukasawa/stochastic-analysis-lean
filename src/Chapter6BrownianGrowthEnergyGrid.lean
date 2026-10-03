import Chapter6BrownianGrowthMoments
import Chapter6BrownianGrowthSquareIntegrable
import Chapter6ConditionalFiniteSumBound

open MeasureTheory ProbabilityTheory Set Filter Finset
open scoped Topology BigOperators
namespace Asakura.Chapter6
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter7
set_option maxHeartbeats 3200000
set_option backward.isDefEq.respectTransparency false

theorem brownian_growth_energy_grid_bound {Ω : Type*} {m : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] {d n : ℕ} (B : BrownianSystem P d)
    (h : ℝ) (hh : 0<h) (b : ℕ → (Fin d → ℝ) → Fin d → ℝ)
    (hb : ∀ k,Measurable (b k)) (K : ℝ) (hK : 0≤K)
    (hbb : ∀ k y,‖WithLp.toLp 2 (b k y)‖≤K*(1+‖WithLp.toLp 2 y‖)) :
    let V := fun w i => B.W i (realTimeClamp ((n:ℝ)*h)) w
    let S := fun w => ∑ k∈range n,h*∑ j,(b k (fun i => B.W i (realTimeClamp ((k:ℝ)*h)) w) j)^2
    Integrable S P ∧ ∀ᵐ w ∂P,|P[S|MeasurableSpace.comap V inferInstance] w|≤
      ((n:ℝ)*h)*(2*K^2*(3+2*(d:ℝ)*((n:ℝ)*h)))*(1+‖WithLp.toLp 2 (V w)‖^2) := by
  let V := fun w i => B.W i (realTimeClamp ((n:ℝ)*h)) w
  let G := MeasurableSpace.comap V inferInstance
  letI : MeasurableSpace Ω := m
  let E := fun k w => ∑ j,(b k (fun i => B.W i (realTimeClamp ((k:ℝ)*h)) w) j)^2
  let C := 2*K^2*(3+2*(d:ℝ)*((n:ℝ)*h))
  have hi k (hk : k∈range n) : Integrable (fun w => h*E k w) P :=
    (brownian_growth_grid_square_integrable P B h hh k (mem_range.mp hk) (b k) (hb k) K (hbb k)).const_mul h
  have hbound k (hk : k∈range n) : ∀ᵐ w ∂P,|P[(fun w => h*E k w)|G] w|≤h*C*(1+‖WithLp.toLp 2 (V w)‖^2) := by
    have hm := (brownian_bridge_grid_growth_moments P B h hh k (mem_range.mp hk) (b k) (hb k) K hK (hbb k)).1
    simp only [EuclideanSpace.real_norm_sq_eq,WithLp.ofLp_toLp] at hm
    have hn : 0≤ᵐ[P] P[E k|G] := condExp_nonneg (ae_of_all _ (fun w => sum_nonneg (fun j _ => sq_nonneg _)))
    have hs := condExp_smul (μ := P) h (E k) G
    filter_upwards [hm,hn,hs] with w hm hn hs
    change P[(fun w => h*E k w)|G] w=h*P[E k|G] w at hs
    rw [hs,abs_of_nonneg (mul_nonneg hh.le hn)]
    simpa only [C,V,EuclideanSpace.real_norm_sq_eq,mul_assoc] using mul_le_mul_of_nonneg_left hm hh.le
  have hs := conditional_finite_sum_abs_bound P n (fun k w => h*E k w)
    (fun _ w => h*C*(1+‖WithLp.toLp 2 (V w)‖^2)) hi G hbound
  refine ⟨integrable_finsetSum _ hi,?_⟩
  filter_upwards [hs] with w hw
  apply hw.trans_eq
  simp only [sum_const,card_range,nsmul_eq_mul,C,V]
  ring

end Asakura.Chapter6
