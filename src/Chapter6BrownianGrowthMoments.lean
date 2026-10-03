import Chapter6BrownianBridgeRegression
import Chapter6GaussianGrowthMoments

open MeasureTheory ProbabilityTheory Set Filter Finset
open scoped Topology
namespace Asakura.Chapter6
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter7
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

theorem brownian_bridge_grid_growth_moments {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d n : ℕ} (B : BrownianSystem P d)
    (h : ℝ) (hh : 0<h) (k : ℕ) (hk : k<n)
    (b : (Fin d → ℝ) → Fin d → ℝ) (hb : Measurable b) (K : ℝ) (hK : 0≤K)
    (hbb : ∀ y,‖WithLp.toLp 2 (b y)‖≤K*(1+‖WithLp.toLp 2 y‖)) :
    let U := fun w i => B.W i (realTimeClamp ((k:ℝ)*h)) w
    let V := fun w i => B.W i (realTimeClamp ((n:ℝ)*h)) w
    (∀ᵐ w ∂P,P[(fun w => ‖WithLp.toLp 2 (b (U w))‖^2)|MeasurableSpace.comap V inferInstance] w
      ≤2*K^2*(3+2*(d:ℝ)*((n:ℝ)*h))*(1+‖WithLp.toLp 2 (V w)‖^2)) ∧
    (∀ᵐ w ∂P,P[(fun w => ‖WithLp.toLp 2 (V w-U w)‖^2)|MeasurableSpace.comap V inferInstance] w
      ≤(2/((n:ℝ)*h)+2*(d:ℝ))*(1+‖WithLp.toLp 2 (V w)‖^2)*((n:ℝ)*h-(k:ℝ)*h)) := by
  let U := fun w i => B.W i (realTimeClamp ((k:ℝ)*h)) w
  let V := fun w i => B.W i (realTimeClamp ((n:ℝ)*h)) w
  let times : Bool × Fin d → ℕ := fun p => if p.1 then n else k
  have ht p : times p≤n := by dsimp [times]; split_ifs <;> omega
  obtain ⟨hg,hm,hcov⟩ := brownian_grid_samples_gaussian P B h hh.le times ht (fun p => p.2)
  let LU : ((Bool × Fin d) → ℝ) →L[ℝ] (Fin d → ℝ) := ContinuousLinearMap.pi (fun i => ContinuousLinearMap.proj (false,i))
  let LV : ((Bool × Fin d) → ℝ) →L[ℝ] (Fin d → ℝ) := ContinuousLinearMap.pi (fun i => ContinuousLinearMap.proj (true,i))
  have hUV : HasGaussianLaw (fun w => (U w,V w)) P := hg.map (LU.prod LV)
  have hWa (i : Fin d) (a : ℕ) : Measurable (B.W i (realTimeClamp ((a:ℝ)*h))) :=
    ((B.martingale i).adapted P B.F _ (changed_time_finite _ (mul_nonneg (Nat.cast_nonneg a) hh.le))).mono (B.le _) le_rfl
  have hUm : Measurable U := measurable_pi_iff.mpr (fun i => hWa i k)
  have hVm : Measurable V := measurable_pi_iff.mpr (fun i => hWa i n)
  have hU0 i : (∫ w,U w i ∂P)=0 := hm (false,i)
  have hV0 i : (∫ w,V w i ∂P)=0 := hm (true,i)
  have hUU i j : cov[(fun w => U w i),(fun w => U w j);P]=if i=j then (k:ℝ)*h else 0 := by
    simpa [times,U] using hcov (false,i) (false,j)
  have hVV i j : cov[(fun w => V w i),(fun w => V w j);P]=if i=j then (n:ℝ)*h else 0 := by
    simpa [times,V] using hcov (true,i) (true,j)
  have hUVc i j : cov[(fun w => U w i),(fun w => V w j);P]=if i=j then (k:ℝ)*h else 0 := by
    simpa [times,U,V,min_eq_left hk.le] using hcov (false,i) (true,j)
  exact gaussian_bridge_linear_growth_moments P U V hUm hVm hUV ((k:ℝ)*h) ((n:ℝ)*h)
    (mul_nonneg (Nat.cast_nonneg k) hh.le) (mul_lt_mul_of_pos_right (Nat.cast_lt.mpr hk) hh)
    hU0 hV0 hUU hVV hUVc b hb K hK hbb

end Asakura.Chapter6
