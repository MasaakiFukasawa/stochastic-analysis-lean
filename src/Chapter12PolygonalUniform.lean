import Chapter12InterpolationKernel
import Mathlib.Topology.UniformSpace.HeineCantor

open Set Filter
namespace Asakura.Chapter12
set_option maxHeartbeats 1200000

/-- The deterministic estimate underlying polygonal Brownian approximation. -/
theorem convex_interpolation_error {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x y z : E) (a e : ℝ) (ha : 0≤a) (ha1 : a≤1)
    (hx : ‖x-z‖≤e) (hy : ‖y-z‖≤e) :
    ‖(1-a) • x+a • y-z‖≤e := by
  have he : (1-a) • x+a • y-z=(1-a) • (x-z)+a • (y-z) := by module
  rw [he]
  calc
    _≤‖(1-a) • (x-z)‖+‖a • (y-z)‖ := norm_add_le _ _
    _=(1-a)*‖x-z‖+a*‖y-z‖ := by
      simp [norm_smul,Real.norm_eq_abs,abs_of_nonneg ha,abs_of_nonneg (sub_nonneg.mpr ha1)]
    _≤(1-a)*e+a*e := add_le_add
      (mul_le_mul_of_nonneg_left hx (sub_nonneg.mpr ha1)) (mul_le_mul_of_nonneg_left hy ha)
    _=e := by ring

/-- On a compact interval every continuous path has uniformly convergent
linear interpolants whenever the two endpoints approach the evaluation time
uniformly. This includes non-nested partitions. -/
theorem polygonal_uniform_convergence {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (T : ℝ) (f : Icc (0:ℝ) T → E) (hf : Continuous f)
    (l r : ℕ → Icc (0:ℝ) T → Icc (0:ℝ) T)
    (a : ℕ → Icc (0:ℝ) T → ℝ) (ha : ∀ n t,0≤a n t ∧ a n t≤1)
    (hl : TendstoUniformly l id atTop) (hr : TendstoUniformly r id atTop) :
    TendstoUniformly (fun n t => (1-a n t) • f (l n t)+a n t • f (r n t)) f atTop := by
  have hu := CompactSpace.uniformContinuous_of_continuous hf
  apply Metric.tendstoUniformly_iff.mpr
  intro e he
  obtain ⟨d,hd,hdu⟩ := Metric.uniformContinuous_iff.mp hu (e/2) (by linarith)
  filter_upwards [Metric.tendstoUniformly_iff.mp hl d hd,
    Metric.tendstoUniformly_iff.mp hr d hd] with n hn hm
  intro t
  have h1 : ‖f (l n t)-f t‖≤e/2 := by
    rw [← dist_eq_norm,dist_comm]
    exact (hdu (hn t)).le
  have h2 : ‖f (r n t)-f t‖≤e/2 := by
    rw [← dist_eq_norm,dist_comm]
    exact (hdu (hm t)).le
  rw [dist_comm,dist_eq_norm]
  exact (convex_interpolation_error _ _ _ _ _ (ha n t).1 (ha n t).2 h1 h2).trans_lt (by linarith)

end Asakura.Chapter12
