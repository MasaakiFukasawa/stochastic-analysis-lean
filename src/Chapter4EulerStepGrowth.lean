import Chapter4EulerInterpolationAlgebra
import Chapter4RunningNormPath

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter4
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false

lemma uniform_grid_interval_unique (h : ℝ) (hh : 0≤h) (k l : ℕ) (r : ℝ)
    (hk : r∈Ioc ((k:ℝ)*h) (((k:ℝ)+1)*h))
    (hl : r∈Ioc ((l:ℝ)*h) (((l:ℝ)+1)*h)) : k=l := by
  apply le_antisymm
  · by_contra hn
    have hn' : l+1≤k := Nat.lt_of_not_ge hn
    have hx : ((l:ℝ)+1)*h≤(k:ℝ)*h := mul_le_mul_of_nonneg_right (by exact_mod_cast hn') hh
    linarith [hk.1,hl.2]
  · by_contra hn
    have hn' : k+1≤l := Nat.lt_of_not_ge hn
    have hx : ((k:ℝ)+1)*h≤(l:ℝ)*h := mul_le_mul_of_nonneg_right (by exact_mod_cast hn') hh
    linarith [hl.1,hk.2]

lemma disjoint_grid_step_square_bound (h : ℝ) (hh : 0≤h) (n : ℕ)
    (G : ℕ → ℝ) (r B : ℝ) (hB : 0≤B)
    (hb : ∀ k∈Finset.range n,r∈Ioc ((k:ℝ)*h) (((k:ℝ)+1)*h) → (G k)^2≤B) :
    (∑ k∈Finset.range n,(Ioc ((k:ℝ)*h) (((k:ℝ)+1)*h)).indicator (fun _ => G k) r)^2≤B := by
  classical
  by_cases he : ∃ k∈Finset.range n,r∈Ioc ((k:ℝ)*h) (((k:ℝ)+1)*h)
  · obtain ⟨k,hk,hr⟩ := he
    rw [Finset.sum_eq_single k,indicator_of_mem hr]
    · exact hb k hk hr
    · intro l hl hlk
      apply indicator_of_notMem
      intro hr'
      exact hlk (uniform_grid_interval_unique h hh l k r hr' hr)
    · intro hkn
      exact (hkn hk).elim
  · have hzero : ∀ k∈Finset.range n,(Ioc ((k:ℝ)*h) (((k:ℝ)+1)*h)).indicator (fun _ => G k) r=0 := by
      intro k hk
      apply indicator_of_notMem
      exact fun hr => he ⟨k,hk,hr⟩
    simpa only [Finset.sum_eq_zero hzero,zero_pow (by decide : (2:ℕ)≠0)] using hB

lemma vector_value_le_prefix_norm {R : ℝ} (hR : 0≤R) {dim : ℕ}
    (Y : C(Icc (0:ℝ) R,Fin dim → ℝ)) (s : Icc (0:ℝ) R)
    (r : ℝ) (hr : r∈Icc 0 R) (hsr : s.val≤r) :
    ‖Y s‖≤‖prefixPath hR (normEnvelope Y) r‖ := by
  have hh := (prefixPath hR (normEnvelope Y) r).norm_coe_le_norm s
  change ‖‖Y (min s (projIcc 0 R hR r))‖‖≤_ at hh
  simpa only [projIcc_of_mem hR hr,min_eq_left (show s≤(⟨r,hr⟩ : Icc 0 R) from hsr),norm_norm] using hh

/-- Step coefficients are bounded by the running norm of the actual Euler
path, with a constant independent of the number of grid cells. -/
theorem euler_step_coefficient_growth {Ω : Type*} {dim noise : ℕ}
    (μ : Fin dim → (Fin dim → ℝ) → ℝ) (σ : Fin dim → Fin noise → (Fin dim → ℝ) → ℝ)
    (W : Fin noise → ℝ → Ω → ℝ) (ξ : Ω → Fin dim → ℝ) (h : ℝ) (hh : 0≤h)
    (n : ℕ) (V : Ω → C(Icc (0:ℝ) ((n:ℝ)*h),Fin dim → ℝ))
    (hV : ∀ w r,V w r=eulerInterpolation μ σ W ξ h n r.val w)
    (b : (Fin dim → ℝ) → ℝ) (K : ℝ) (hK : 0≤K)
    (hb : ∀ x,(b x)^2≤K*(1+‖x‖^2))
    (w : Ω) (r : ℝ) (hr : r∈Icc 0 ((n:ℝ)*h)) :
    (∑ k∈Finset.range n,(Ioc ((k:ℝ)*h) (((k:ℝ)+1)*h)).indicator
      (fun _ => b (eulerGrid μ σ W ξ h k w)) r)^2≤
      K*(1+‖prefixPath (show 0≤(n:ℝ)*h by positivity) (normEnvelope (V w)) r‖^2) := by
  apply disjoint_grid_step_square_bound h hh n _ r _ (by positivity)
  intro k hk hkr
  have hk' : k≤n := (Finset.mem_range.mp hk).le
  have htk : (k:ℝ)*h∈Icc 0 ((n:ℝ)*h) := ⟨by positivity,mul_le_mul_of_nonneg_right (by exact_mod_cast hk') hh⟩
  have he : V w ⟨(k:ℝ)*h,htk⟩=eulerGrid μ σ W ξ h k w := by
    rw [hV,euler_interpolation_past μ σ W ξ h hh k n hk' _ le_rfl,euler_interpolation_grid μ σ W ξ h hh k]
  have hv := vector_value_le_prefix_norm (show 0≤(n:ℝ)*h by positivity) (V w) ⟨(k:ℝ)*h,htk⟩ r hr hkr.1.le
  rw [he] at hv
  exact (hb _).trans (mul_le_mul_of_nonneg_left
    (add_le_add le_rfl (pow_le_pow_left₀ (norm_nonneg _) hv 2)) hK)

end Asakura.Chapter4
