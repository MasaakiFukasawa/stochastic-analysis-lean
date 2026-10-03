import Chapter4EulerGrid

open Set
open scoped BigOperators
namespace Asakura.Chapter4
set_option maxHeartbeats 1800000

noncomputable def eulerInterpolation {Ω : Type*} {dim noise : ℕ}
    (μ : Fin dim → (Fin dim → ℝ) → ℝ) (σ : Fin dim → Fin noise → (Fin dim → ℝ) → ℝ)
    (W : Fin noise → ℝ → Ω → ℝ) (ξ : Ω → Fin dim → ℝ) (h : ℝ)
    (n : ℕ) (r : ℝ) (w : Ω) (i : Fin dim) : ℝ :=
  ξ w i+∑ k∈Finset.range n,
    (μ i (eulerGrid μ σ W ξ h k w)*(min (((k:ℝ)+1)*h) r-min ((k:ℝ)*h) r)+
      ∑ j,σ i j (eulerGrid μ σ W ξ h k w)*(W j (min (((k:ℝ)+1)*h) r) w-W j (min ((k:ℝ)*h) r) w))

lemma euler_interpolation_past {Ω : Type*} {dim noise : ℕ}
    (μ : Fin dim → (Fin dim → ℝ) → ℝ) (σ : Fin dim → Fin noise → (Fin dim → ℝ) → ℝ)
    (W : Fin noise → ℝ → Ω → ℝ) (ξ : Ω → Fin dim → ℝ) (h : ℝ) (hh : 0≤h)
    (k n : ℕ) (hkn : k≤n) (r : ℝ) (hr : r≤(k:ℝ)*h) :
    eulerInterpolation μ σ W ξ h n r=eulerInterpolation μ σ W ξ h k r := by
  induction n, hkn using Nat.le_induction with
  | base => rfl
  | succ n hkn ih =>
    funext w i
    have hn : r≤(n:ℝ)*h := hr.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hkn) hh)
    have hn1 : r≤((n:ℝ)+1)*h := by nlinarith
    simp only [eulerInterpolation,Finset.sum_range_succ,min_eq_right hn,min_eq_right hn1,
      sub_self,mul_zero,Finset.sum_const_zero,zero_add,add_zero]
    exact congrFun (congrFun ih w) i

lemma euler_interpolation_grid {Ω : Type*} {dim noise : ℕ}
    (μ : Fin dim → (Fin dim → ℝ) → ℝ) (σ : Fin dim → Fin noise → (Fin dim → ℝ) → ℝ)
    (W : Fin noise → ℝ → Ω → ℝ) (ξ : Ω → Fin dim → ℝ) (h : ℝ) (hh : 0≤h)
    (n : ℕ) : eulerInterpolation μ σ W ξ h n ((n:ℝ)*h)=eulerGrid μ σ W ξ h n := by
  induction n with
  | zero => funext w i;simp [eulerInterpolation,eulerGrid]
  | succ n ih =>
    funext w i
    have hn : (n:ℝ)*h≤((n:ℝ)+1)*h := by nlinarith
    have hp : eulerInterpolation μ σ W ξ h n (((n:ℝ)+1)*h) w i=
        eulerInterpolation μ σ W ξ h n ((n:ℝ)*h) w i := by
      dsimp only [eulerInterpolation]
      congr 1
      apply Finset.sum_congr rfl
      intro k hk
      have hk' : k+1≤n := Finset.mem_range.mp hk
      have hk1 : ((k:ℝ)+1)*h≤(n:ℝ)*h := mul_le_mul_of_nonneg_right (by exact_mod_cast hk') hh
      have hk0 : (k:ℝ)*h≤(n:ℝ)*h := by nlinarith
      rw [min_eq_left hk1,min_eq_left hk0,min_eq_left (hk1.trans hn),min_eq_left (hk0.trans hn)]
    change eulerInterpolation μ σ W ξ h (n+1) (((n+1:ℕ):ℝ)*h) w i=_
    simp only [Nat.cast_add,Nat.cast_one,eulerInterpolation,Finset.sum_range_succ,min_self,min_eq_left hn,eulerGrid]
    have hh' : ((n:ℝ)+1)*h-(n:ℝ)*h=h := by ring
    rw [hh']
    have hi := congrFun (congrFun ih w) i
    dsimp only [eulerInterpolation] at hp hi
    linarith only [hp,hi]

lemma euler_interpolation_after {Ω : Type*} {dim noise : ℕ}
    (μ : Fin dim → (Fin dim → ℝ) → ℝ) (σ : Fin dim → Fin noise → (Fin dim → ℝ) → ℝ)
    (W : Fin noise → ℝ → Ω → ℝ) (ξ : Ω → Fin dim → ℝ) (h : ℝ) (hh : 0≤h)
    (n : ℕ) (r : ℝ) (hr : (n:ℝ)*h≤r) :
    eulerInterpolation μ σ W ξ h n r=eulerGrid μ σ W ξ h n := by
  rw [← euler_interpolation_grid μ σ W ξ h hh n]
  funext w i
  dsimp only [eulerInterpolation]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k+1≤n := Finset.mem_range.mp hk
  have hk1 : ((k:ℝ)+1)*h≤(n:ℝ)*h := mul_le_mul_of_nonneg_right (by exact_mod_cast hk') hh
  have hk0 : (k:ℝ)*h≤(n:ℝ)*h := by nlinarith
  rw [min_eq_left hk1,min_eq_left hk0,min_eq_left (hk1.trans hr),min_eq_left (hk0.trans hr)]

/-- The finite-sum continuous interpolation agrees with the displayed
Euler formula on every grid cell, including both endpoints. -/
theorem euler_interpolation_on_cell {Ω : Type*} {dim noise : ℕ}
    (μ : Fin dim → (Fin dim → ℝ) → ℝ) (σ : Fin dim → Fin noise → (Fin dim → ℝ) → ℝ)
    (W : Fin noise → ℝ → Ω → ℝ) (ξ : Ω → Fin dim → ℝ) (h : ℝ) (hh : 0≤h)
    (n k : ℕ) (hkn : k<n) (r : ℝ) (hr : r∈Icc ((k:ℝ)*h) (((k:ℝ)+1)*h)) :
    eulerInterpolation μ σ W ξ h n r=fun w i =>
      eulerGrid μ σ W ξ h k w i+μ i (eulerGrid μ σ W ξ h k w)*(r-(k:ℝ)*h)+
        ∑ j,σ i j (eulerGrid μ σ W ξ h k w)*(W j r w-W j ((k:ℝ)*h) w) := by
  rw [euler_interpolation_past μ σ W ξ h hh (k+1) n hkn r (by simpa using hr.2)]
  funext w i
  have he := congrFun (congrFun (euler_interpolation_after μ σ W ξ h hh k r hr.1) w) i
  dsimp only [eulerInterpolation] at he ⊢
  rw [Finset.sum_range_succ,min_eq_right hr.2,min_eq_left hr.1]
  linarith only [he]

end Asakura.Chapter4
