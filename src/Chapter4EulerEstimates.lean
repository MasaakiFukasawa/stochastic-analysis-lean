import FullAuditChapter4Gronwall
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open MeasureTheory Set Filter
open scoped Topology
namespace Asakura.Chapter4

/-- The split used at the last step of the Euler proof, valid in any normed
state space. -/
theorem split_error_sq {E : Type*} [NormedAddCommGroup E] (x y z : E) :
    ‖x-z‖^2 ≤ 2*‖x-y‖^2+2*‖y-z‖^2 := by
  have h : ‖x-z‖ ≤ ‖x-y‖+‖y-z‖ := by
    calc
      ‖x-z‖ = ‖(x-y)+(y-z)‖ := by congr 1; abel
      _ ≤ _ := norm_add_le _ _
  nlinarith [norm_nonneg (x-z), norm_nonneg (x-y), norm_nonneg (y-z),
    sq_nonneg (‖x-y‖-‖y-z‖)]

/-- The within-cell estimate uses h² ≤ T h, not a maximum of Brownian
increments over all grid cells. -/
theorem euler_cell_bound (h T K M b v : ℝ) (hh : 0 ≤ h) (hhT : h ≤ T)
    (hb : 0 ≤ b) (hv : 0 ≤ v) (hgrowth : b+v ≤ K*(1+M)) :
    2*h^2*b+2*h*v ≤ 2*(T+1)*K*(1+M)*h := by
  have hT : 0 ≤ T := hh.trans hhT
  have h1 : h^2 ≤ T*h := by nlinarith
  have h2 := mul_le_mul_of_nonneg_right h1 hb
  have h3 := mul_le_mul_of_nonneg_left hgrowth (show 0 ≤ 2*(T+1)*h by positivity)
  have h4 := mul_nonneg (mul_nonneg hh hv) (show 0 ≤ T by linarith)
  nlinarith [mul_nonneg hh hb]

/-- Quantitative Gronwall step for Euler moments. -/
theorem euler_moment_bound (H : ℝ → ℝ) (M C T : ℝ) (hH : ContinuousOn H (Icc 0 T)) (hT : 0 ≤ T) (hC : 0 < C)
    (h : ∀ t ∈ Icc 0 T, H t ≤ 3*M+C*∫ s in 0..t, (1+H s)) :
    ∀ t ∈ Icc 0 T, H t ≤ (3*M+C*T)*Real.exp (C*t) := by
  apply Asakura.FullAudit.ch4_gronwall_written H (3*M+C*T) C T hT hH hC
  intro t ht
  have hi : IntervalIntegrable H volume 0 t :=
    (hH.mono (Icc_subset_Icc_right ht.2)).intervalIntegrable_of_Icc ht.1
  have he : (∫ s in 0..t, (1+H s)) = t + ∫ s in 0..t, H s := by
    rw [intervalIntegral.integral_add intervalIntegrable_const hi]
    simp
  have hh := h t ht
  rw [he] at hh
  have hm := mul_le_mul_of_nonneg_left ht.2 hC.le
  nlinarith

/-- The final Volterra inequality gives the squared O(n⁻¹) rate with a
constant independent of n and the initial second moment M. -/
theorem euler_squared_rate (F : ℝ → ℝ) (T C M : ℝ) (n : ℕ)
    (hT : 0 ≤ T) (hC : 0 < C) (hn : 0 < n)
    (hF : ContinuousOn F (Icc 0 T))
    (h : ∀ t ∈ Icc 0 T,
      F t ≤ C*(∫ s in 0..t, F s) + C*(1+M)*(T/(n:ℝ))) :
    F T ≤ (C*T*Real.exp (C*T))*(1+M)/(n:ℝ) := by
  have hg := Asakura.FullAudit.ch4_gronwall_written F (C*(1+M)*(T/(n:ℝ))) C T hT hF hC
    (fun t ht => by linarith [h t ht]) T ⟨hT,le_rfl⟩
  convert hg using 1 <;> ring

/-- Passage from the squared estimate to the root mean square estimate. -/
theorem euler_root_rate (E A : ℝ) (n : ℕ) (hE : 0 ≤ E) (hA : 0 ≤ A)
    (h : E ≤ A/(n:ℝ)) :
    Real.sqrt E ≤ Real.sqrt A / Real.sqrt (n:ℝ) := by
  simpa only [Real.sqrt_div hA] using Real.sqrt_le_sqrt h

/-- The same Gronwall argument closes uniqueness, with zero initial error. -/
theorem uniqueness_from_difference_estimate (u : ℝ → ℝ) (T c : ℝ)
    (hT : 0 ≤ T) (hc : 0 < c) (hu : ContinuousOn u (Icc 0 T))
    (hpos : ∀ t ∈ Icc 0 T, 0 ≤ u t)
    (h : ∀ t ∈ Icc 0 T, u t ≤ c*∫ s in 0..t, u s) :
    ∀ t ∈ Icc 0 T, u t = 0 := by
  have hg := Asakura.FullAudit.ch4_gronwall_written u 0 c T hT hu hc
    (fun t ht => by simpa using h t ht)
  intro t ht
  have hg' := hg t ht
  simp only [zero_mul] at hg'
  exact le_antisymm hg' (hpos t ht)

end Asakura.Chapter4
