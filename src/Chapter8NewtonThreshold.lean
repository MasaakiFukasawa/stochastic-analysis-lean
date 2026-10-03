import FullAuditLangevinPaths

namespace Asakura.Chapter8
set_option maxHeartbeats 300000

/-- The open interval for b in the manuscript is nonempty. -/
theorem newton_threshold_interval (l u δ : ℝ) (hl : 0 < l)
    (hlu : l ≤ u) (hδ : Real.sqrt u - Real.sqrt l < δ) :
    ∃ b : ℝ, max (l - δ * Real.sqrt l) (u - δ * Real.sqrt u) < b ∧
      b < l + δ * Real.sqrt l := by
  have hs := Real.sqrt_le_sqrt hlu
  have hd : 0 < δ := lt_of_le_of_lt (sub_nonneg.mpr hs) hδ
  have hsl : 0 < Real.sqrt l := Real.sqrt_pos.2 hl
  have hsu : 0 < Real.sqrt u := Real.sqrt_pos.2 (lt_of_lt_of_le hl hlu)
  have hprod := mul_lt_mul_of_pos_right hδ (add_pos hsu hsl)
  have hls := Real.sq_sqrt hl.le
  have hus := Real.sq_sqrt (le_trans hl.le hlu)
  have hleft : u - δ * Real.sqrt u < l + δ * Real.sqrt l := by
    nlinarith
  exact exists_between (max_lt (by nlinarith) hleft)

/-- Determinants of P and both endpoint R matrices, without spectral assumptions. -/
theorem newton_threshold_determinants (l u δ b : ℝ) (hl : 0 < l)
    (hlu : l ≤ u) (hd : 0 < δ)
    (hb : max (l - δ * Real.sqrt l) (u - δ * Real.sqrt u) < b)
    (hb' : b < l + δ * Real.sqrt l) :
    0 < b + δ^2/4 ∧
    0 < δ^2*l - (l-b)^2 ∧ 0 < δ^2*u - (u-b)^2 := by
  have hbl := (max_lt_iff.mp hb).1
  have hbu := (max_lt_iff.mp hb).2
  have hls := Real.sq_sqrt hl.le
  have hus := Real.sq_sqrt (le_trans hl.le hlu)
  have hmono := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hlu) hd.le
  have hpu : b < u + δ * Real.sqrt u := by linarith
  have hdl : 0 < (δ * Real.sqrt l - (l-b)) * (δ * Real.sqrt l + (l-b)) :=
    mul_pos (by linarith) (by linarith)
  have hdu : 0 < (δ * Real.sqrt u - (u-b)) * (δ * Real.sqrt u + (u-b)) :=
    mul_pos (by linarith) (by linarith)
  constructor
  · nlinarith [sq_nonneg (Real.sqrt l - δ/2)]
  constructor
  · have he : (δ * Real.sqrt l - (l-b)) * (δ * Real.sqrt l + (l-b)) =
        δ^2*l - (l-b)^2 := by
      calc
        _ = δ^2*(Real.sqrt l)^2 - (l-b)^2 := by ring
        _ = _ := by rw [hls]
    rwa [he] at hdl
  · have he : (δ * Real.sqrt u - (u-b)) * (δ * Real.sqrt u + (u-b)) =
        δ^2*u - (u-b)^2 := by
      calc
        _ = δ^2*(Real.sqrt u)^2 - (u-b)^2 := by ring
        _ = _ := by rw [hus]
    rwa [he] at hdu

/-- The energy P is strictly positive away from the origin. -/
theorem newton_energy_positive (δ b q v : ℝ) (hp : 0 < b + δ^2/4)
    (hz : q ≠ 0 ∨ v ≠ 0) :
    0 < (b + δ^2/2)*q^2 + δ*q*v + v^2 := by
  have he : (b + δ^2/2)*q^2 + δ*q*v + v^2 =
      (v + δ*q/2)^2 + (b + δ^2/4)*q^2 := by ring
  rw [he]
  by_cases hq : q = 0
  · have hv : v ≠ 0 := hz.resolve_left (not_not_intro hq)
    simpa [hq] using sq_pos_of_ne_zero hv
  · exact add_pos_of_nonneg_of_pos (sq_nonneg _) (mul_pos hp (sq_pos_of_ne_zero hq))

/-- Positivity of R(h) from its determinant, by completing the square. -/
theorem newton_dissipation_positive (δ h b q v : ℝ) (hd : 0 < δ)
    (hdet : 0 < δ^2*h - (h-b)^2) (hz : q ≠ 0 ∨ v ≠ 0) :
    0 < δ*h*q^2 + 2*(h-b)*q*v + δ*v^2 := by
  have he : δ * (δ*h*q^2 + 2*(h-b)*q*v + δ*v^2) =
      (δ*v + (h-b)*q)^2 + (δ^2*h - (h-b)^2)*q^2 := by ring
  have hp : 0 < δ * (δ*h*q^2 + 2*(h-b)*q*v + δ*v^2) := by
    rw [he]
    by_cases hq : q = 0
    · have hv : v ≠ 0 := hz.resolve_left (not_not_intro hq)
      simpa [hq] using sq_pos_of_ne_zero (mul_ne_zero hd.ne' hv)
    · exact add_pos_of_nonneg_of_pos (sq_nonneg _) (mul_pos hdet (sq_pos_of_ne_zero hq))
  exact (mul_pos_iff_of_pos_left hd).mp hp

end Asakura.Chapter8
