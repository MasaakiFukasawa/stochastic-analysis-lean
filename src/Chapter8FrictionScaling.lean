import Chapter8NewtonThreshold

namespace Asakura.Chapter8

/-- The physical friction assumption is exactly the dimensionless one used
in the quadratic-form construction. -/
theorem newton_friction_rescaling (m γ κ L : ℝ) (hm : 0 < m) (hκ : 0 ≤ κ) (hL : 0 ≤ L)
    (hγ : Real.sqrt m * (Real.sqrt L - Real.sqrt κ) < γ) :
    Real.sqrt (L/m) - Real.sqrt (κ/m) < γ/m := by
  have hs : 0 < Real.sqrt m := Real.sqrt_pos.mpr hm
  have hsq := Real.sq_sqrt hm.le
  rw [Real.sqrt_div hL,Real.sqrt_div hκ]
  apply (lt_div_iff₀ hm).mpr
  have he : (Real.sqrt L / Real.sqrt m - Real.sqrt κ / Real.sqrt m)*m =
      Real.sqrt m*(Real.sqrt L-Real.sqrt κ) := by
    calc
      _ = (Real.sqrt L / Real.sqrt m - Real.sqrt κ / Real.sqrt m)*(Real.sqrt m)^2 := by rw [hsq]
      _ = _ := by field_simp
  rwa [he]

end Asakura.Chapter8
