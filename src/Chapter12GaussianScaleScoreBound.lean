import Chapter12GaussianScaleKernelBound

open Finset
namespace Asakura.Chapter12
set_option maxHeartbeats 2200000

/-- The scale score is uniformly bounded by a quadratic polynomial on a
positive compact scale interval. -/
theorem gaussian_scale_score_bound (s u Z K D : ℝ) (hs : 0<s)
    (hu : s/2≤u) (hu' : u≤2*s) (hZ : 0≤Z) (hK : 0≤K) (hD : 0≤D) :
    |Z/u^3-D/u-u*K/4|≤(8/s^3+2*D/s+s*K/2)*(1+Z) := by
  have hup : 0<u := by linarith
  have hcube : (s/2)^3≤u^3 := pow_le_pow_left₀ (by positivity) hu 3
  have hfirst : Z/u^3≤8/s^3*Z := by
    have hh := div_le_div_of_nonneg_left hZ (by positivity : 0<(s/2)^3) hcube
    convert hh using 1 <;> field_simp <;> ring
  have hsecond : D/u≤2*D/s := by
    have hh := div_le_div_of_nonneg_left hD (by positivity : 0<s/2) hu
    convert hh using 1 <;> field_simp <;> ring
  have hthird : u*K/4≤s*K/2 := by
    have hh := mul_le_mul_of_nonneg_right hu' hK
    linarith
  have hab : |Z/u^3-D/u-u*K/4|≤Z/u^3+D/u+u*K/4 := by
    calc
      _≤|Z/u^3-D/u|+|u*K/4| := abs_sub _ _
      _≤(|Z/u^3|+|D/u|)+|u*K/4| := add_le_add (abs_sub _ _) le_rfl
      _=_ := by rw [abs_of_nonneg (by positivity),abs_of_nonneg (by positivity),abs_of_nonneg (by positivity)]
  have hp : 0≤8/s^3 := by positivity
  have hp2 : 0≤2*D/s+s*K/2 := by positivity
  nlinarith [mul_nonneg hp2 hZ]

end Asakura.Chapter12
