import Chapter6GaussianBridgeSquare

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
namespace Asakura.Chapter6
set_option maxHeartbeats 1800000

lemma bridge_square_coarse_bounds (s t z d : ℝ) (hs : 0≤s) (hst : s<t)
    (hz : 0≤z) (hd : 0≤d) :
    2*(s/t)^2*z+2*d*(s*(t-s)/t)≤(2+2*d*t)*(1+z) ∧
    2*((t-s)/t)^2*z+2*d*(s*(t-s)/t)≤(2/t+2*d)*(1+z)*(t-s) := by
  have ht : 0<t := lt_of_le_of_lt hs hst
  have ha : 0≤s/t := div_nonneg hs ht.le
  have hb : s/t≤1 := (div_le_one ht).2 hst.le
  have hc : 0≤(t-s)/t := div_nonneg (sub_nonneg.mpr hst.le) ht.le
  have he : (t-s)/t≤1 := (div_le_one ht).2 (by linarith)
  have hv : s*(t-s)/t≤t-s := (div_le_iff₀ ht).2 (by nlinarith)
  have hv' : s*(t-s)/t≤t := hv.trans (by linarith)
  have hsa : (s/t)^2≤1 := by nlinarith
  have hsc : ((t-s)/t)^2≤(t-s)/t := by nlinarith
  constructor
  · have h1 := mul_le_mul_of_nonneg_right hsa hz
    have h2 := mul_le_mul_of_nonneg_left hv' (show 0≤d by exact hd)
    nlinarith [mul_nonneg (mul_nonneg hd ht.le) hz]
  · have h1 := mul_le_mul_of_nonneg_right hsc hz
    have h2 := mul_le_mul_of_nonneg_left hv hd
    have hh : 2*((t-s)/t)*z+2*d*(t-s)≤(2/t+2*d)*(1+z)*(t-s) := by
      have hpos : 0≤2/t*(t-s)+2*d*z*(t-s) := by positivity
      have heq : (2/t+2*d)*(1+z)*(t-s)-(2*((t-s)/t)*z+2*d*(t-s))=2/t*(t-s)+2*d*z*(t-s) := by ring
      linarith
    linarith

end Asakura.Chapter6
