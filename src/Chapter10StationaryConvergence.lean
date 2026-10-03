import Chapter10StationaryError
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Order.Filter.AtTopBot.Field
import Mathlib.Tactic.FieldSimp

open Set Filter
open scoped Topology
namespace Asakura.Chapter10
set_option backward.isDefEq.respectTransparency false

/-- The positive root displayed in the text, allowing k=c^2/r^2. -/
theorem stationary_riccati_root (a k q : ℝ) (ha : 0<a) (hk : 0<k) (hq : 0<q) :
    let v := (Real.sqrt (a^2+k*q^2)-a)/k
    0<v ∧ q^2-2*a*v-k*v^2=0 := by
  have hd : 0≤a^2+k*q^2 := by positivity
  have hs := Real.sq_sqrt hd
  have hsn := Real.sqrt_nonneg (a^2+k*q^2)
  have hpos : a<Real.sqrt (a^2+k*q^2) := by
    have hkp : 0<k*q^2 := by positivity
    nlinarith
  dsimp only
  constructor
  · exact div_pos (sub_pos.mpr hpos) hk
  · field_simp
    have hs' : Real.sqrt (a^2+q^2*k)^2=a^2+q^2*k := by simpa only [mul_comm k] using hs
    nlinarith [hs']

/-- The decay estimate proves convergence of every nonnegative solution to
the displayed stationary variance. -/
theorem stationary_riccati_convergence (S : ℝ → ℝ) (a k q v : ℝ)
    (ha : 0<a) (hk : 0≤k) (hv : 0≤v) (heq : q-2*a*v-k*v^2=0)
    (hS : ∀ t,0≤t → 0≤S t)
    (hd : ∀ t,0≤t → HasDerivAt S (q-2*a*S t-k*(S t)^2) t) :
    Tendsto S atTop (𝓝 v) := by
  have he : Tendsto (fun t : ℝ => Real.exp (-4*a*t)) atTop (𝓝 0) := by
    have hmul : Tendsto (fun t : ℝ => (4*a)*t) atTop atTop :=
      (tendsto_const_mul_atTop_of_pos (by positivity : (0:ℝ)<4*a)).mpr tendsto_id
    simpa only [Function.comp_def,neg_mul] using Real.tendsto_exp_neg_atTop_nhds_zero.comp hmul
  have hb := he.const_mul ((S 0-v)^2)
  simp only [mul_zero] at hb
  have hsquare : Tendsto (fun t => (S t-v)^2) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall fun t => sq_nonneg _)
      (eventually_atTop.2 ⟨0,fun t ht => riccati_equilibrium_decay S a k q v hk hv heq hS hd t ht⟩) hb
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hsqrt := Real.continuous_sqrt.continuousAt.tendsto.comp hsquare
  simpa only [Function.comp_def,Real.sqrt_zero,Real.sqrt_sq_eq_abs,Real.norm_eq_abs] using hsqrt

/-- Exactly the coefficient convention in the stationary-error example. The
existence and nonnegativity hypotheses are supplied by the preceding Riccati
existence theorem, not by this scalar asymptotic calculation. -/
theorem stationary_error_example (S : ℝ → ℝ) (a q c r : ℝ)
    (ha : 0<a) (hq : 0<q) (hc : c≠0) (hr : 0<r)
    (hS : ∀ t,0≤t → 0≤S t)
    (hd : ∀ t,0≤t → HasDerivAt S (q^2-2*a*S t-(c^2/r^2)*(S t)^2) t) :
    Tendsto S atTop (𝓝 ((r^2/c^2)*(Real.sqrt (a^2+c^2*q^2/r^2)-a))) := by
  have hk : 0<c^2/r^2 := div_pos (sq_pos_of_ne_zero hc) (sq_pos_of_pos hr)
  have hv := stationary_riccati_root a (c^2/r^2) q ha hk hq
  have ht := stationary_riccati_convergence S a (c^2/r^2) (q^2)
    ((Real.sqrt (a^2+(c^2/r^2)*q^2)-a)/(c^2/r^2)) ha hk.le hv.1.le hv.2 hS hd
  have he : (Real.sqrt (a^2+(c^2/r^2)*q^2)-a)/(c^2/r^2) =
      (r^2/c^2)*(Real.sqrt (a^2+c^2*q^2/r^2)-a) := by
    have hi : (c^2/r^2)*q^2=c^2*q^2/r^2 := by ring
    rw [hi]
    field_simp
  rwa [he] at ht

end Asakura.Chapter10
