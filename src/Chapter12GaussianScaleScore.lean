import Chapter12GaussianShiftScores
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

open Finset
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

/-- The density score for a proportional volatility change with the
Black--Scholes mean correction. At z=s*w-s^2*k/2 it gives the vega weight
(sum(w_i^2)-d)/s - dot(k,w). -/
theorem gaussian_scale_density_score {d : ℕ} (C s : ℝ) (hs : s≠0)
    (w k : Fin d → ℝ) :
    HasDerivAt
      (fun u => C*Real.exp (-(d:ℝ)*Real.log u-
        (∑ i,((s*w i-s^2*k i/2)/u+u*k i/2)^2)/2))
      ((C*Real.exp (-(d:ℝ)*Real.log s-(∑ i,(w i)^2)/2))*
        (((∑ i,(w i)^2)-(d:ℝ))/s-(∑ i,k i*w i))) s := by
  let z : Fin d → ℝ := fun i => s*w i-s^2*k i/2
  have he (i : Fin d) : z i/s+s*k i/2=w i := by
    dsimp [z]
    field_simp [hs]
    <;> ring
  have hd (i : Fin d) : HasDerivAt (fun u : ℝ => z i/u+u*k i/2)
      (-w i/s+k i) s := by
    have hh := ((hasDerivAt_const s (z i)).div (hasDerivAt_id s) hs).add
      (((hasDerivAt_id s).mul_const (k i)).div_const 2)
    convert hh using 1
    · funext u
      rfl
    · dsimp only [id_eq,z]
      field_simp [hs]
      <;> ring
  have hsq (i : Fin d) : HasDerivAt (fun u : ℝ => (z i/u+u*k i/2)^2)
      (2*w i*(-w i/s+k i)) s := by
    convert (hd i).pow 2 using 1
    simp only [he,pow_one,Nat.cast_ofNat,Nat.reduceSub]
  have hh := (((Real.hasDerivAt_log hs).const_mul (-(d:ℝ))).sub
    ((HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => hsq i)).div_const 2)).exp.const_mul C
  have hsum : (∑ i,2*w i*(-w i/s+k i))/2=
      -(∑ i,(w i)^2)/s+(∑ i,k i*w i) := by
    simp only [div_eq_mul_inv,Finset.sum_mul,← Finset.sum_neg_distrib,← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  convert hh using 1
  simp only [Pi.sub_apply,he,hsum]
  field_simp [hs]
  <;> ring

end Asakura.Chapter12
