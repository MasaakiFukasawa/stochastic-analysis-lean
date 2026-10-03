import Chapter13PrimitiveProducts
import Chapter11DiscountProduct

open MeasureTheory Set
namespace Asakura.Chapter13
set_option maxHeartbeats 2000000

theorem exponential_kernel_integral (a t T:ℝ) (ha:a≠0) :
    (∫s in t..T,Real.exp (-a*s))=Real.exp (-a*t)*((1-Real.exp (-a*(T-t)))/a) := by
  have hd x:HasDerivAt (fun s => Real.exp (-a*s)/(-a)) (Real.exp (-a*x)) x := by
    simpa [ha] using (((hasDerivAt_id x).const_mul (-a)).exp.div_const (-a))
  have hi:IntervalIntegrable (fun s => Real.exp (-a*s)) volume t T := (by fun_prop : Continuous (fun s:ℝ => Real.exp (-a*s))).intervalIntegrable t T
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x) hi]
  have he:Real.exp (-a*T)=Real.exp (-a*t)*Real.exp (-a*(T-t)) := by rw [←Real.exp_add];congr 1;ring
  rw [he]
  field_simp
  ring

theorem exponential_state_drift (a t X Y V:ℝ) (hV:0≤V) :
    Real.exp (-a*t)*(Y*Real.exp (-a*t))-a*(Real.exp (-a*t)*X)=
      Real.exp (-2*a*t)*Y-a*(Real.exp (-a*t)*X) ∧
    Real.exp (-a*t)*(Real.sqrt V*Real.exp (a*t))=Real.sqrt V ∧
    Real.exp (-2*a*t)*(Real.sqrt V*Real.exp (a*t))^2-2*a*(Real.exp (-2*a*t)*Y)=
      V-2*a*(Real.exp (-2*a*t)*Y) := by
  have he:Real.exp (-a*t)*Real.exp (a*t)=1 := by rw [←Real.exp_add];simp
  have he2:Real.exp (-2*a*t)=Real.exp (-a*t)*Real.exp (-a*t) := by rw [←Real.exp_add];congr 1;ring
  refine ⟨?_,?_,?_⟩
  · rw [he2];ring
  · calc
      _=(Real.exp (-a*t)*Real.exp (a*t))*Real.sqrt V := by ring
      _=_ := by rw [he];ring
  · rw [he2]
    have hh:Real.exp (-a*t)*Real.exp (-a*t)*(Real.sqrt V*Real.exp (a*t))^2=V := by
      calc
        _=(Real.exp (-a*t)*Real.exp (a*t))^2*(Real.sqrt V)^2 := by ring
        _=V := by rw [he,Real.sq_sqrt hV];ring
    rw [hh]

theorem exponential_bond_exponent (a t B X Y:ℝ) :
    -(Real.exp (-a*t)*B)^2*Y/2-(Real.exp (-a*t)*B)*X=
      -B^2*(Real.exp (-2*a*t)*Y)/2-B*(Real.exp (-a*t)*X) := by
  have he:Real.exp (-2*a*t)=Real.exp (-a*t)^2 := by rw [pow_two,←Real.exp_add];congr 1;ring
  rw [he]
  ring
theorem exponential_weight_time_density (a t:ℝ) :
    Real.exp (-a*t)=1+∫s in 0..t,-a*Real.exp (-a*s) := by
  have hd s:HasDerivAt (fun r:ℝ => Real.exp (-a*r)) (-a*Real.exp (-a*s)) s := by
    simpa only [mul_comm,id_eq,mul_one] using ((hasDerivAt_id s).const_mul (-a)).exp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hd s)
    ((by fun_prop : Continuous (fun s:ℝ => -a*Real.exp (-a*s))).intervalIntegrable 0 t)]
  simp

end Asakura.Chapter13
#print axioms Asakura.Chapter13.exponential_kernel_integral
#print axioms Asakura.Chapter13.exponential_state_drift
#print axioms Asakura.Chapter13.exponential_bond_exponent

#print axioms Asakura.Chapter13.exponential_weight_time_density
