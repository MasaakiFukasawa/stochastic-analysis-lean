import Chapter12FiniteGraphHolder
import Chapter12UniformCoordinateProjection

namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000

private theorem sqrt_nat_power (x : ℝ) (hx : 0≤x) (k : ℕ) : Real.sqrt (x^k)=(Real.sqrt x)^k := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ,Real.sqrt_mul (pow_nonneg hx k),ih,pow_succ]

/-- Fully contracted finite tensors, with no self-contractions, are
bounded by the product of their Hilbert norms. Coordinate dimensions
cancel because every edge contributes exactly two tensor indices. -/
theorem finite_tensor_network_bound (N e : ℕ) {V : Type*} [Fintype V] [DecidableEq V]
    (degree : V → ℕ) (port : ∀ v,Fin (degree v) → Fin e)
    (hport : ∀ v,Function.Injective (port v))
    (left right : Fin e → V) (hneq : ∀ k,left k≠right k)
    (hcover : ∀ v k,v≠left k → v≠right k → ∀ j,port v j≠k)
    (hdegree : (∑ v,degree v)=2*e)
    (A : ∀ v,(Fin (degree v) → Fin (N+1)) → ℝ) :
    |∑ a : Fin e → Fin (N+1),∏ v,A v (a ∘ port v)|≤
      ∏ v,Real.sqrt (∑ b : Fin (degree v) → Fin (N+1),A v b^2) := by
  let f := fun v (a : Fin e → Fin (N+1)) => |A v (a ∘ port v)|
  have hdep : ∀ v k,v≠left k → v≠right k → IgnoresCoordinate (f v) k := by
    intro v k hvl hvr a i
    have he : (Function.update a k i) ∘ port v=a ∘ port v := by
      funext j
      exact Function.update_of_ne (hcover v k hvl hvr j) _ _
    change |A v ((Function.update a k i) ∘ port v)|=|A v (a ∘ port v)|
    rw [he]
  have hh := finite_graph_holder N e left right hneq f (fun v a => abs_nonneg _) hdep
  have hnorm (v : V) : cubeAverage N e (fun a => f v a^2)=
      (∑ b : Fin (degree v) → Fin (N+1),A v b^2)/(N+1:ℝ)^(degree v) := by
    change cubeAverage N e (fun a => |A v (a ∘ port v)|^2)=_
    simp_rw [sq_abs]
    exact (cubeAverage_coordinate_projection N e (degree v) (port v) (hport v)
      (fun b => A v b^2)).trans (cubeAverage_eq_sum _ _ _)
  have hK : 0<(N+1:ℝ) := by positivity
  have hden : (∏ v,(Real.sqrt (N+1:ℝ))^(degree v))=(N+1:ℝ)^e := by
    rw [Finset.prod_pow_eq_pow_sum,hdegree,pow_mul,Real.sq_sqrt hK.le]
  have hrhs : (∏ v,Real.sqrt (cubeAverage N e (fun a => f v a^2)))=
      (∏ v,Real.sqrt (∑ b : Fin (degree v) → Fin (N+1),A v b^2))/(N+1:ℝ)^e := by
    simp_rw [hnorm,Real.sqrt_div (Finset.sum_nonneg (fun _ _ => sq_nonneg _)),sqrt_nat_power _ hK.le]
    rw [Finset.prod_div_distrib,hden]
  rw [hrhs,cubeAverage_eq_sum] at hh
  have hs : (∑ a : Fin e → Fin (N+1),∏ v,f v a)≤
      ∏ v,Real.sqrt (∑ b : Fin (degree v) → Fin (N+1),A v b^2) :=
    (div_le_div_iff_of_pos_right (pow_pos hK e)).mp hh
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  simpa only [Finset.abs_prod,f] using hs

end Asakura.Chapter12
