import Chapter4LangevinEigenvalues
import Mathlib.Analysis.Calculus.Deriv.Slope

open Matrix Filter
open scoped Topology Matrix.Norms.Operator
namespace Asakura.Chapter4
set_option maxHeartbeats 3200000
set_option backward.isDefEq.respectTransparency false

/-- The divided differences in the distinct-root formula have the
stated limits at a repeated root. -/
theorem companion_coefficients_repeated_limit (a t : ℂ) :
    Tendsto (fun b : ℂ => (Complex.exp (a*t)-Complex.exp (b*t))/(a-b))
      (𝓝[≠] a) (𝓝 (t*Complex.exp (a*t))) ∧
    Tendsto (fun b : ℂ => (a*Complex.exp (b*t)-b*Complex.exp (a*t))/(a-b))
      (𝓝[≠] a) (𝓝 ((1-a*t)*Complex.exp (a*t))) := by
  have hd : HasDerivAt (fun b : ℂ => Complex.exp (b*t)) (t*Complex.exp (a*t)) a := by
    convert ((hasDerivAt_id a).mul_const t).cexp using 1 <;> simp only [id_eq] <;> ring
  have hs := hd.tendsto_slope
  have hfirst : Tendsto (fun b : ℂ => (Complex.exp (a*t)-Complex.exp (b*t))/(a-b))
      (𝓝[≠] a) (𝓝 (t*Complex.exp (a*t))) := by
    convert hs using 1
    funext b
    simp only [slope, vsub_eq_sub, smul_eq_mul, div_eq_mul_inv]
    rw [← neg_sub b a,inv_neg,← neg_sub (Complex.exp (b*t)) (Complex.exp (a*t))]
    ring
  refine ⟨hfirst,?_⟩
  have ht : Tendsto (fun b : ℂ => Complex.exp (a*t)-a*((Complex.exp (a*t)-Complex.exp (b*t))/(a-b)))
      (𝓝[≠] a) (𝓝 (Complex.exp (a*t)-a*(t*Complex.exp (a*t)))) :=
    tendsto_const_nhds.sub (tendsto_const_nhds.mul hfirst)
  have heq : (fun b : ℂ => Complex.exp (a*t)-a*((Complex.exp (a*t)-Complex.exp (b*t))/(a-b)))
      =ᶠ[𝓝[≠] a] (fun b => (a*Complex.exp (b*t)-b*Complex.exp (a*t))/(a-b)) := by
    filter_upwards [self_mem_nhdsWithin] with b hb
    have hba : a-b≠0 := sub_ne_zero.mpr (Ne.symm hb)
    field_simp
    ring
  convert ht.congr' heq using 1 <;> ring

/-- The repeated-root formula is obtained by continuity of the matrix
exponential and the divided-difference limits, as in the manuscript. -/
theorem companion_exp_repeated_first_row (a t : ℂ) :
    let A : Matrix (Fin 2) (Fin 2) ℂ := !![0,1;-a*a,a+a]
    NormedSpace.exp (t • A) 0 0=(1-a*t)*Complex.exp (a*t) ∧
    NormedSpace.exp (t • A) 0 1=t*Complex.exp (a*t) := by
  dsimp only
  have hc : Continuous (fun b : ℂ => NormedSpace.exp
      (t • (!![0,1;-a*b,a+b] : Matrix (Fin 2) (Fin 2) ℂ))) := by
    apply NormedSpace.exp_continuous.comp
    fun_prop
  have hc0 := (((continuous_apply 0).comp ((continuous_apply 0).comp hc)).continuousAt (x:=a)).tendsto.mono_left (nhdsWithin_le_nhds (s := {a}ᶜ))
  have hc1 := (((continuous_apply 1).comp ((continuous_apply 0).comp hc)).continuousAt (x:=a)).tendsto.mono_left (nhdsWithin_le_nhds (s := {a}ᶜ))
  have he0 : (fun b : ℂ => NormedSpace.exp (t • (!![0,1;-a*b,a+b] : Matrix (Fin 2) (Fin 2) ℂ)) 0 0)
      =ᶠ[𝓝[≠] a] (fun b => (a*Complex.exp (b*t)-b*Complex.exp (a*t))/(a-b)) := by
    filter_upwards [self_mem_nhdsWithin] with b hb
    exact (companion_exp_first_row a b t (Ne.symm hb)).1
  have he1 : (fun b : ℂ => NormedSpace.exp (t • (!![0,1;-a*b,a+b] : Matrix (Fin 2) (Fin 2) ℂ)) 0 1)
      =ᶠ[𝓝[≠] a] (fun b => (Complex.exp (a*t)-Complex.exp (b*t))/(a-b)) := by
    filter_upwards [self_mem_nhdsWithin] with b hb
    exact (companion_exp_first_row a b t (Ne.symm hb)).2
  exact ⟨tendsto_nhds_unique (hc0.congr' he0) (companion_coefficients_repeated_limit a t).2,
    tendsto_nhds_unique (hc1.congr' he1) (companion_coefficients_repeated_limit a t).1⟩

end Asakura.Chapter4
