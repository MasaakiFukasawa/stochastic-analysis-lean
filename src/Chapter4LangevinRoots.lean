import Chapter4LangevinEigenvalues
import Mathlib.Analysis.SpecialFunctions.Sqrt

open Matrix Complex
open scoped Topology Matrix.Norms.Operator ComplexConjugate
namespace Asakura.Chapter4
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

/-- Any square root of the discriminant gives precisely the two roots
used in the manuscript's companion matrix. -/
theorem langevin_root_algebra (κ γ m q : ℂ) (hm : m≠0)
    (hq : q^2=γ^2/m^2-4*κ/m) :
    let a := (-γ/m+q)/2
    let b := (-γ/m-q)/2
    a+b= -γ/m ∧ -a*b= -κ/m ∧ a-b=q := by
  dsimp only
  constructor
  · ring
  constructor
  · linear_combination hq/4
  · ring

theorem langevin_exp_distinct_roots (κ γ m q t : ℂ) (hm : m≠0)
    (hq : q^2=γ^2/m^2-4*κ/m) (hd : γ^2/m^2-4*κ/m≠0) :
    let a := (-γ/m+q)/2
    let b := (-γ/m-q)/2
    NormedSpace.exp (t • (!![0,1;-κ/m,-γ/m] : Matrix (Fin 2) (Fin 2) ℂ)) 0 0=
      (a*Complex.exp (b*t)-b*Complex.exp (a*t))/(a-b) ∧
    NormedSpace.exp (t • (!![0,1;-κ/m,-γ/m] : Matrix (Fin 2) (Fin 2) ℂ)) 0 1=
      (Complex.exp (a*t)-Complex.exp (b*t))/(a-b) := by
  dsimp only
  obtain ⟨hs,hp,hsub⟩ := langevin_root_algebra κ γ m q hm hq
  have hne : (-γ/m+q)/2≠(-γ/m-q)/2 := by
    intro he
    have hq0 : q=0 := by rw [he,sub_self] at hsub;exact hsub.symm
    apply hd
    rw [← hq,hq0,zero_pow (by norm_num)]
  have hh := companion_exp_first_row ((-γ/m+q)/2) ((-γ/m-q)/2) t hne
  dsimp only at hh
  rw [hp,hs] at hh
  exact hh

/-- For a negative real discriminant the two roots are conjugate. -/
theorem langevin_negative_discriminant (c D : ℝ) (hD : D<0) :
    let q : ℂ := (Real.sqrt (-D) : ℂ)*Complex.I
    q^2=(D:ℂ) ∧
    conj (((c:ℂ)+q)/2)=((c:ℂ)-q)/2 := by
  dsimp only
  constructor
  · rw [mul_pow,Complex.I_sq,← Complex.ofReal_pow,Real.sq_sqrt (by linarith)]
    simp
  · simp only [map_div₀,map_add,map_mul,Complex.conj_ofReal,Complex.conj_I,map_ofNat]
    ring

/-- The two displayed entries are real when the roots are conjugate. -/
theorem companion_conjugate_entries_real (a : ℂ) (t : ℝ) :
    conj ((a*Complex.exp (conj a*t)-conj a*Complex.exp (a*t))/(a-conj a))=
      (a*Complex.exp (conj a*t)-conj a*Complex.exp (a*t))/(a-conj a) ∧
    conj ((Complex.exp (a*t)-Complex.exp (conj a*t))/(a-conj a))=
      (Complex.exp (a*t)-Complex.exp (conj a*t))/(a-conj a) := by
  constructor <;> simp only [map_div₀,map_sub,map_mul,← Complex.exp_conj,map_ofNat,
    Complex.conj_ofReal,starRingEnd_self_apply]
  all_goals
    rw [show conj a-a= -(a-conj a) by ring,div_neg_eq_neg_div]
    ring

end Asakura.Chapter4
