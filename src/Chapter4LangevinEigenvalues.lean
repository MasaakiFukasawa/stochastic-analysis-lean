import Chapter4MatrixExpCalculus
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

open Matrix
open scoped Topology Matrix.Norms.Operator
namespace Asakura.Chapter4
set_option maxHeartbeats 3600000
set_option backward.isDefEq.respectTransparency false

/-- The first row of the companion-matrix exponential for distinct roots.
The calculation is over C, so negative discriminants are included. -/
theorem companion_exp_first_row (a b t : ℂ) (hab : a≠b) :
    let A : Matrix (Fin 2) (Fin 2) ℂ := !![0,1;-a*b,a+b]
    NormedSpace.exp (t • A) 0 0=(a*Complex.exp (b*t)-b*Complex.exp (a*t))/(a-b) ∧
    NormedSpace.exp (t • A) 0 1=(Complex.exp (a*t)-Complex.exp (b*t))/(a-b) := by
  classical
  dsimp only
  let P : Matrix (Fin 2) (Fin 2) ℂ := !![1,1;a,b]
  let Q : Matrix (Fin 2) (Fin 2) ℂ := !![b/(b-a),-1/(b-a);-a/(b-a),1/(b-a)]
  have hba : b-a≠0 := sub_ne_zero.mpr hab.symm
  have hPQ : P*Q=1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [P,Q,Matrix.mul_apply,Fin.sum_univ_two] <;> field_simp <;> ring
  have hQP : Q*P=1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [P,Q,Matrix.mul_apply,Fin.sum_univ_two] <;> field_simp <;> ring
  let U : (Matrix (Fin 2) (Fin 2) ℂ)ˣ := ⟨P,Q,hPQ,hQP⟩
  let D : Matrix (Fin 2) (Fin 2) ℂ := diagonal ![t*a,t*b]
  have hconj : P*D*Q=t • (!![0,1;-a*b,a+b] : Matrix (Fin 2) (Fin 2) ℂ) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [P,Q,D,Matrix.mul_apply,Fin.sum_univ_two,Matrix.diagonal,Matrix.vecHead,Matrix.vecTail] <;> field_simp <;> ring
  have hexp := Matrix.exp_units_conj U D
  change NormedSpace.exp (P*D*Q)=P*NormedSpace.exp D*Q at hexp
  rw [hconj] at hexp
  have hed : NormedSpace.exp D=diagonal ![Complex.exp (t*a),Complex.exp (t*b)] := by
    change NormedSpace.exp (diagonal ![t*a,t*b])=diagonal ![Complex.exp (t*a),Complex.exp (t*b)]
    rw [Matrix.exp_diagonal]
    congr 1
    ext i
    fin_cases i <;> simp [Pi.coe_exp,← Complex.exp_eq_exp_ℂ]
  rw [hed] at hexp
  rw [hexp]
  constructor <;> simp [P,Q,Matrix.mul_apply,Fin.sum_univ_two,Matrix.diagonal,Matrix.vecHead,Matrix.vecTail,mul_comm t]
  all_goals field_simp;ring

end Asakura.Chapter4
