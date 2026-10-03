import Chapter4LevyCalculus

open Set
open scoped ContDiff
namespace Asakura.Chapter4
open Asakura.Chapter5
set_option maxHeartbeats 2500000

noncomputable def geometricFlow (y a b : ℝ) (p : Fin 2 → ℝ) : ℝ :=
  y*Real.exp ((a-b^2/2)*p 0+b*p 1)

lemma geometricFlow_smooth (y a b : ℝ) : ContDiff ℝ 2 (geometricFlow y a b) := by
  unfold geometricFlow; fun_prop

lemma geometricFlow_time (y a b t x : ℝ) :
    HasDerivAt (fun r => geometricFlow y a b ![r,x])
      ((a-b^2/2)*geometricFlow y a b ![t,x]) t := by
  have h := ((((hasDerivAt_id t).const_mul (a-b^2/2)).add_const (b*x)).exp).const_mul y
  convert h using 1 <;> simp only [id_eq,geometricFlow,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.head_cons] <;> ring

lemma geometricFlow_space (y a b t x : ℝ) :
    HasDerivAt (fun z => geometricFlow y a b ![t,z])
      (b*geometricFlow y a b ![t,x]) x := by
  have h := ((((hasDerivAt_id x).const_mul b).const_add ((a-b^2/2)*t)).exp).const_mul y
  convert h using 1 <;> simp only [id_eq,geometricFlow,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.head_cons] <;> ring

lemma geometricFlow_fderiv_time (y a b t x : ℝ) :
    fderiv ℝ (geometricFlow y a b) ![t,x] (Pi.single 0 1)=
      (a-b^2/2)*geometricFlow y a b ![t,x] :=
  (((geometricFlow_smooth y a b).differentiable (by norm_num)).differentiableAt.hasFDerivAt.comp_hasDerivAt t
    (fin2_time_slice_derivative t x)).unique (geometricFlow_time y a b t x)

lemma geometricFlow_fderiv_space (y a b t x : ℝ) :
    fderiv ℝ (geometricFlow y a b) ![t,x] (Pi.single 1 1)=b*geometricFlow y a b ![t,x] := by
  rw [fin2_space_derivative _ _ _ ((geometricFlow_smooth y a b).differentiable (by norm_num) _)]
  exact (geometricFlow_space y a b t x).deriv

lemma geometricFlow_fderiv_second (y a b t x : ℝ) :
    fderiv ℝ (fderiv ℝ (geometricFlow y a b)) ![t,x] (Pi.single 1 1) (Pi.single 1 1)=
      b^2*geometricFlow y a b ![t,x] := by
  rw [fin2_space_second_derivative _ univ isOpen_univ (geometricFlow_smooth y a b).contDiffOn t x (by simp)]
  simp_rw [(geometricFlow_space y a b t _).deriv]
  convert ((geometricFlow_space y a b t x).const_mul b).deriv using 1 <;> ring

end Asakura.Chapter4
