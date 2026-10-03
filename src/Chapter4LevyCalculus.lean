import Chapter5TimeReversePDE
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

open Set
open scoped ContDiff
namespace Asakura.Chapter4
open Asakura.Chapter5
set_option maxHeartbeats 2500000

noncomputable def levyCos (u : ℝ) (p : Fin 2 → ℝ) : ℝ := Real.exp (u^2*p 0/2)*Real.cos (u*p 1)
noncomputable def levySin (u : ℝ) (p : Fin 2 → ℝ) : ℝ := Real.exp (u^2*p 0/2)*Real.sin (u*p 1)

lemma levyCos_smooth (u : ℝ) : ContDiff ℝ 2 (levyCos u) := by unfold levyCos; fun_prop
lemma levySin_smooth (u : ℝ) : ContDiff ℝ 2 (levySin u) := by unfold levySin; fun_prop

lemma levyCos_time (u t x : ℝ) :
    HasDerivAt (fun r => levyCos u ![r,x]) (u^2/2*levyCos u ![t,x]) t := by
  have h := (((hasDerivAt_id t).const_mul (u^2)).div_const 2).exp.mul_const (Real.cos (u*x))
  convert h using 1 <;> simp only [id_eq,levyCos,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.head_cons] <;> ring

lemma levySin_time (u t x : ℝ) :
    HasDerivAt (fun r => levySin u ![r,x]) (u^2/2*levySin u ![t,x]) t := by
  have h := (((hasDerivAt_id t).const_mul (u^2)).div_const 2).exp.mul_const (Real.sin (u*x))
  convert h using 1 <;> simp only [id_eq,levySin,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.head_cons] <;> ring

lemma levyCos_space (u t x : ℝ) :
    HasDerivAt (fun y => levyCos u ![t,y]) (-u*levySin u ![t,x]) x := by
  have h := (((hasDerivAt_id x).const_mul u).cos).const_mul (Real.exp (u^2*t/2))
  convert h using 1 <;> simp only [id_eq,levyCos,levySin,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.head_cons] <;> ring

lemma levySin_space (u t x : ℝ) :
    HasDerivAt (fun y => levySin u ![t,y]) (u*levyCos u ![t,x]) x := by
  have h := (((hasDerivAt_id x).const_mul u).sin).const_mul (Real.exp (u^2*t/2))
  convert h using 1 <;> simp only [id_eq,levyCos,levySin,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.head_cons] <;> ring

lemma levyCos_fderiv_time (u t x : ℝ) :
    fderiv ℝ (levyCos u) ![t,x] (Pi.single 0 1)=u^2/2*levyCos u ![t,x] :=
  (((levyCos_smooth u).differentiable (by norm_num)).differentiableAt.hasFDerivAt.comp_hasDerivAt t
    (fin2_time_slice_derivative t x)).unique (levyCos_time u t x)

lemma levySin_fderiv_time (u t x : ℝ) :
    fderiv ℝ (levySin u) ![t,x] (Pi.single 0 1)=u^2/2*levySin u ![t,x] :=
  (((levySin_smooth u).differentiable (by norm_num)).differentiableAt.hasFDerivAt.comp_hasDerivAt t
    (fin2_time_slice_derivative t x)).unique (levySin_time u t x)

lemma levyCos_fderiv_space (u t x : ℝ) :
    fderiv ℝ (levyCos u) ![t,x] (Pi.single 1 1)=-u*levySin u ![t,x] := by
  rw [fin2_space_derivative _ _ _ ((levyCos_smooth u).differentiable (by norm_num) _)]
  exact (levyCos_space u t x).deriv

lemma levySin_fderiv_space (u t x : ℝ) :
    fderiv ℝ (levySin u) ![t,x] (Pi.single 1 1)=u*levyCos u ![t,x] := by
  rw [fin2_space_derivative _ _ _ ((levySin_smooth u).differentiable (by norm_num) _)]
  exact (levySin_space u t x).deriv

lemma levyCos_fderiv_second (u t x : ℝ) :
    fderiv ℝ (fderiv ℝ (levyCos u)) ![t,x] (Pi.single 1 1) (Pi.single 1 1)=
      -u^2*levyCos u ![t,x] := by
  rw [fin2_space_second_derivative _ univ isOpen_univ (levyCos_smooth u).contDiffOn t x (by simp)]
  simp_rw [(levyCos_space u t _).deriv]
  convert ((levySin_space u t x).const_mul (-u)).deriv using 1 <;> ring

lemma levySin_fderiv_second (u t x : ℝ) :
    fderiv ℝ (fderiv ℝ (levySin u)) ![t,x] (Pi.single 1 1) (Pi.single 1 1)=
      -u^2*levySin u ![t,x] := by
  rw [fin2_space_second_derivative _ univ isOpen_univ (levySin_smooth u).contDiffOn t x (by simp)]
  simp_rw [(levySin_space u t _).deriv]
  convert ((levyCos_space u t x).const_mul u).deriv using 1 <;> ring

lemma levyCos_harmonic (u t x : ℝ) :
    fderiv ℝ (levyCos u) ![t,x] (Pi.single 0 1)+
      fderiv ℝ (fderiv ℝ (levyCos u)) ![t,x] (Pi.single 1 1) (Pi.single 1 1)/2=0 := by
  rw [levyCos_fderiv_time,levyCos_fderiv_second]; ring

lemma levySin_harmonic (u t x : ℝ) :
    fderiv ℝ (levySin u) ![t,x] (Pi.single 0 1)+
      fderiv ℝ (fderiv ℝ (levySin u)) ![t,x] (Pi.single 1 1) (Pi.single 1 1)/2=0 := by
  rw [levySin_fderiv_time,levySin_fderiv_second]; ring

lemma levyCos_bound (u R t x : ℝ) (ht : t≤R) : |levyCos u ![t,x]|≤Real.exp (u^2*R/2) := by
  simp only [id_eq,levyCos,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.head_cons,abs_mul,
    abs_of_pos (Real.exp_pos _)]
  calc
    _ ≤ Real.exp (u^2*t/2)*1 := mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (Real.exp_pos _).le
    _ ≤ _ := by rw [mul_one]; exact Real.exp_le_exp.mpr (by nlinarith [sq_nonneg u])

lemma levySin_bound (u R t x : ℝ) (ht : t≤R) : |levySin u ![t,x]|≤Real.exp (u^2*R/2) := by
  simp only [id_eq,levySin,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.head_cons,abs_mul,
    abs_of_pos (Real.exp_pos _)]
  calc
    _ ≤ Real.exp (u^2*t/2)*1 := mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) (Real.exp_pos _).le
    _ ≤ _ := by rw [mul_one]; exact Real.exp_le_exp.mpr (by nlinarith [sq_nonneg u])

end Asakura.Chapter4
