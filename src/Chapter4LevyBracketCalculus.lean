import Chapter4LevyCalculus
import Chapter4FlowDerivative

open Set
namespace Asakura.Chapter4
open Asakura.Chapter5
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

noncomputable def bracketCos (u : ℝ) (p : Fin 2 → ℝ) := levyCos u ![p 1,p 0]
noncomputable def bracketSin (u : ℝ) (p : Fin 2 → ℝ) := levySin u ![p 1,p 0]

lemma bracketCos_smooth (u : ℝ) : ContDiff ℝ 2 (bracketCos u) := by
  apply (levyCos_smooth u).comp
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;> exact contDiff_apply ℝ ℝ _
lemma bracketSin_smooth (u : ℝ) : ContDiff ℝ 2 (bracketSin u) := by
  apply (levySin_smooth u).comp
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;> exact contDiff_apply ℝ ℝ _

lemma bracketCos_first (u x y : ℝ) :
    fderiv ℝ (bracketCos u) ![x,y] (Pi.single 0 1)=-u*levySin u ![y,x] := by
  have ht := (((bracketCos_smooth u).differentiable (by norm_num)) ![x,y]).hasFDerivAt.comp_hasDerivAt x
    (fin2_time_slice_derivative x y)
  exact ht.unique (by simpa only [bracketCos,Function.comp_def,Matrix.cons_val_zero,Matrix.cons_val_one] using levyCos_space u y x)
lemma bracketSin_first (u x y : ℝ) :
    fderiv ℝ (bracketSin u) ![x,y] (Pi.single 0 1)=u*levyCos u ![y,x] := by
  have ht := (((bracketSin_smooth u).differentiable (by norm_num)) ![x,y]).hasFDerivAt.comp_hasDerivAt x
    (fin2_time_slice_derivative x y)
  exact ht.unique (by simpa only [bracketSin,Function.comp_def,Matrix.cons_val_zero,Matrix.cons_val_one] using levySin_space u y x)

lemma bracketCos_harmonic (u x y : ℝ) :
    fderiv ℝ (bracketCos u) ![x,y] (Pi.single 1 1)+
      fderiv ℝ (fderiv ℝ (bracketCos u)) ![x,y] (Pi.single 0 1) (Pi.single 0 1)/2=0 := by
  have h1 : fderiv ℝ (bracketCos u) ![x,y] (Pi.single 1 1)=u^2/2*levyCos u ![y,x] := by
    have ht := (((bracketCos_smooth u).differentiable (by norm_num)) ![x,y]).hasFDerivAt.comp_hasDerivAt y
      (fin2_space_slice_derivative x y)
    exact ht.unique (by simpa only [bracketCos,Function.comp_def,Matrix.cons_val_zero,Matrix.cons_val_one] using levyCos_time u y x)
  have hd := fin2_partial_time_derivative (bracketCos u) (bracketCos_smooth u) x y 0
  have he : (fun r => fderiv ℝ (bracketCos u) ![r,y] (Pi.single 0 1))=(fun r => -u*levySin u ![y,r]) :=
    funext (fun r => bracketCos_first u r y)
  rw [he] at hd
  have h2 := hd.unique ((levySin_space u y x).const_mul (-u))
  rw [h1,h2]
  ring

lemma bracketSin_harmonic (u x y : ℝ) :
    fderiv ℝ (bracketSin u) ![x,y] (Pi.single 1 1)+
      fderiv ℝ (fderiv ℝ (bracketSin u)) ![x,y] (Pi.single 0 1) (Pi.single 0 1)/2=0 := by
  have h1 : fderiv ℝ (bracketSin u) ![x,y] (Pi.single 1 1)=u^2/2*levySin u ![y,x] := by
    have ht := (((bracketSin_smooth u).differentiable (by norm_num)) ![x,y]).hasFDerivAt.comp_hasDerivAt y
      (fin2_space_slice_derivative x y)
    exact ht.unique (by simpa only [bracketSin,Function.comp_def,Matrix.cons_val_zero,Matrix.cons_val_one] using levySin_time u y x)
  have hd := fin2_partial_time_derivative (bracketSin u) (bracketSin_smooth u) x y 0
  have he : (fun r => fderiv ℝ (bracketSin u) ![r,y] (Pi.single 0 1))=(fun r => u*levyCos u ![y,r]) :=
    funext (fun r => bracketSin_first u r y)
  rw [he] at hd
  have h2 := hd.unique ((levyCos_space u y x).const_mul u)
  rw [h1,h2]
  ring

end Asakura.Chapter4
