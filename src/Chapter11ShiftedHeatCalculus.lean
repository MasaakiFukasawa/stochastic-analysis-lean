import Chapter11HeatToBlackScholes
import Chapter3GradientCalculus

open Set Filter
open scoped Topology ContDiff
namespace Asakura.Chapter11
set_option maxHeartbeats 3500000
set_option backward.isDefEq.respectTransparency false

noncomputable def shiftedBrownianHeatPrice (F : ℝ × ℝ → ℝ) (A σ T c κ : ℝ) (q : Fin 2 → ℝ) : ℝ :=
  A*F (σ^2*(T-q 0),c+σ*q 1+κ*q 0)

theorem shifted_brownian_heat_smooth_at (F : ℝ × ℝ → ℝ)
    (hF : ContDiffOn ℝ ∞ F {q | 0<q.1}) (A σ T c κ : ℝ) (hσ : σ≠0)
    (q : Fin 2 → ℝ) (hq : q 0<T) : ContDiffAt ℝ ∞ (shiftedBrownianHeatPrice F A σ T c κ) q := by
  have hm : ContDiffAt ℝ ∞ (fun q : Fin 2 → ℝ => (σ^2*(T-q 0),c+σ*q 1+κ*q 0)) q := by fun_prop
  exact contDiffAt_const.mul ((hF.contDiffAt ((isOpen_lt continuous_const continuous_fst).mem_nhds
    (mul_pos (sq_pos_of_ne_zero hσ) (sub_pos.mpr hq)))).comp q hm)

theorem shifted_brownian_heat_first (F : ℝ × ℝ → ℝ)
    (hF : ContDiffOn ℝ ∞ F {q | 0<q.1}) (A σ T c κ : ℝ) (hσ : σ≠0)
    (q h : Fin 2 → ℝ) (hq : q 0<T) :
    fderiv ℝ (shiftedBrownianHeatPrice F A σ T c κ) q h=
      A*fderiv ℝ F (σ^2*(T-q 0),c+σ*q 1+κ*q 0) (-σ^2*h 0,σ*h 1+κ*h 0) := by
  have hs : ContDiffAt ℝ ∞ F (σ^2*(T-q 0),c+σ*q 1+κ*q 0) :=
    hF.contDiffAt ((isOpen_lt continuous_const continuous_fst).mem_nhds
      (mul_pos (sq_pos_of_ne_zero hσ) (sub_pos.mpr hq)))
  have hm := (((hasFDerivAt_const (c:=T) q).sub (hasFDerivAt_apply (𝕜:=ℝ) 0 q)).const_mul (σ^2)).prodMk
    ((((hasFDerivAt_apply (𝕜:=ℝ) 1 q).const_mul σ).const_add c).add ((hasFDerivAt_apply (𝕜:=ℝ) 0 q).const_mul κ))
  have hd := (((hs.differentiableAt (by simp)).hasFDerivAt).comp q hm).const_mul A
  simp only [Function.comp_def,Pi.sub_apply,Pi.add_apply] at hd
  rw [show shiftedBrownianHeatPrice F A σ T c κ=(fun q : Fin 2 → ℝ => A*F (σ^2*(T-q 0),c+σ*q 1+κ*q 0)) from rfl,hd.fderiv]
  simp only [ContinuousLinearMap.smul_apply,ContinuousLinearMap.comp_apply,ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.add_apply,ContinuousLinearMap.sub_apply,ContinuousLinearMap.zero_apply,ContinuousLinearMap.proj_apply,smul_eq_mul]
  congr 2
  ext <;> simp <;> ring

theorem shifted_brownian_heat_second (F : ℝ × ℝ → ℝ)
    (hF : ContDiffOn ℝ ∞ F {q | 0<q.1}) (A σ T c κ : ℝ) (hσ : σ≠0)
    (q : Fin 2 → ℝ) (hq : q 0<T) :
    fderiv ℝ (fderiv ℝ (shiftedBrownianHeatPrice F A σ T c κ)) q (Pi.single 1 1) (Pi.single 1 1)=
      A*σ^2*fderiv ℝ (fderiv ℝ F) (σ^2*(T-q 0),c+σ*q 1+κ*q 0) (0,1) (0,1) := by
  let v := shiftedBrownianHeatPrice F A σ T c κ
  let z := (σ^2*(T-q 0),c+σ*q 1+κ*q 0)
  have hs := shifted_brownian_heat_smooth_at F hF A σ T c κ hσ q hq
  have hgrad : (fun p => fderiv ℝ v p (Pi.single 1 1))=ᶠ[𝓝 q]
      (fun p : Fin 2 → ℝ => A*σ*fderiv ℝ F (σ^2*(T-p 0),c+σ*p 1+κ*p 0) (0,1)) := by
    filter_upwards [(isOpen_lt (continuous_apply 0) continuous_const).mem_nhds hq] with p hp
    rw [shifted_brownian_heat_first F hF A σ T c κ hσ p _ hp]
    simp only [Pi.single_eq_same,Pi.single_eq_of_ne (by decide : (0:Fin 2)≠1),mul_zero,mul_one,add_zero]
    rw [show ((0:ℝ),σ)=σ • (0,1) by ext <;> simp,map_smul,smul_eq_mul]
    ring
  have hFs : ContDiffAt ℝ ∞ F z := hF.contDiffAt ((isOpen_lt continuous_const continuous_fst).mem_nhds
    (mul_pos (sq_pos_of_ne_zero hσ) (sub_pos.mpr hq)))
  have hFd : DifferentiableAt ℝ (fderiv ℝ F) z := (hFs.fderiv_right (m:=1) (by simp)).differentiableAt (by simp)
  have hm := (((hasFDerivAt_const (c:=T) q).sub (hasFDerivAt_apply (𝕜:=ℝ) 0 q)).const_mul (σ^2)).prodMk
    ((((hasFDerivAt_apply (𝕜:=ℝ) 1 q).const_mul σ).const_add c).add ((hasFDerivAt_apply (𝕜:=ℝ) 0 q).const_mul κ))
  have hd := ((hFd.hasFDerivAt.comp q hm).clm_apply (hasFDerivAt_const (c:=((0:ℝ),1)) q)).const_mul (A*σ)
  simp only [Function.comp_def,Pi.sub_apply,Pi.add_apply] at hd
  have hvd : DifferentiableAt ℝ (fderiv ℝ v) q := (hs.fderiv_right (m:=1) (by simp)).differentiableAt (by simp)
  have hgder : fderiv ℝ (fun p => fderiv ℝ v p (Pi.single 1 1)) q (Pi.single 1 1)=
      fderiv ℝ (fderiv ℝ v) q (Pi.single 1 1) (Pi.single 1 1) := by
    rw [fderiv_clm_apply hvd (differentiableAt_const _)]
    simp
  rw [←hgder,hgrad.fderiv_eq,hd.fderiv]
  simp only [ContinuousLinearMap.smul_apply,ContinuousLinearMap.comp_apply,ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.add_apply,ContinuousLinearMap.sub_apply,ContinuousLinearMap.zero_apply,ContinuousLinearMap.proj_apply,
    ContinuousLinearMap.add_apply,neg_apply,ContinuousLinearMap.flip_apply,smul_eq_mul,
    Pi.single_eq_same,Pi.single_eq_of_ne (by decide : (0:Fin 2)≠1),mul_zero,mul_one,sub_zero,zero_sub,
    map_zero,zero_add,add_zero,neg_zero]
  rw [show ((0:ℝ),σ)=σ • (0,1) by ext <;> simp,map_smul,ContinuousLinearMap.smul_apply,smul_eq_mul]
  dsimp only [z]
  ring

/-- The shift from risk-neutral to original Brownian coordinates adds
precisely the excess-return multiple of the spatial derivative. -/
theorem shifted_brownian_heat_harmonic (F : ℝ × ℝ → ℝ)
    (hF : ContDiffOn ℝ ∞ F {q | 0<q.1})
    (hHeat : ∀ t y,0<t → deriv (fun s => F (s,y)) t=(1/2:ℝ)*deriv (deriv (fun a => F (t,a))) y)
    (A σ T c κ : ℝ) (hσ : σ≠0) (t x : ℝ) (ht : t<T) :
    fderiv ℝ (shiftedBrownianHeatPrice F A σ T c κ) ![t,x] (Pi.single 0 1)+
      fderiv ℝ (fderiv ℝ (shiftedBrownianHeatPrice F A σ T c κ)) ![t,x] (Pi.single 1 1) (Pi.single 1 1)/2=(κ/σ)*fderiv ℝ (shiftedBrownianHeatPrice F A σ T c κ) ![t,x] (Pi.single 1 1) := by
  let τ := σ^2*(T-t)
  let y := c+σ*x+κ*t
  have hτ : 0<τ := mul_pos (sq_pos_of_ne_zero hσ) (sub_pos.mpr ht)
  have hs a : ContDiffAt ℝ ∞ F (τ,a) := hF.contDiffAt ((isOpen_lt continuous_const continuous_fst).mem_nhds hτ)
  have hdt : fderiv ℝ F (τ,y) (1,0)=deriv (fun s => F (s,y)) τ := by
    simpa only [iteratedFDeriv_one_apply] using (scalar_time_slice_derivative F τ y (hs y)).deriv.symm
  have hdd : fderiv ℝ (fderiv ℝ F) (τ,y) (0,1) (0,1)=deriv (deriv (fun a => F (τ,a))) y := by
    simpa only [iteratedFDeriv_two_apply] using scalar_space_second_jet F τ y hs
  rw [shifted_brownian_heat_first F hF A σ T c κ hσ _ _ (by simpa using ht),
    shifted_brownian_heat_second F hF A σ T c κ hσ _ (by simpa using ht),
    shifted_brownian_heat_first F hF A σ T c κ hσ _ _ (by simpa using ht)]
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Pi.single_eq_same,
    Pi.single_eq_of_ne (by decide : (1:Fin 2)≠0),
    Pi.single_eq_of_ne (by decide : (0:Fin 2)≠1),mul_zero,mul_one,add_zero,zero_add]
  rw [show (-σ^2,κ)=(-σ^2) • ((1:ℝ),0)+κ • (0,1) by ext <;> simp,
    show ((0:ℝ),σ)=σ • ((0:ℝ),1) by ext <;> simp,
    map_add,map_smul,map_smul,map_smul]
  simp only [smul_eq_mul]
  change A*((-σ^2)*fderiv ℝ F (τ,y) (1,0)+κ*fderiv ℝ F (τ,y) (0,1))+
    (A*σ^2*fderiv ℝ (fderiv ℝ F) (τ,y) (0,1) (0,1))/2=
      (κ/σ)*(A*(σ*fderiv ℝ F (τ,y) (0,1)))
  rw [hdt,hdd,hHeat τ y hτ]
  field_simp
  ring

end Asakura.Chapter11
