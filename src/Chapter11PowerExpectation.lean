import FullAuditMertonVerification
import Chapter11ExponentialTransform

open MeasureTheory Set Filter
open scoped ENNReal
namespace Asakura.Chapter11
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter5 Asakura.Chapter6
set_option maxHeartbeats 3500000
set_option backward.isDefEq.respectTransparency false

theorem power_transform_drift_square (r μ σ γ z : ℝ) (hσ : σ≠0) (hγ : γ≠0) (hγ1 : γ≠1) :
    ((1-γ)*(r+z*(μ-r)-σ^2*z^2/2)-mertonRate r μ σ γ+((1-γ)*(σ*z))^2/2)/(1-γ)=
      -(γ*σ^2/2)*(z-(μ-r)/(γ*σ^2))^2 := by
  dsimp only [mertonRate]
  field_simp
  <;> ring

/-- Take expectations in the constructed transformed equation. The loss is
integrable and nonnegative even when the utility denominator is negative. -/
theorem power_transform_expected_bound {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (U π : Ω × ℝ → ℝ) (M : Ω → ℝ)
    (r μ σ γ T c K : ℝ) (hσ : σ≠0) (hγ : 0<γ) (hγ1 : γ≠1) (hT : 0≤T)
    (hU : Measurable U) (hπ : Measurable π) (hpos : ∀ z,0<U z) (hb : ∀ z,|π z|≤K)
    (hUi : Integrable U (P.prod (volume.restrict (Icc 0 T))))
    (hMi : Integrable M P) (hM0 : (∫ w,M w ∂P)=0)
    (hIto : ∀ᵐ w ∂P,U (w,T)=c+
      (∫ s in 0..T,U (w,s)*((1-γ)*(r+π (w,s)*(μ-r)-σ^2*(π (w,s))^2/2)-mertonRate r μ σ γ+((1-γ)*(σ*π (w,s)))^2/2))+M w) :
    Integrable (fun w => U (w,T)/(1-γ)) P ∧
    (∫ w,U (w,T)/(1-γ) ∂P)=c/(1-γ)-γ*σ^2/2*(∫ w,(∫ s in Icc 0 T,U (w,s)*(π (w,s)-(μ-r)/(γ*σ^2))^2) ∂P) ∧
    (∫ w,U (w,T)/(1-γ) ∂P)≤c/(1-γ) := by
  let a := (μ-r)/(γ*σ^2)
  let ν := volume.restrict (Icc 0 T)
  have hp : MemLp π ∞ (P.prod ν) := MemLp.of_bound hπ.aestronglyMeasurable K
    (ae_of_all _ fun z => by simpa only [Real.norm_eq_abs] using hb z)
  have hd : MemLp (fun z => (π z-a)^2) ∞ (P.prod ν) := by
    have hh := hp.sub (memLp_const a)
    simpa only [pow_two,Pi.sub_apply] using hh.fun_mul hh
  have hLoss : Integrable (fun z => U z*(π z-a)^2) (P.prod ν) := by
    convert hd.integrable_mul (memLp_one_iff_integrable.mpr hUi) using 1
    funext z
    simp only [Pi.mul_apply]
    ring
  have hLi : Integrable (fun w => ∫ s,U (w,s)*(π (w,s)-a)^2 ∂ν) P := hLoss.integral_prod_left
  have he : (fun w => U (w,T)/(1-γ))=ᵐ[P]
      fun w => c/(1-γ)-γ*σ^2/2*(∫ s,U (w,s)*(π (w,s)-a)^2 ∂ν)+M w/(1-γ) := by
    filter_upwards [hIto] with w hw
    rw [hw,add_div,add_div,←intervalIntegral.integral_div]
    have hh : (fun s => U (w,s)*((1-γ)*(r+π (w,s)*(μ-r)-σ^2*(π (w,s))^2/2)-mertonRate r μ σ γ+((1-γ)*(σ*π (w,s)))^2/2)/(1-γ))=
        fun s => -(γ*σ^2/2)*(U (w,s)*(π (w,s)-a)^2) := by
      funext s
      rw [mul_div_assoc,power_transform_drift_square r μ σ γ _ hσ (ne_of_gt hγ) hγ1]
      ring
    rw [hh,intervalIntegral.integral_const_mul,intervalIntegral.integral_of_le hT,←integral_Icc_eq_integral_Ioc]
    dsimp only [ν]
    ring
  have hbase : Integrable (fun w => c/(1-γ)-γ*σ^2/2*(∫ s,U (w,s)*(π (w,s)-a)^2 ∂ν)) P :=
    (integrable_const _).sub (hLi.const_mul _)
  have hutil := (hbase.add (hMi.div_const _)).congr he.symm
  have hmean : (∫ w,U (w,T)/(1-γ) ∂P)=c/(1-γ)-γ*σ^2/2*(∫ w,(∫ s,U (w,s)*(π (w,s)-a)^2 ∂ν) ∂P) := by
    rw [integral_congr_ae he,integral_add hbase (hMi.div_const _),integral_div,hM0,zero_div,add_zero,
      integral_sub (integrable_const _) (hLi.const_mul _),integral_const,probReal_univ,one_smul,integral_const_mul]
  refine ⟨hutil,hmean,?_⟩
  rw [hmean]
  have hn : 0≤∫ w,(∫ s,U (w,s)*(π (w,s)-a)^2 ∂ν) ∂P :=
    integral_nonneg fun w => integral_nonneg fun s => mul_nonneg (hpos _).le (sq_nonneg _)
  have : 0≤γ*σ^2/2*(∫ w,(∫ s,U (w,s)*(π (w,s)-a)^2 ∂ν) ∂P) := by positivity
  linarith

end Asakura.Chapter11
