import Chapter11LogUtility

open MeasureTheory Set Filter
namespace Asakura.Chapter11
open Asakura.FullAudit
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

/-- The interval-constrained exercise: integrate the pointwise projection
inequality, retain all integrability hypotheses, and prove attainment. -/
theorem constrained_log_utility {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (π : Ω → ℝ → ℝ) (M : Ω → ℝ)
    (x r μ σ T : ℝ) (hx : 0<x) (hσ : σ≠0) (hT : 0≤T)
    (hm : Measurable (Function.uncurry π)) (hb : ∀ w t,π w t∈Icc 0 1)
    (hMi : Integrable M P) (hM0 : (∫ w,M w ∂P)=0) :
    let a := (μ-r)/σ^2
    let p := min 1 (max 0 a)
    let L := Real.log x+(r+p*(μ-r)-σ^2*p^2/2)*T
    (∫ w,Real.log (terminalLogWealth π M x r μ σ T w) ∂P)≤L ∧
      ((∀ w t,π w t=p) → (∫ w,Real.log (terminalLogWealth π M x r μ σ T w) ∂P)=L) := by
  dsimp only
  let a := (μ-r)/σ^2
  let p := min 1 (max 0 a)
  have hbound w t : ‖π w t‖≤1 := by
    rw [Real.norm_eq_abs,abs_of_nonneg (hb w t).1]
    exact (hb w t).2
  have he := (logarithmic_wealth_identity P π M x r μ σ T 1 hx hσ hT hm hbound hMi hM0).2
  have hi : Integrable (fun z : Ω × ℝ => (π z.1 z.2-a)^2) (P.prod (volume.restrict (Icc 0 T))) := by
    have hh : MemLp (Function.uncurry π) 2 (P.prod (volume.restrict (Icc 0 T))) :=
      MemLp.of_bound hm.aestronglyMeasurable 1 (ae_of_all _ fun z => hbound z.1 z.2)
    exact (memLp_two_iff_integrable_sq (hh.sub (memLp_const a)).aestronglyMeasurable).mp (hh.sub (memLp_const a))
  have hmass : (volume.restrict (Icc 0 T)).real univ=T := by
    rw [Measure.real,Measure.restrict_apply_univ,Real.volume_Icc,sub_zero,ENNReal.toReal_ofReal hT]
  have hlo : (p-a)^2*T≤∫ w,(∫ t in Icc 0 T,(π w t-a)^2) ∂P := by
    have hpoint w : (p-a)^2*T≤∫ t in Icc 0 T,(π w t-a)^2 := by
      have hp : MemLp (π w) 2 (volume.restrict (Icc 0 T)) :=
        MemLp.of_bound (hm.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable 1
          (ae_of_all _ (hbound w))
      have hip := (memLp_two_iff_integrable_sq (hp.sub (memLp_const a)).aestronglyMeasurable).mp (hp.sub (memLp_const a))
      have hh := integral_mono (integrable_const ((p-a)^2)) hip (fun t => finance_interval_projection a (π w t) (hb w t))
      simpa only [integral_const,hmass,smul_eq_mul,mul_comm,Pi.sub_apply] using hh
    simpa only [integral_const,probReal_univ,one_smul] using
      integral_mono (integrable_const ((p-a)^2*T)) hi.integral_prod_left hpoint
  have hs := finance_log_square r μ σ p hσ
  constructor
  · rw [he]
    have hmul := mul_le_mul_of_nonneg_left hlo (show 0≤σ^2/2 by positivity)
    change _≤Real.log x+(r+p*(μ-r)-σ^2*p^2/2)*T
    dsimp only [a] at hmul
    nlinarith only [hmul,congrArg (fun z => z*T) hs]
  · intro hp
    rw [he]
    simp only [hp,integral_const,hmass,smul_eq_mul,probReal_univ,one_mul]
    change Real.log x+(r+(μ-r)^2/(2*σ^2))*T-σ^2/2*(T*(p-a)^2)=_
    dsimp only [a] at *
    change _=Real.log x+(r+p*(μ-r)-σ^2*p^2/2)*T
    rw [hs]
    ring

end Asakura.Chapter11
