import Chapter10KyleOrderMoment

open MeasureTheory Set Filter
open scoped ENNReal
namespace Asakura.Chapter10
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

lemma terminal_inverse_not_integrable (T : ℝ) (hT : 0<T) :
    ¬IntegrableOn (fun t => (T-t)⁻¹) (Ioo 0 T) volume := by
  intro hi
  have h := (intervalIntegrable_iff_integrableOn_Ioo_of_le hT.le).mpr hi
  have hh := h.comp_sub_left T
  have hh' : IntervalIntegrable (fun t : ℝ => t⁻¹) volume 0 T := by
    simpa only [sub_sub_cancel,sub_zero,sub_self] using hh.symm
  have hr : IntegrableOn (fun t : ℝ => t^(-1:ℝ)) (Ioo 0 T) volume := by
    simpa only [Real.rpow_neg_one] using (intervalIntegrable_iff_integrableOn_Ioo_of_le hT.le).mp hh'
  have hf := (intervalIntegral.integrableOn_Ioo_rpow_iff hT).mp hr
  norm_num at hf

/-- The actual second moment of the equilibrium order speed has infinite
time integral. This is compatible with the already proved L1 admissibility. -/
theorem kyle_order_energy_infinite {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (E : ℝ → Ω → ℝ) (S0 T l : ℝ)
    (hS : 0<S0) (hT : 0<T) (hl : 0<l)
    (hvar : ∀ t∈Ioo 0 T,(∫ w,(E t w)^2 ∂P)=S0*(T-t)/T) :
    (∫⁻ t,ENNReal.ofReal (∫ w,(E t w/(l*(T-t)))^2 ∂P) ∂volume.restrict (Ioo 0 T))=⊤ := by
  let ν := volume.restrict (Ioo (0:ℝ) T)
  let K := S0/(T*l^2)
  have hK : 0<K := div_pos hS (mul_pos hT (sq_pos_of_pos hl))
  let f := fun t => K*(T-t)⁻¹
  have he : (fun t => ∫ w,(E t w/(l*(T-t)))^2 ∂P)=ᵐ[ν] f := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    simp_rw [div_pow]
    rw [integral_div,hvar t ht]
    dsimp only [f,K]
    field_simp [hT.ne',hl.ne',(sub_pos.mpr ht.2).ne']
    <;> ring
  have hfm : Measurable f := measurable_const.mul ((measurable_const.sub measurable_id).inv)
  have hfn : 0≤ᵐ[ν] f := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact mul_nonneg hK.le (inv_nonneg.mpr (sub_pos.mpr ht.2).le)
  have hni : ¬Integrable f ν := by
    intro hf
    have hh := hf.const_mul K⁻¹
    have heq : (fun t => K⁻¹*f t)=(fun t => (T-t)⁻¹) := by
      funext t
      dsimp only [f]
      rw [←mul_assoc,inv_mul_cancel₀ hK.ne',one_mul]
    rw [heq] at hh
    exact terminal_inverse_not_integrable T hT hh
  change (∫⁻ t,ENNReal.ofReal (∫ w,(E t w/(l*(T-t)))^2 ∂P) ∂ν)=⊤
  rw [lintegral_congr_ae (he.mono (fun t ht => congrArg ENNReal.ofReal ht))]
  by_contra hh
  exact hni ⟨hfm.aestronglyMeasurable,(hasFiniteIntegral_iff_ofReal hfn).mpr (lt_top_iff_ne_top.mpr hh)⟩

end Asakura.Chapter10
