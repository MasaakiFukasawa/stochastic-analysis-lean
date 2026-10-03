import Chapter10KyleOrderAdmissibility

open MeasureTheory Set Filter
namespace Asakura.Chapter10
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

/-- The equilibrium gain process satisfies the absolute-integrability part
of admissibility. Fubini also gives its unconditional expected profit. -/
theorem kyle_equilibrium_profit_integrable {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (E : ℝ → Ω → ℝ)
    (hm : Measurable (Function.uncurry E)) (h2 : ∀ t,MemLp (E t) 2 P)
    (S0 T l : ℝ) (hS : 0≤S0) (hT : 0<T) (hl : 0<l)
    (hvar : ∀ t∈Ioo 0 T,(∫ w,(E t w)^2 ∂P)=S0*(T-t)/T) :
    Integrable (fun z : ℝ × Ω => (E z.1 z.2)^2/(l*(T-z.1))) ((volume.restrict (Ioo 0 T)).prod P) ∧
      (∫ w,(∫ t,(E t w)^2/(l*(T-t)) ∂volume.restrict (Ioo 0 T)) ∂P)=S0/l := by
  let ν := volume.restrict (Ioo (0:ℝ) T)
  let U := fun t w => (E t w)^2/(l*(T-t))
  have hUm : Measurable (Function.uncurry U) :=
    (hm.pow_const 2).div (measurable_const.mul (measurable_const.sub measurable_fst))
  have hUi t : Integrable (U t) P := (h2 t).integrable_sq.div_const _
  have hmean t (ht : t∈Ioo 0 T) : (∫ w,U t w ∂P)=S0/(l*T) := by
    dsimp only [U]
    rw [integral_div,hvar t ht]
    field_simp [hT.ne',hl.ne',(sub_pos.mpr ht.2).ne']
  have hnorm t (ht : t∈Ioo 0 T) : (∫ w,‖U t w‖ ∂P)=S0/(l*T) := by
    have he : (fun w => ‖U t w‖)=U t := by
      funext w
      exact Real.norm_of_nonneg (div_nonneg (sq_nonneg _) (mul_pos hl (sub_pos.mpr ht.2)).le)
    rw [he,hmean t ht]
  have hi : Integrable (Function.uncurry U) (ν.prod P) := by
    apply (integrable_prod_iff hUm.aestronglyMeasurable).mpr
    refine ⟨ae_of_all _ hUi,?_⟩
    apply (integrable_const (S0/(l*T))).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact (hnorm t ht).symm
  refine ⟨hi,?_⟩
  change (∫ w,(∫ t,U t w ∂ν) ∂P)=S0/l
  rw [← integral_integral_swap hi]
  have he : (fun t => ∫ w,U t w ∂P)=ᵐ[ν] (fun _ => S0/(l*T)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact hmean t ht
  change (∫ t,(∫ w,U t w ∂P) ∂ν)=S0/l
  rw [integral_congr_ae he,integral_const]
  simp only [ν,Measure.real,Measure.restrict_apply_univ,Real.volume_Ioo,sub_zero,
    ENNReal.toReal_ofReal hT.le,smul_eq_mul]
  field_simp

end Asakura.Chapter10
