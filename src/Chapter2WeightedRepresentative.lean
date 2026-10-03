import Chapter2WeightedEnergy

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal ProbabilityTheory
namespace Asakura.Chapter2Complete
open Asakura.FullAudit
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (a b : ℝ) (hab : a ≤ b) [Fact (a ≤ b)] (A : Ω → ℝ → ℝ)
    (hA : ∀ ω, MonotoneOn (A ω) (Icc a b))
    (hr : ∀ ω x, x ∈ Icc a b → ContinuousWithinAt (A ω) (Icc a b ∩ Ici x) x)
    (hm : ∀ t, Measurable (fun ω => A ω t))
    (K : ℝ) (hK : ∀ ω, A ω b-A ω a ≤ K)
    (F : Icc a b → MeasurableSpace Ω) (hle : ∀ t, F t ≤ ‹MeasurableSpace Ω›)

/-- A common sample null set also gives equality for the concrete weighted
measure and for its progressive restriction. -/
theorem weighted_ae_of_pathwise_ae
    (H J : Ω × Icc a b → ℝ)
    (hH : @Measurable _ _ (progressiveSpace F) inferInstance H)
    (hJ : @Measurable _ _ (progressiveSpace F) inferInstance J)
    (he : ∀ᵐ ω ∂P, ∀ t, H (ω,t) = J (ω,t)) :
    H =ᵐ[(weightedPathMeasure P a b hab A hA hr hm).trim
      (progressive_space_le_product F hle)] J := by
  have hHp : Measurable H := hH.mono (progressive_space_le_product F hle) le_rfl
  have hJp : Measurable J := hJ.mono (progressive_space_le_product F hle) le_rfl
  apply ae_eq_trim_of_measurable (progressive_space_le_product F hle) hH hJ
  have hproj : Measurable (fun p : Ω × ℝ => (p.1,projIcc a b hab p.2)) :=
    measurable_fst.prodMk (continuous_projIcc.measurable.comp measurable_snd)
  apply (ae_map_iff hproj.aemeasurable (measurableSet_eq_fun hHp hJp)).2
  apply Measure.ae_compProd_of_ae_ae
    (measurableSet_eq_fun (hHp.comp hproj) (hJp.comp hproj))
  exact he.mono fun ω hω => .of_forall fun r => hω _

include hK

/-- The null-set removal in the density proof preserves progressiveness
and the L2 equivalence class and makes every path's square integral finite. -/
theorem progressive_L2_finite_path_representative
    (hnull : ∀ t N, MeasurableSet N → P N = 0 → MeasurableSet[F t] N)
    (H : Ω × Icc a b → ℝ)
    (hH : @Measurable _ _ (progressiveSpace F) inferInstance H)
    (hH2 : letI : MeasurableSpace (Ω × Icc a b) := progressiveSpace F
      MemLp H 2 ((weightedPathMeasure P a b hab A hA hr hm).trim
        (progressive_space_le_product F hle))) :
    ∃ J : Ω × Icc a b → ℝ,
      @Measurable _ _ (progressiveSpace F) inferInstance J ∧
      J =ᵐ[(weightedPathMeasure P a b hab A hA hr hm).trim
        (progressive_space_le_product F hle)] H ∧
      ∀ ω, (∫⁻ r, ENNReal.ofReal (J (ω,projIcc a b hab r) ^ 2)
        ∂(intervalStieltjes a b hab (A ω) (hA ω) (hr ω)).measure) < ∞ := by
  classical
  let κ := randomStieltjesKernel a b hab A hA hr hm
  letI : IsFiniteKernel κ := random_stieltjes_kernel_finite a b hab A hA hr hm K hK
  let E := fun ω => ∫⁻ r, ENNReal.ofReal (H (ω,projIcc a b hab r) ^ 2) ∂κ ω
  have hHp : Measurable H := hH.mono (progressive_space_le_product F hle) le_rfl
  have hproj : Measurable (fun p : Ω × ℝ => (p.1,projIcc a b hab p.2)) :=
    measurable_fst.prodMk (continuous_projIcc.measurable.comp measurable_snd)
  have hEm : Measurable E := ((hHp.pow_const 2).ennreal_ofReal.comp hproj).lintegral_kernel_prod_right'
  let N := {ω | E ω = ∞}
  have hNm : MeasurableSet N := hEm (measurableSet_singleton ∞)
  have hfinite : ∀ᵐ ω ∂P, E ω < ∞ :=
    progressive_L2_path_energy_finite P a b hab A hA hr hm K hK F hle H hH hH2
  have hN0 : P N = 0 := by
    have hh := hfinite.mono fun ω hω => hω.ne
    simpa only [ae_iff,not_not] using hh
  let J := fun p : Ω × Icc a b => if p.1 ∈ N then 0 else H p
  have hJ : @Measurable _ _ (progressiveSpace F) inferInstance J := by
    apply (measurable_progressive_iff F J).2
    intro t
    exact Measurable.ite ((hnull t N hNm hN0).preimage measurable_fst)
      measurable_const ((measurable_progressive_iff F H).1 hH t)
  have he : ∀ᵐ ω ∂P, ∀ t, J (ω,t) = H (ω,t) := by
    have hh : ∀ᵐ ω ∂P, ω ∉ N := by
      rw [ae_iff]
      simpa using hN0
    exact hh.mono fun ω hω t => if_neg hω
  refine ⟨J,hJ,weighted_ae_of_pathwise_ae P a b hab A hA hr hm F hle J H hJ hH he,?_⟩
  intro ω
  by_cases hω : ω ∈ N
  · simp only [J,hω,if_pos,zero_pow (by decide : 2 ≠ 0),ENNReal.ofReal_zero,lintegral_zero]
    exact ENNReal.zero_lt_top
  · simp only [J,hω,if_neg]
    exact lt_top_iff_ne_top.2 hω

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.weighted_ae_of_pathwise_ae
#print axioms Asakura.Chapter2Complete.progressive_L2_finite_path_representative
