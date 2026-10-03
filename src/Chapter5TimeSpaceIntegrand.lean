import Chapter5TimeSpaceDensity

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter5
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete
set_option backward.isDefEq.respectTransparency false

/-- Continuous functions of time and a continuous semimartingale supply
all measurability and path-regularity inputs to integral composition. -/
theorem time_space_integrand_regularity
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)]
    (F : ClosedTime T → MeasurableSpace Ω)
    (X A M : ClosedTime T → Ω → ℝ) (hX : SemimartingaleDecomposition P F X A M)
    (R : ℝ) (hR : 0 ≤ R) (ψ : (Fin 2 → ℝ) → ℝ) (hψ : Continuous ψ) :
    let H := fun z : Ω × ℝ => ψ ![(finitePrefixTime (T := T) R hR (realTimeClamp z.2)).val,
      X (realTimeClamp z.2) z.1]
    (∀ w, Measurable (fun r => H (w,r))) ∧
    (∀ r : ℝ, 0 ≤ r → (r:EReal) < T → Measurable[F (realTimeClamp r)] (fun w => H (w,r))) ∧
    (∀ b : ℝ, 0 ≤ b → (b:EReal) < T → ∀ w, ContinuousOn (fun r => H (w,r)) (Icc 0 b)) := by
  dsimp only
  have hK : Continuous (fun r : ℝ => (finitePrefixTime (T := T) R hR (realTimeClamp r)).val) :=
    continuous_subtype_val.comp ((finite_prefix_time_continuous R hR).comp real_time_clamp_continuous)
  have hfinite (r : ℝ) (hr : 0 ≤ r) (hrT : (r:EReal) < T) : realTimeClamp (T := T) r < ⊤ := by
    change (realTimeClamp r : EReal) < T
    rw [real_time_clamp_eq r hr hrT.le]; exact hrT
  refine ⟨?_,?_,?_⟩
  · intro w
    apply hψ.measurable.comp
    apply Measurable.of_eval
    intro i
    fin_cases i
    · exact hK.measurable
    · exact open_path_real_measurable _ (hX.continuous w)
  · intro r hr hrT
    letI : MeasurableSpace Ω := F (realTimeClamp r)
    apply hψ.measurable.comp
    apply Measurable.of_eval
    intro i
    fin_cases i
    · exact measurable_const
    · have he : X (realTimeClamp r) = fun w => A (realTimeClamp r) w+M (realTimeClamp r) w :=
        funext (hX.decomposition _ (hfinite r hr hrT))
      change Measurable[F (realTimeClamp r)] (X (realTimeClamp r))
      rw [he]
      exact (hX.variation.adapted _ (hfinite r hr hrT)).add (hX.martingale.adapted P F _ (hfinite r hr hrT))
  · intro b hb hbT w
    apply hψ.comp_continuousOn
    intro r hr
    apply ContinuousAt.continuousWithinAt
    apply continuousAt_pi.mpr
    intro i
    fin_cases i
    · exact hK.continuousAt
    · exact (hX.continuous w _ (hfinite r hr.1 ((EReal.coe_le_coe hr.2).trans_lt hbT))).comp
        real_time_clamp_continuous.continuousAt

/-- A Borel coefficient evaluated on an adapted continuous solution is
progressive; continuity of the coefficient is not an extra assumption. -/
theorem borel_diffusion_progressive
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)]
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F)
    (X A M : ClosedTime T → Ω → ℝ) (hX : SemimartingaleDecomposition P F X A M)
    (b : ℝ) (hb : 0 ≤ b) (hbT : (b:EReal) < T)
    (σ : ℝ × ℝ → ℝ) (hσ : Measurable σ) :
    @Measurable _ _ (progressiveSpace (fun t : Icc (0:ℝ) b => F (realTimeClamp t.val))) inferInstance
      (fun z : Ω × Icc (0:ℝ) b => σ (z.2.val,X (realTimeClamp z.2.val) z.1)) := by
  have hfinite (r : ℝ) (hr : r ∈ Icc 0 b) : realTimeClamp (T := T) r < ⊤ := by
    change (realTimeClamp r : EReal) < T
    rw [real_time_clamp_eq r hr.1 ((EReal.coe_le_coe hr.2).trans hbT.le)]
    exact (EReal.coe_le_coe hr.2).trans_lt hbT
  have hxp := continuous_adapted_real_progressive F hF
    (fun z : Ω × ℝ => X (realTimeClamp z.2) z.1) b hb (by
      intro r hr
      have he : X (realTimeClamp r) = fun w => A (realTimeClamp r) w+M (realTimeClamp r) w :=
        funext (hX.decomposition _ (hfinite r hr))
      change Measurable[F (realTimeClamp r)] (X (realTimeClamp r))
      rw [he]
      exact (hX.variation.adapted _ (hfinite r hr)).add (hX.martingale.adapted P F _ (hfinite r hr)))
    (fun w r hr => ((hX.continuous w _ (hfinite r hr)).comp real_time_clamp_continuous.continuousAt).continuousWithinAt)
  have htp := continuous_adapted_real_progressive F hF
    (fun z : Ω × ℝ => z.2) b hb (fun _ _ => measurable_const) (fun _ => continuousOn_id)
  exact hσ.comp (htp.prodMk hxp)

end Asakura.Chapter5
