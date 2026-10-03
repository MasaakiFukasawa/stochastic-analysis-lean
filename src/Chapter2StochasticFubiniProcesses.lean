import Chapter2ItoFubiniOperator
import Chapter2MixedL2PointwiseIntegrable

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

/-- The operator Fubini equality is realized by actual Ito-integral processes
on both sides, including the terminal values. The pointwise mean integrand
is progressive by the joint progressive measurability in the printed premise. -/
theorem stochastic_fubini_actual_processes
    {Ω E : Type*} {m : MeasurableSpace Ω} [MeasurableSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (X : ClosedTime T → Ω → ℝ) (c : ℕ → ℝ)
    (μ : Measure E) [SigmaFinite μ] (ν : Measure (Ω × ℝ)) [SigmaFinite ν]
    (L : progressiveEnergyRange F c ν →ₗᵢ[ℝ] continuousM2Terminal P F)
    (hIto : ∀ G : progressiveEnergyIntegrands F c ν,
      ∃ Y : ClosedTime T → Ω → ℝ, ∃ hY : ContinuousM2Witness P F Y,
        ItoCovarianceFormula P F X G.val Y ∧
        L ⟨progressiveEnergyToLp F c ν G,LinearMap.mem_range_self _ G⟩ = m2TerminalOfProcess P F Y hY)
    (H : E × (Ω × ℝ) → ℝ) (hH : Measurable H)
    (hp : ∀ n, @Measurable _ _
      ((inferInstance : MeasurableSpace E).prod (progressiveSpace (fun t : Icc (0:ℝ) (c n) => F (realTimeClamp t.val)))) inferInstance
      (fun z : E × (Ω × Icc (0:ℝ) (c n)) => H (z.1,(z.2.1,z.2.2.val))))
    (hN : (∫⁻ x, eLpNorm (fun z => H (x,z)) 2 ν ∂μ) < ∞) :
    (∀ᵐ z ∂ν, Integrable (fun x => H (x,z)) μ) ∧
    ∃ Z : E → continuousM2Terminal P F, Integrable Z μ ∧
      (∀ᵐ x ∂μ, ∃ Y : ClosedTime T → Ω → ℝ, ∃ hY : ContinuousM2Witness P F Y,
        ItoCovarianceFormula P F X (fun z => H (x,z)) Y ∧ Z x = m2TerminalOfProcess P F Y hY) ∧
      ∃ Ybar : ClosedTime T → Ω → ℝ, ∃ hYbar : ContinuousM2Witness P F Ybar,
        ItoCovarianceFormula P F X (fun z => ∫ x, H (x,z) ∂μ) Ybar ∧
        (∫ x, Z x ∂μ) = m2TerminalOfProcess P F Ybar hYbar := by
  have hpx x n : @Measurable _ _
      (progressiveSpace (fun t : Icc (0:ℝ) (c n) => F (realTimeClamp t.val))) inferInstance
      (fun z : Ω × Icc (0:ℝ) (c n) => H (x,(z.1,z.2.val))) :=
    (hp n).comp measurable_prodMk_left
  obtain ⟨U,hU,hUI,hLI,g,hg,hcomm⟩ := ito_fubini_for_actual_operator P F hF hle hnull c μ ν L H hH hpx hN
  have hgood := (integrable_l2Section μ ν H hH hN).2.1
  let Hbar := fun z => ∫ x, H (x,z) ∂μ
  have hbarL : MemLp Hbar 2 ν := (Lp.memLp (g : Lp ℝ 2 ν)).ae_eq hg
  have hbarM : Measurable Hbar := hH.stronglyMeasurable.integral_prod_left'.measurable
  have hbarP n : @Measurable _ _
      (progressiveSpace (fun t : Icc (0:ℝ) (c n) => F (realTimeClamp t.val))) inferInstance
      (fun z : Ω × Icc (0:ℝ) (c n) => Hbar (z.1,z.2.val)) := by
    letI : MeasurableSpace (Ω × Icc (0:ℝ) (c n)) :=
      progressiveSpace (fun t : Icc (0:ℝ) (c n) => F (realTimeClamp t.val))
    exact (hp n).stronglyMeasurable.integral_prod_left'.measurable
  let G : progressiveEnergyIntegrands F c ν := ⟨Hbar,hbarM,hbarP,hbarL⟩
  have hge : g = ⟨progressiveEnergyToLp F c ν G,LinearMap.mem_range_self _ G⟩ := by
    apply Subtype.ext
    apply Lp.ext
    exact hg.trans hbarL.coeFn_toLp.symm
  obtain ⟨Ybar,hYbar,hbarChar,hbarTerm⟩ := hIto G
  refine ⟨mixed_l1_l2_pointwise_integrable μ ν H hH hN,
    (fun x => L (U x)),hLI,?_,Ybar,hYbar,hbarChar,?_⟩
  · filter_upwards [hgood] with x hx
    let Gx : progressiveEnergyIntegrands F c ν :=
      ⟨fun z => H (x,z),hH.comp measurable_prodMk_left,hpx x,hx.choose⟩
    have he : U x = ⟨progressiveEnergyToLp F c ν Gx,LinearMap.mem_range_self _ Gx⟩ := by
      apply Subtype.ext
      exact (hU x).trans hx.choose_spec
    obtain ⟨Y,hY,hchar,hterm⟩ := hIto Gx
    exact ⟨Y,hY,hchar,by rw [he]; exact hterm⟩
  · exact hcomm.trans (by rw [hge]; exact hbarTerm)

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.stochastic_fubini_actual_processes
