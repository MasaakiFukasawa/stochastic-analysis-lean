import Chapter2FubiniCovarianceSeparation
import Chapter2ActualItoOperator
import Chapter2ItoParameterIntegrability
import Chapter2L2FubiniMinkowski
import Chapter2MixedL2PointwiseIntegrable

open MeasureTheory Set Filter
open scoped Topology ENNReal Classical
namespace Asakura.Chapter2Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false

theorem ItoCovarianceFormula.congr_integral
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (X Y Z : ClosedTime T → Ω → ℝ) (H : Ω × ℝ → ℝ)
    (hY : LocalMProcessWitness P F Y) (hZ : LocalMProcessWitness P F Z)
    (he : ∀ᵐ ω ∂P, ∀ t, t < ⊤ → Y t ω = Z t ω)
    (hI : ItoCovarianceFormula P F X H Y) : ItoCovarianceFormula P F X H Z := by
  intro N C hN hC
  obtain ⟨D,hD,hform⟩ := hI N C hN hC
  exact ⟨D,hD.congr_ae_processes P F hF hle hY hN hZ hN he
    (.of_forall (fun _ _ _ => rfl)),hform⟩

/-- The printed stochastic-Fubini proof, from the original local
martingale: construct the M2-valued family and the mean-integrand integral,
then identify them by KW, covariance exchange, signed Fubini, and separation.
The Ito-operator integral-commutation theorem is not used. -/
theorem stochastic_fubini_printed_proof
    {Ω : Type} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (X : ClosedTime T → Ω → ℝ) (hX : LocalMProcessWitness P F X) :
    ∃ (c : ℕ → ℝ) (hc : ∀ n, 0 < c n) (A : ClosedTime T → Ω → ℝ)
      (hAm : ∀ n ω, MonotoneOn (fun r => A (realTimeClamp r) ω) (Icc 0 (c n)))
      (hAc : ∀ n ω, ContinuousOn (fun r => A (realTimeClamp r) ω) (Icc 0 (c n)))
      (ν : Measure (Ω × ℝ)),
      LocalCovarianceWitness P F X X A ∧ SigmaFinite ν ∧ StrictMono c ∧
      (∀ n, (c n:EReal) < T) ∧
      (∀ t, t < ⊤ → ∃ n, t < realTimeClamp (T := T) (c n)) ∧
      (∀ f : Ω × ℝ → ℝ≥0∞, Measurable f →
        (∫⁻ z, f z ∂ν) = ∫⁻ ω, ⨆ n, ∫⁻ r, f (ω,r)
          ∂(intervalStieltjes 0 (c n) (hc n).le (fun r => A (realTimeClamp r) ω) (hAm n ω)
            (fun r hr => (hAc n ω r hr).mono inter_subset_left)).measure ∂P) ∧
      ∃ L : progressiveEnergyRange F c ν →ₗᵢ[ℝ] continuousM2Terminal P F,
      ∀ (E : Type) [MeasurableSpace E] (μ : Measure E) [SigmaFinite μ]
        (H : E × (Ω × ℝ) → ℝ), Measurable H →
        (∀ n, @Measurable _ _
      ((inferInstance : MeasurableSpace E).prod (progressiveSpace (fun t : Icc (0:ℝ) (c n) => F (realTimeClamp t.val)))) inferInstance
      (fun z : E × (Ω × Icc (0:ℝ) (c n)) => H (z.1,(z.2.1,z.2.2.val)))) →
        (∫⁻ x, eLpNorm (fun z => H (x,z)) 2 ν ∂μ) < ∞ →
    (∀ᵐ z ∂ν, Integrable (fun x => H (x,z)) μ) ∧
    ∃ Z : E → continuousM2Terminal P F, Integrable Z μ ∧
      (∀ᵐ x ∂μ, ∃ Y : ClosedTime T → Ω → ℝ, ∃ hY : ContinuousM2Witness P F Y,
        ItoCovarianceFormula P F X (fun z => H (x,z)) Y ∧ Z x = m2TerminalOfProcess P F Y hY) ∧
      ∃ Ybar : ClosedTime T → Ω → ℝ, ∃ hYbar : ContinuousM2Witness P F Ybar,
        ItoCovarianceFormula P F X (fun z => ∫ x, H (x,z) ∂μ) Ybar ∧
        (∫ x, Z x ∂μ) = m2TerminalOfProcess P F Ybar hYbar := by
  obtain ⟨c,hc,hcm,hcT,hct,hcut,hcc⟩ := positive_real_time_exhaustion hT
  obtain ⟨A,hA,hm,hcont,h0,hAmr⟩ := quadratic_variation_measurable_encoding P hT F hF hle hnull X hX
  have hAm n := (regular_covariance_on_real_intervals A hm hcont (c n) (hc n).le (hcT n)).1
  have hAc n := (regular_covariance_on_real_intervals A hm hcont (c n) (hc n).le (hcT n)).2
  obtain ⟨ν,hν,henergy⟩ := global_stieltjes_energy_identity P c (fun n => (hc n).le) hcm.monotone
    (fun ω r => A (realTimeClamp r) ω) hAm hAc hAmr
  letI : SigmaFinite ν := hν
  obtain ⟨L,hIto⟩ := actual_ito_l2_isometry_constructed P hT F hF hle hnull X A hX hA
    c hc hcm hcT hct hcut hcc hAm hAc hAmr ν henergy
  refine ⟨c,hc,A,hAm,hAc,ν,hA,hν,hcm,hcT,hcc,henergy,L,?_⟩
  intro E mE μ hμ H hH hp hN
  have hpx x n : @Measurable _ _
      (progressiveSpace (fun t : Icc (0:ℝ) (c n) => F (realTimeClamp t.val))) inferInstance
      (fun z : Ω × Icc (0:ℝ) (c n) => H (x,(z.1,z.2.val))) :=
    (hp n).comp measurable_prodMk_left
  obtain ⟨U,hU,hUm,hUI,hLI,_⟩ := ito_parameter_family_integrable P F c μ ν L H hH hpx hN
  have hgood := (integrable_l2Section μ ν H hH hN).2.1
  let Hbar := fun z => ∫ x, H (x,z) ∂μ
  have hbarL : MemLp Hbar 2 ν := (mixed_l1_l2_fubini_minkowski μ ν H hH hN).2.2.1
  have hbarM : Measurable Hbar := hH.stronglyMeasurable.integral_prod_left'.measurable
  have hbarP n : @Measurable _ _
      (progressiveSpace (fun t : Icc (0:ℝ) (c n) => F (realTimeClamp t.val))) inferInstance
      (fun z : Ω × Icc (0:ℝ) (c n) => Hbar (z.1,z.2.val)) := by
    letI : MeasurableSpace (Ω × Icc (0:ℝ) (c n)) :=
      progressiveSpace (fun t : Icc (0:ℝ) (c n) => F (realTimeClamp t.val))
    exact (hp n).stronglyMeasurable.integral_prod_left'.measurable
  let G : progressiveEnergyIntegrands F c ν := ⟨Hbar,hbarM,hbarP,hbarL⟩
  obtain ⟨W,hW,hWI,_⟩ := hIto G
  let Z := fun x => L (U x)
  have hZI : ∀ᵐ x ∂μ, ∃ Y : ClosedTime T → Ω → ℝ, ∃ hY : ContinuousM2Witness P F Y,
      ItoCovarianceFormula P F X (fun z => H (x,z)) Y ∧ Z x = m2TerminalOfProcess P F Y hY := by
    filter_upwards [hgood] with x hx
    let Gx : progressiveEnergyIntegrands F c ν :=
      ⟨fun z => H (x,z),hH.comp measurable_prodMk_left,hpx x,hx.choose⟩
    have he : U x = ⟨progressiveEnergyToLp F c ν Gx,LinearMap.mem_range_self _ Gx⟩ := by
      apply Subtype.ext
      exact (hU x).trans hx.choose_spec
    obtain ⟨Y,hY,hchar,hterm⟩ := hIto Gx
    exact ⟨Y,hY,hchar,by dsimp only [Z]; rw [he]; exact hterm⟩
  have hZI' : ∀ᵐ x ∂μ, ItoCovarianceFormula P F X (fun z => H (x,z)) (m2ProcessOfTerminal P F (Z x)) := by
    filter_upwards [hZI] with x hx
    obtain ⟨Y,hY,hchar,hterm⟩ := hx
    have hZx := (m2_process_of_terminal_spec P F (Z x)).1
    have heT : Y ⊤ =ᵐ[P] m2ProcessOfTerminal P F (Z x) ⊤ := by
      have hz := (m2_process_of_terminal_spec P F (Z x)).2
      have heLp : (Z x : Lp ℝ 2 P) = (hY.moment ⊤).toLp (Y ⊤) := congrArg Subtype.val hterm
      rw [heLp] at hz
      exact (hY.moment ⊤).coeFn_toLp.symm.trans hz.symm
    have he := continuous_m2_terminal_injective P F hF hle Y _ hY hZx heT
    apply hchar.congr_integral P F hF hle X Y _ _
      (continuous_m2_is_local P F hF hle _ hct.monotone hcut hcc Y hY)
      (continuous_m2_is_local P F hF hle _ hct.monotone hcut hcc _ hZx)
    exact he.mono (fun ω hω t _ => hω t)
  have he := stochastic_fubini_by_covariance_separation μ P hT F hF hle hnull X A hX hA
    hm hcont hAmr c (fun n => (hc n).le) hcT hcc ν henergy H hH hN Z hLI hZI' W hW hWI
  refine ⟨mixed_l1_l2_pointwise_integrable μ ν H hH hN,Z,hLI,hZI,W,hW,hWI,?_⟩
  have heT : m2ProcessOfTerminal P F (∫ x, Z x ∂μ) ⊤ =ᵐ[P] W ⊤ :=
    he.mono (fun ω hω => hω ⊤)
  apply Subtype.ext
  apply Lp.ext
  exact (m2_process_of_terminal_spec P F (∫ x, Z x ∂μ)).2.symm.trans
    (heT.trans ((hW.moment ⊤).coeFn_toLp.symm))

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.stochastic_fubini_printed_proof
