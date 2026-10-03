import Chapter2ItoM2Uniqueness
import Chapter2ProgressiveEnergySpace
import Chapter2M2TerminalRealization
import Chapter2LinearNormFactor

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

/-- Assemble the pointwise existence construction into an isometric operator
on actual L2 equivalence classes. Linearity and representative independence
are proved from covariance uniqueness and the isometry, not assumed for the
chosen existence witnesses. -/
theorem ito_operator_from_characterized_existence
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (X : ClosedTime T → Ω → ℝ) (hX : LocalMProcessWitness P F X)
    (c : ℕ → ℝ) (ν : Measure (Ω × ℝ))
    (hex : ∀ H : progressiveEnergyIntegrands F c ν,
      ∃ Y : ClosedTime T → Ω → ℝ, ∃ hY : ContinuousM2Witness P F Y,
        ItoCovarianceFormula P F X H.val Y ∧
        ‖(hY.moment ⊤).toLp (Y ⊤)‖^2 = ‖progressiveEnergyToLp F c ν H‖^2) :
    ∃ L : progressiveEnergyRange F c ν →ₗᵢ[ℝ] continuousM2Terminal P F,
      ∀ H : progressiveEnergyIntegrands F c ν,
        ∃ Y : ClosedTime T → Ω → ℝ, ∃ hY : ContinuousM2Witness P F Y,
          ItoCovarianceFormula P F X H.val Y ∧
          L ⟨progressiveEnergyToLp F c ν H,LinearMap.mem_range_self _ H⟩ = m2TerminalOfProcess P F Y hY := by
  classical
  choose Y hY hchar hnorm using hex
  let J := fun H => m2TerminalOfProcess P F (Y H) (hY H)
  have hn H : ‖J H‖^2 = ‖progressiveEnergyToLp F c ν H‖^2 := hnorm H
  have hlin (a : ℝ) (H G : progressiveEnergyIntegrands F c ν) :
      J (a • H+G) = a • J H+J G := by
    apply m2_terminal_realization_linear P F (Y H) (Y G) (Y (a • H+G)) (hY H) (hY G) (hY (a • H+G)) a
    have hw : ItoCovarianceFormula P F X (fun z => a*H.val z+G.val z) (Y (a • H+G)) := hchar (a • H+G)
    have he := ito_m2_covariance_linearity P hT F hF hle hnull X (Y H) (Y G) (Y (a • H+G))
      H.val G.val a hX (hY H) (hY G) (hY (a • H+G)) (hchar H) (hchar G) hw
    exact he.mono (fun ω hω => hω ⊤)
  have hzero : J 0 = 0 := by
    apply norm_eq_zero.mp
    have hz := hn 0
    rw [map_zero,norm_zero,zero_pow (by norm_num : (2:ℕ) ≠ 0)] at hz
    nlinarith [norm_nonneg (J 0)]
  let JL : progressiveEnergyIntegrands F c ν →ₗ[ℝ] continuousM2Terminal P F :=
    { toFun := J
      map_add' := fun H G => by simpa only [one_smul] using hlin 1 H G
      map_smul' := fun a H => by
        change J (a • H) = a • J H
        simpa only [add_zero,hzero] using hlin a H 0 }
  have hnorm' H : ‖JL H‖ = ‖progressiveEnergyToLp F c ν H‖ := by
    have h := hn H
    change ‖JL H‖^2 = ‖progressiveEnergyToLp F c ν H‖^2 at h
    nlinarith [norm_nonneg (JL H),norm_nonneg (progressiveEnergyToLp F c ν H)]
  obtain ⟨L,hL⟩ := linear_isometry_factor_through_range (progressiveEnergyToLp F c ν) JL hnorm'
  exact ⟨L,fun H => ⟨Y H,hY H,hchar H,hL H⟩⟩

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.ito_operator_from_characterized_existence
