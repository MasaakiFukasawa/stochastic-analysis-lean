import FullAuditMartingaleHilbert

open MeasureTheory Set
open scoped ENNReal
namespace Asakura.Chapter2Complete
open Asakura.FullAudit Asakura.Chapter2Written
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false

noncomputable def m2TerminalOfProcess
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    (X : ClosedTime T → Ω → ℝ) (hX : ContinuousM2Witness P F X) : continuousM2Terminal P F :=
  ⟨(hX.moment ⊤).toLp (X ⊤),X,hX,(hX.moment ⊤).coeFn_toLp.symm⟩

theorem m2_terminal_realization_linear
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    (X Y Z : ClosedTime T → Ω → ℝ)
    (hX : ContinuousM2Witness P F X) (hY : ContinuousM2Witness P F Y)
    (hZ : ContinuousM2Witness P F Z) (a : ℝ)
    (he : Z ⊤ =ᵐ[P] fun ω => a*X ⊤ ω+Y ⊤ ω) :
    m2TerminalOfProcess P F Z hZ = a • m2TerminalOfProcess P F X hX + m2TerminalOfProcess P F Y hY := by
  apply Subtype.ext
  apply Lp.ext
  have hx := (hX.moment ⊤).coeFn_toLp
  have hy := (hY.moment ⊤).coeFn_toLp
  have hz := (hZ.moment ⊤).coeFn_toLp
  have hs := Lp.coeFn_smul a ((hX.moment ⊤).toLp (X ⊤))
  have ha := Lp.coeFn_add (a • (hX.moment ⊤).toLp (X ⊤)) ((hY.moment ⊤).toLp (Y ⊤))
  filter_upwards [hx,hy,hz,hs,ha,he] with ω hxω hyω hzω hsω haω heω
  change ((hZ.moment ⊤).toLp (Z ⊤)) ω =
    (a • (hX.moment ⊤).toLp (X ⊤) + (hY.moment ⊤).toLp (Y ⊤)) ω
  rw [hzω,haω]
  simp only [Pi.add_apply]
  rw [hsω]
  change Z ⊤ ω = a*((hX.moment ⊤).toLp (X ⊤)) ω+((hY.moment ⊤).toLp (Y ⊤)) ω
  rw [hxω,hyω]
  exact heω

theorem real_l2_norm_sq_integral
    {S : Type*} [MeasurableSpace S] (ν : Measure S) (H : S → ℝ) (hH : MemLp H 2 ν) :
    ‖hH.toLp H‖^2 = ∫ z, H z^2 ∂ν := by
  rw [← real_inner_self_eq_norm_sq,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hH.coeFn_toLp] with z hz
  rw [Real.inner_apply,hz]
  ring

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.m2_terminal_realization_linear
#print axioms Asakura.Chapter2Complete.real_l2_norm_sq_integral
