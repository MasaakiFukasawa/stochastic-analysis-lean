import Chapter2M2TerminalRealization

open MeasureTheory Set
open scoped ENNReal
namespace Asakura.Chapter2Complete
open Asakura.FullAudit Asakura.Chapter2Written
set_option maxHeartbeats 1300000
set_option backward.isDefEq.respectTransparency false

noncomputable def m2ProcessOfTerminal
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    (v : continuousM2Terminal P F) : ClosedTime T → Ω → ℝ :=
  Classical.choose v.property

theorem m2_process_of_terminal_spec
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    (v : continuousM2Terminal P F) :
    ContinuousM2Witness P F (m2ProcessOfTerminal P F v) ∧
      m2ProcessOfTerminal P F v ⊤ =ᵐ[P] (v : Lp ℝ 2 P) :=
  Classical.choose_spec v.property

theorem m2_process_terminal_value
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    (v : continuousM2Terminal P F) :
    m2TerminalOfProcess P F (m2ProcessOfTerminal P F v) (m2_process_of_terminal_spec P F v).1 = v := by
  apply Subtype.ext
  apply Lp.ext
  exact ((m2_process_of_terminal_spec P F v).1.moment ⊤).coeFn_toLp.trans (m2_process_of_terminal_spec P F v).2

theorem m2_process_representation_linear
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (v w : continuousM2Terminal P F) (a : ℝ) :
    ∀ᵐ ω ∂P, ∀ t, m2ProcessOfTerminal P F (a • v+w) t ω =
      a*m2ProcessOfTerminal P F v t ω + m2ProcessOfTerminal P F w t ω := by
  let X := m2ProcessOfTerminal P F v
  let Y := m2ProcessOfTerminal P F w
  let Z := m2ProcessOfTerminal P F (a • v+w)
  have hX := (m2_process_of_terminal_spec P F v).1
  have hY := (m2_process_of_terminal_spec P F w).1
  have hZ := (m2_process_of_terminal_spec P F (a • v+w)).1
  apply continuous_m2_terminal_injective P F hF hle Z (fun t ω => a*X t ω+Y t ω) hZ
    ((hX.smul P F a).add P F hY)
  have hx := (m2_process_of_terminal_spec P F v).2
  have hy := (m2_process_of_terminal_spec P F w).2
  have hz := (m2_process_of_terminal_spec P F (a • v+w)).2
  have hs := Lp.coeFn_smul a (v : Lp ℝ 2 P)
  have ha := Lp.coeFn_add (a • (v : Lp ℝ 2 P)) (w : Lp ℝ 2 P)
  filter_upwards [hx,hy,hz,hs,ha] with ω hxω hyω hzω hsω haω
  change Z ⊤ ω = a*X ⊤ ω+Y ⊤ ω
  change Z ⊤ ω = (a • (v : Lp ℝ 2 P)+(w : Lp ℝ 2 P)) ω at hzω
  rw [hzω,haω]
  simp only [Pi.add_apply]
  rw [hsω]
  change a*(v : Lp ℝ 2 P) ω+(w : Lp ℝ 2 P) ω = a*X ⊤ ω+Y ⊤ ω
  change X ⊤ ω = (v : Lp ℝ 2 P) ω at hxω
  change Y ⊤ ω = (w : Lp ℝ 2 P) ω at hyω
  rw [hxω,hyω]

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.m2_process_representation_linear
