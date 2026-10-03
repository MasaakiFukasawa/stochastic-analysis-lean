import Chapter12NormalizedBrownianTerminalLaw
import Chapter12FiniteWienerInformation

open MeasureTheory ProbabilityTheory Set
namespace Asakura.Chapter12
open Asakura.FullAudit Asakura.Chapter2Complete Asakura.Chapter4
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

theorem actual_brownian_normalized_terminal_law {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ}
    (B : BrownianSystem P (d+1)) (T : ℝ) (hT : 0<T) :
    HasLaw (fun w i => B.W i (realTimeClamp T) w/Real.sqrt T)
      (Measure.pi (fun _ : Fin (d+1) => gaussianReal 0 1)) P := by
  obtain ⟨W,hW,hm,hinc⟩ := finite_horizon_wiener_information P B T hT.le
  have hh := normalized_brownian_terminal_law P d T hT W hW
  have hzero : realTimeClamp (T := (⊤:EReal)) 0 = ⊥ :=
    Subtype.ext (real_time_clamp_eq 0 le_rfl le_top)
  have he (i : Fin (d+1)) : (fun w => B.W i (realTimeClamp T) w/Real.sqrt T) =ᵐ[P]
      (fun w => W (brownianTimeDirection (i,⟨T,hT.le,le_rfl⟩)) w/Real.sqrt T) := by
    have hi := hinc i 0 T le_rfl hT.le le_rfl
    rw [hzero] at hi
    filter_upwards [hi,(B.martingale i).initial P B.F] with w hw hz
    dsimp only [brownianTimeDirection]
    rw [hw,hz]
    simp only [Pi.zero_apply,sub_zero]
  apply hh.congr
  filter_upwards [ae_all_iff.mpr he] with w hw
  funext i
  exact hw i

end Asakura.Chapter12
