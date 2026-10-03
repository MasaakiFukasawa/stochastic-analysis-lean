import Chapter6ConditionalBoundLimit

open MeasureTheory Set Filter
open scoped Topology
namespace Asakura.Chapter6
set_option maxHeartbeats 2000000

theorem three_L1_limits_identity {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X Y Z : Ω → ℝ) (hX : Integrable X P) (hY : Integrable Y P) (hZ : Integrable Z P)
    (S T U : ℕ → Ω → ℝ) (hS : ∀ n,Integrable (S n) P) (hT : ∀ n,Integrable (T n) P) (hU : ∀ n,Integrable (U n) P)
    (he : ∀ n,S n=ᵐ[P] fun w => T n w+U n w)
    (hlX : Tendsto (fun n => ∫ w,‖X w-S n w‖ ∂P) atTop (𝓝 0))
    (hlY : Tendsto (fun n => ∫ w,‖Y w-T n w‖ ∂P) atTop (𝓝 0))
    (hlZ : Tendsto (fun n => ∫ w,‖Z w-U n w‖ ∂P) atTop (𝓝 0)) : X=ᵐ[P] fun w => Y w+Z w := by
  have hi : Integrable (fun w => X w-(Y w+Z w)) P := hX.sub (hY.add hZ)
  have hb n : (∫ w,‖X w-(Y w+Z w)‖ ∂P)≤
      (∫ w,‖X w-S n w‖ ∂P)+(∫ w,‖Y w-T n w‖ ∂P)+(∫ w,‖Z w-U n w‖ ∂P) := by
    have hpoint : ∀ᵐ w ∂P,‖X w-(Y w+Z w)‖≤‖X w-S n w‖+‖Y w-T n w‖+‖Z w-U n w‖ := by
      filter_upwards [he n] with w hw
      calc
        _ = ‖((X w-S n w)-(Y w-T n w))-(Z w-U n w)‖ := by rw [hw]; congr 1; ring
        _ ≤ _ := by
          have h1 := norm_sub_le ((X w-S n w)-(Y w-T n w)) (Z w-U n w)
          have h2 := norm_sub_le (X w-S n w) (Y w-T n w)
          linarith
    have hm := integral_mono_ae hi.norm ((((hX.sub (hS n)).norm).add ((hY.sub (hT n)).norm)).add ((hZ.sub (hU n)).norm)) hpoint
    have hi1 : Integrable (fun w => ‖X w-S n w‖) P := (hX.sub (hS n)).norm
    have hi2 : Integrable (fun w => ‖Y w-T n w‖) P := (hY.sub (hT n)).norm
    have hi3 : Integrable (fun w => ‖Z w-U n w‖) P := (hZ.sub (hU n)).norm
    change (∫ w,‖X w-(Y w+Z w)‖ ∂P)≤∫ w,(‖X w-S n w‖+‖Y w-T n w‖)+‖Z w-U n w‖ ∂P at hm
    have hi12 : Integrable (fun w => ‖X w-S n w‖+‖Y w-T n w‖) P := hi1.add hi2
    rw [integral_add hi12 hi3,integral_add hi1 hi2] at hm
    exact hm
  have hz : (∫ w,‖X w-(Y w+Z w)‖ ∂P)=0 := le_antisymm
    (ge_of_tendsto (by simpa only [add_zero] using (hlX.add hlY).add hlZ) (Eventually.of_forall hb))
    (integral_nonneg (fun _ => norm_nonneg _))
  have hae := (integral_eq_zero_iff_of_nonneg (fun _ => norm_nonneg _) hi.norm).mp hz
  exact hae.mono (fun w hw => sub_eq_zero.mp (norm_eq_zero.mp hw))

end Asakura.Chapter6
