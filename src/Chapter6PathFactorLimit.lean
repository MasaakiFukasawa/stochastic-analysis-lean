import Chapter6ConditionalBoundLimit
import FullAuditFactorizationExercise

open MeasureTheory Set Filter
open scoped Topology
namespace Asakura.Chapter6
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

/-- A limit in L1 of measurable path functionals is itself a path
functional up to the identification of almost everywhere equal functions. -/
theorem path_factor_of_L1_limit {Ω E : Type*} {m : MeasurableSpace Ω} [MeasurableSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → E) (hX : Measurable X)
    (S : ℕ → Ω → ℝ) (Z : Ω → ℝ)
    (hSm : ∀ n,Measurable[MeasurableSpace.comap X inferInstance] (S n))
    (hSi : ∀ n,Integrable (S n) P) (hZi : Integrable Z P)
    (hl : Tendsto (fun n => ∫ w,‖Z w-S n w‖ ∂P) atTop (𝓝 0)) :
    ∃ a : E → ℝ,Measurable a ∧ Z=ᵐ[P] a ∘ X := by
  let G := MeasurableSpace.comap X inferInstance
  letI : MeasurableSpace Ω := m
  have hG : G≤m := hX.comap_le
  have hi : Integrable (fun w => Z w-P[Z|G] w) P := hZi.sub integrable_condExp
  have hb n : (∫ w,‖Z w-P[Z|G] w‖ ∂P)≤2*∫ w,‖Z w-S n w‖ ∂P := by
    have hc := condExp_sub hZi (hSi n) G
    have hs : P[S n|G]=S n := condExp_of_stronglyMeasurable hG (hSm n).stronglyMeasurable (hSi n)
    have hp : ∀ᵐ w ∂P,‖Z w-P[Z|G] w‖≤‖Z w-S n w‖+‖P[(fun w => Z w-S n w)|G] w‖ := by
      filter_upwards [hc] with w hc
      change P[(fun w => Z w-S n w)|G] w=P[Z|G] w-P[S n|G] w at hc
      rw [hs] at hc
      rw [hc]
      calc
        _ = ‖(Z w-S n w)-(P[Z|G] w-S n w)‖ := by congr 1; ring
        _ ≤ _ := norm_sub_le _ _
    have hh := integral_mono_ae hi.norm (((hZi.sub (hSi n)).norm).add integrable_condExp.norm) hp
    simp only [Pi.add_apply] at hh
    rw [integral_add ((hZi.sub (hSi n)).norm) integrable_condExp.norm] at hh
    have hc := integral_norm_condExp_le (μ := P) (m := G) (fun w => Z w-S n w)
    simp only [Pi.sub_apply] at hh
    linarith
  have he : (∫ w,‖Z w-P[Z|G] w‖ ∂P)=0 := le_antisymm
    (ge_of_tendsto (by simpa using hl.const_mul 2) (Eventually.of_forall hb))
    (integral_nonneg (fun _ => norm_nonneg _))
  have hae := (integral_eq_zero_iff_of_nonneg (fun _ => norm_nonneg _) hi.norm).mp he
  obtain ⟨a,ha,he⟩ := Asakura.FullAudit.measurable_factorization_written X (P[Z|G]) stronglyMeasurable_condExp.measurable
  refine ⟨a,ha,?_⟩
  filter_upwards [hae] with w hw
  have hh := sub_eq_zero.mp (norm_eq_zero.mp hw)
  exact hh.trans (congrFun he w)

end Asakura.Chapter6
