import Chapter2StochasticIntervalIntegrand
import FullAuditBoundedKW

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

/-- The stochastic-interval indicator is progressive on each real-time
prefix used in the construction of the actual integral. -/
theorem real_stochastic_interval_progressive
    {Ω : Type*} {T : EReal} [Fact (0 ≤ T)]
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F)
    (σ τ : Ω → ℝ) (hσ0 : ∀ ω, 0 ≤ σ ω) (hτ0 : ∀ ω, 0 ≤ τ ω)
    (hσT : ∀ ω, (σ ω:EReal) < T) (hτT : ∀ ω, (τ ω:EReal) < T)
    (hσ : ∀ t, MeasurableSet[F t] {ω | realTimeClamp (T := T) (σ ω) ≤ t})
    (hτ : ∀ t, MeasurableSet[F t] {ω | realTimeClamp (T := T) (τ ω) ≤ t})
    (b : ℝ) (hb : 0 ≤ b) (hbT : (b:EReal) < T) :
    @MeasurableSet (Ω × Icc (0:ℝ) b)
      (progressiveSpace (fun t : Icc (0:ℝ) b => F (realTimeClamp (T := T) t.val)))
      {z | σ z.1 < z.2.val ∧ z.2.val ≤ τ z.1} := by
  have hg := stochastic_interval_progressive F hF
    (fun ω => realTimeClamp (T := T) (σ ω)) (fun ω => realTimeClamp (T := T) (τ ω)) hσ hτ
  apply MeasurableSpace.measurableSet_iInf.mpr
  intro t
  letI : MeasurableSpace Ω := F (realTimeClamp (T := T) t.val)
  let q : Iic t → Iic (realTimeClamp (T := T) t.val) := fun s =>
    ⟨realTimeClamp (T := T) s.val.val,real_time_clamp_mono s.property⟩
  have hq : Measurable q :=
    ((real_time_clamp_continuous.measurable.comp measurable_subtype_coe).comp measurable_subtype_coe).subtype_mk
  have hs := MeasurableSpace.measurableSet_iInf.mp hg (realTimeClamp (T := T) t.val)
  have hmap : Measurable (fun z : Ω × Iic t => (z.1,q z.2)) :=
    measurable_fst.prodMk (hq.comp measurable_snd)
  have hm := hmap hs
  change MeasurableSet {z : Ω × Iic t | σ z.1 < z.2.val.val ∧ z.2.val.val ≤ τ z.1}
  have he : {z : Ω × Iic t | σ z.1 < z.2.val.val ∧ z.2.val.val ≤ τ z.1} =
      {z : Ω × Iic t | realTimeClamp (T := T) (σ z.1) < realTimeClamp (T := T) z.2.val.val ∧
        realTimeClamp (T := T) z.2.val.val ≤ realTimeClamp (T := T) (τ z.1)} := by
    ext z
    change (σ z.1 < z.2.val.val ∧ z.2.val.val ≤ τ z.1) ↔
      (realTimeClamp (T := T) (σ z.1):EReal) < (realTimeClamp (T := T) z.2.val.val:EReal) ∧
      (realTimeClamp (T := T) z.2.val.val:EReal) ≤ (realTimeClamp (T := T) (τ z.1):EReal)
    rw [real_time_clamp_eq _ (hσ0 _) (hσT _).le,
      real_time_clamp_eq _ (hτ0 _) (hτT _).le,
      real_time_clamp_eq _ z.2.val.property.1 ((EReal.coe_le_coe z.2.val.property.2).trans hbT.le)]
    exact_mod_cast Iff.rfl
  rw [he]
  exact hm

theorem real_stochastic_interval_integrand_progressive
    {Ω : Type*} {T : EReal} [Fact (0 ≤ T)]
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F)
    (σ τ : Ω → ℝ) (hσ0 : ∀ ω, 0 ≤ σ ω) (hτ0 : ∀ ω, 0 ≤ τ ω)
    (hσT : ∀ ω, (σ ω:EReal) < T) (hτT : ∀ ω, (τ ω:EReal) < T)
    (hσ : ∀ t, MeasurableSet[F t] {ω | realTimeClamp (T := T) (σ ω) ≤ t})
    (hτ : ∀ t, MeasurableSet[F t] {ω | realTimeClamp (T := T) (τ ω) ≤ t})
    (b : ℝ) (hb : 0 ≤ b) (hbT : (b:EReal) < T)
    (H : Ω × ℝ → ℝ)
    (hH : @Measurable _ _ (progressiveSpace (fun t : Icc (0:ℝ) b => F (realTimeClamp (T := T) t.val))) inferInstance
      (fun z : Ω × Icc (0:ℝ) b => H (z.1,z.2.val))) :
    @Measurable _ _ (progressiveSpace (fun t : Icc (0:ℝ) b => F (realTimeClamp (T := T) t.val))) inferInstance
      (fun z : Ω × Icc (0:ℝ) b => (Ioc (σ z.1) (τ z.1)).indicator (fun r => H (z.1,r)) z.2.val) := by
  convert hH.indicator (real_stochastic_interval_progressive F hF σ τ hσ0 hτ0 hσT hτT hσ hτ b hb hbT) using 1
  funext z
  simp only [indicator_apply,mem_setOf_eq,mem_Ioc]

/-- Restricting to a stochastic interval preserves the pathwise square
integrability required to construct the new Ito integral. -/
theorem square_integrable_interval_indicator (μ : Measure ℝ) (f : ℝ → ℝ)
    (hf : Integrable (fun r => f r^2) μ) (a b : ℝ) :
    Integrable (fun r => ((Ioc a b).indicator f r)^2) μ := by
  have he : (fun r => ((Ioc a b).indicator f r)^2) = (Ioc a b).indicator (fun r => f r^2) := by
    funext r
    by_cases hr : r ∈ Ioc a b <;> simp [hr]
  rw [he]
  exact hf.indicator measurableSet_Ioc

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.real_stochastic_interval_integrand_progressive
#print axioms Asakura.Chapter2Complete.square_integrable_interval_indicator
