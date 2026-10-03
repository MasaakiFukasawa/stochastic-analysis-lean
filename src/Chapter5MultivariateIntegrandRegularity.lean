import Chapter5TimeSpaceIntegrand

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter5
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete
set_option backward.isDefEq.respectTransparency false

theorem multivariate_integrand_regularity
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] {d : ℕ}
    (F : ClosedTime T → MeasurableSpace Ω)
    (X A M : Fin d → ClosedTime T → Ω → ℝ)
    (hX : ∀ i,SemimartingaleDecomposition P F (X i) (A i) (M i))
    (ψ : (Fin d → ℝ) → ℝ) (hψ : Continuous ψ) :
    let H := fun z : Ω × ℝ => ψ (fun i => X i (realTimeClamp z.2) z.1)
    (∀ w,Measurable (fun r => H (w,r))) ∧
    (∀ r : ℝ,0 ≤ r → (r:EReal) < T → Measurable[F (realTimeClamp r)] (fun w => H (w,r))) ∧
    (∀ b : ℝ,0 ≤ b → (b:EReal) < T → ∀ w,ContinuousOn (fun r => H (w,r)) (Icc 0 b)) := by
  dsimp only
  have ht (r : ℝ) (hr : 0 ≤ r) (hrT : (r:EReal) < T) : realTimeClamp (T := T) r < ⊤ := by
    change (realTimeClamp r : EReal) < T
    rw [real_time_clamp_eq r hr hrT.le]; exact hrT
  refine ⟨?_,?_,?_⟩
  · intro w
    exact hψ.measurable.comp (Measurable.of_eval fun i => open_path_real_measurable _ ((hX i).continuous w))
  · intro r hr hrT
    let : MeasurableSpace Ω := F (realTimeClamp r)
    apply hψ.measurable.comp
    apply Measurable.of_eval
    intro i
    have he : X i (realTimeClamp r) = fun w => A i (realTimeClamp r) w+M i (realTimeClamp r) w :=
      funext ((hX i).decomposition _ (ht r hr hrT))
    rw [he]
    exact ((hX i).variation.adapted _ (ht r hr hrT)).add ((hX i).martingale.adapted P F _ (ht r hr hrT))
  · intro b hb hbT w
    apply hψ.comp_continuousOn
    intro r hr
    apply ContinuousAt.continuousWithinAt
    apply continuousAt_pi.mpr
    intro i
    exact ((hX i).continuous w _ (ht r hr.1 ((EReal.coe_le_coe hr.2).trans_lt hbT))).comp
      real_time_clamp_continuous.continuousAt

end Asakura.Chapter5
