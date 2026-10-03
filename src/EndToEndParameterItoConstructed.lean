import EndToEndLocalItoRepresentative
import Chapter5LocalPathBrownianIntegral

open MeasureTheory Set Filter
namespace Asakura.EndToEnd
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter4 Asakura.Chapter5 Asakura.Chapter13
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

/-- Construct the actual parameterized Brownian integral from its coefficients,
including joint measurability and continuous local-martingale representatives. -/
theorem parameter_ito_constructed {Ω E : Type} {m : MeasurableSpace Ω} [MeasurableSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (B : BrownianSystem P d) (i : Fin d)
    (μ : Measure E) [IsFiniteMeasure μ]
    (H : E × (Ω × ℝ) → ℝ) (hm : Measurable H)
    (hp : ∀ b,0<b → @Measurable _ _
      ((inferInstance : MeasurableSpace E).prod (progressiveSpace (fun t : Icc (0:ℝ) b => B.F (realTimeClamp t.val)))) inferInstance
      (fun z : E × (Ω × Icc (0:ℝ) b) => H (z.1,(z.2.1,z.2.2.val))))
    (hb : ∀ w b,0≤b → ∃ K : ℝ,0≤K ∧ ∀ x r,r∈Icc 0 b → |H (x,(w,r))|≤K) :
    ∃ V : E → HalfClosedTime → Ω → ℝ,
      Measurable (fun z : E × (Ω × HalfClosedTime) => V z.1 z.2.2 z.2.1) ∧
      (∀ x,LocalMProcessWitness P B.F (V x)) ∧
      ∀ᵐ x ∂μ, ItoCovarianceFormula P B.F (B.W i) (fun z => H (x,z)) (V x) := by
  have hT : (0:EReal)<⊤ := by simp
  obtain ⟨c,hc,hcm,hcT,hct,hcut,hcc⟩ := positive_real_time_exhaustion hT
  have hex x : ∃ N, LocalMProcessWitness P B.F N ∧
      ItoCovarianceFormula P B.F (B.W i) (fun z => H (x,z)) N := by
    apply brownian_local_path_energy_integral_constructed P hT B.F B.mono B.le B.null
      (B.W i) (B.C i i) (B.martingale i) (B.cov i i) c hc hcm hcT hct hcut hcc
    · exact fun n w r hr => B.diagonal_clock i w r hr.1
    · exact hm.comp measurable_prodMk_left
    · exact fun n => (hp (c n) (hc n)).comp measurable_prodMk_left
    · intro n
      apply ae_of_all
      intro w
      exact bounded_coefficient_square (fun z => H (x,z)) (hm.comp measurable_prodMk_left)
        (fun w b hb0 => by
          obtain ⟨K,hK,hbound⟩ := hb w b hb0
          exact ⟨K,hK,fun s hs => hbound x s hs⟩) w (c n) (hc n).le
  choose N hN hNI using hex
  obtain ⟨V,hVm,hVa,hVI⟩ := local_ito_joint_representative P B i μ H hm hp hb N hN hNI
  exact ⟨V,hVm,hVa,hVI.mono (fun _ hx => hx.1)⟩

#print axioms parameter_ito_constructed
end Asakura.EndToEnd
