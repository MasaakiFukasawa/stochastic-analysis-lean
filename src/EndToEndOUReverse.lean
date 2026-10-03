import Chapter9OURandomInitial
import Chapter9OUReverseLocalTest
import Chapter9BrownianBefore
import Chapter9ReverseLogEquation

open MeasureTheory Matrix Set
namespace Asakura.EndToEnd
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter4 Asakura.Chapter9
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

/-- Construct the forward solution and the reverse Brownian motion from the
original Brownian system and measurable initial value. The reverse regression
identity is derived, not an input. -/
theorem ou_reverse_constructed {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (B : BrownianSystem P d)
    (ξ : Ω → Fin d → ℝ) (hξ : Measurable[B.F ⊥] ξ) (T : ℝ) :
    ∃ X : ℝ → Ω → Fin d → ℝ,
      (∀ r,Measurable (X r)) ∧ (∀ w,Continuous (fun r => X r w)) ∧
      (∀ᵐ w ∂P,∀ t≥0,∀ i,X t w i=ξ w i-(∫s in 0..t,X s w i)+Real.sqrt 2*B.W i (realTimeClamp t) w) ∧
      BrownianBefore P (reversedNaturalInformation P X T)
        (reverseBrownian (P.map (X 0)) X T) T ∧
      ∀ s,0≤s → s<T → ∀ w i,
        let a := fun r => X (T-r) w i+2*directional
          (fun y => Real.log (ouCoordinateDensity (P.map (X 0)) (T-r,y)))
          (Pi.single i 1) (X (T-r) w)
        IntervalIntegrable a volume 0 s ∧
          X (T-s) w i=X T w i+(∫r in 0..s,a r)+
            Real.sqrt 2*reverseBrownian (P.map (X 0)) X T s w i := by
  obtain ⟨N,hN,hNI,hsol⟩ := standard_ou_common_initial_construction P B
  let X := fun r w i => Real.exp (-r)*(ξ w i+∑ j,N i j (realTimeClamp r) w)
  have hXm r : Measurable (X r) := (standard_ou_adapted P B N hN ξ hξ r).mono (B.le _) le_rfl
  have hXc := standard_ou_path P B N hN ξ
  haveI : IsProbabilityMeasure (P.map (X 0)) :=
    (Measure.isProbabilityMeasure_map_iff (hXm 0).aemeasurable).mpr inferInstance
  refine ⟨X,hXm,hXc,?_,?_,?_⟩
  · filter_upwards [hsol] with w hw
    exact hw (ξ w)
  · apply reverse_brownian_is_brownian P (P.map (X 0)) X hXm hXc T
    intro a c ha hac hcT g hg
    have he := standard_ou_reverse_kernel_conditional P B N hN hNI ξ hξ
      (T-c) (T-a) T (by linarith) (by linarith) (by linarith) g hg
    have hh : T-a-(T-c)=c-a := by ring
    simpa only [reversedNaturalInformation,ouReverseParamTransition,ouCoordinateDensity,hh,X] using! he
  · exact fun s hs hsT w i => reverse_brownian_log_sde (P.map (X 0)) X hXc T s hs hsT w i

#print axioms ou_reverse_constructed
end Asakura.EndToEnd
