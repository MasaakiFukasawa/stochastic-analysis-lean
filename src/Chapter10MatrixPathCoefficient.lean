import Chapter10MatrixIntegralPath
import Chapter2VariationStoppedInterval
import Chapter2ItoIntegrandEncoding

open MeasureTheory Set
namespace Asakura.Chapter10
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

/-- Equality of deterministic coefficients at finite times identifies their
actual matrix-integral path witnesses. No value at infinity is constrained. -/
theorem MatrixIntegralPathWitness.congr_coefficient {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (F : HalfClosedTime → MeasurableSpace Ω)
    (c : ℕ → ℝ) (hc : ∀ k,0≤c k) (hcT : ∀ k,(c k:EReal)<⊤)
    {d r : ℕ} (T : ℝ) (hT : 0≤T)
    (Y : Ω → C(Icc (0:ℝ) T,Fin r → ℝ))
    (H K : Fin d → Fin r → HalfClosedTime → ℝ)
    (Z : Ω → C(Icc (0:ℝ) T,Fin d → ℝ))
    (h : MatrixIntegralPathWitness P F c hc T hT Y H Z)
    (he : ∀ i j t,t<⊤ → H i j t=K i j t) :
    MatrixIntegralPathWitness P F c hc T hT Y K Z := by
  obtain ⟨A,M,N,hY,hN,hZ⟩ := h.representation
  refine ⟨A,M,N,hY,?_,hZ⟩
  intro i j
  obtain ⟨V,U,hNU,hV,hU⟩ := hN i j
  refine ⟨V,U,hNU,?_,?_⟩
  · exact hV.congr_on_time_domain P c hc hcT (A j) V _ _
      (fun w t ht htT => he i j _ (real_time_below t ht htT))
  · exact hU.congr_on_time_domain P F (M j) U _ _
      (fun w t ht htT => he i j _ (real_time_below t ht htT))

end Asakura.Chapter10
