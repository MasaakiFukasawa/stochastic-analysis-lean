import Chapter4SDEEndpointMoment
import Chapter8SDERandomLinearCoordinates

open MeasureTheory Set
namespace Asakura.EndToEnd
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter8
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false

/-- Construct a measurable square-integrable compact path in any linear
coordinates of a Lipschitz SDE. The equality is pointwise, so all times and
parameters may use the same coordinate map. -/
theorem sde_coordinate_path {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (P : Measure Ω) [IsProbabilityMeasure P] {d n : ℕ} (B : BrownianSystem P n)
    (L : ℝ) (hL : 0≤L)
    (b : Fin d → (Fin d → ℝ) → ℝ) (σ : Fin d → Fin n → (Fin d → ℝ) → ℝ)
    (hLip : ∀ x y,(∑i,(b i x-b i y)^2)+(∑i,∑j,(σ i j x-σ i j y)^2)≤L*∑i,(x i-y i)^2)
    (ξ : Ω → Fin d → ℝ) (hξ : MemLp ξ 2 P)
    (X : HalfClosedTime → Ω → Fin d → ℝ) (hX : VectorSDESolution P B.F B.W b σ ξ X)
    (A : (Fin d → ℝ) →L[ℝ] E) (T : ℝ) (hT : 0≤T) :
    ∃ Q : Ω → C(Icc (0:ℝ) T,E),Measurable Q ∧ MemLp Q 2 P ∧
      ∀ w (t : Icc (0:ℝ) T),Q w t=A (X (realTimeClamp t.val) w) := by
  obtain ⟨hm,h2,_⟩ := sde_finite_path_memLp P (EReal.coe_lt_top 0) rfl B.F B.mono B.le B.null
    B.W (fun j => B.C j j) B.martingale (fun j => B.cov j j)
    (fun j w r hr _ => B.diagonal_clock j w r hr) L hL b σ hLip ξ hξ X hX T hT (EReal.coe_lt_top T)
  let C := A.compLeftContinuous ℝ (Icc (0:ℝ) T)
  exact ⟨fun w => C (Vector.realVectorPath X hX.path T (EReal.coe_lt_top T) w),
    C.continuous.measurable.comp hm,C.comp_memLp' h2,fun _ _ => rfl⟩

#print axioms sde_coordinate_path
end Asakura.EndToEnd
