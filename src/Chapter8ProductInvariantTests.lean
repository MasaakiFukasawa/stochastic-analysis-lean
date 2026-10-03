import Chapter8ProductSDEIdentification
import Chapter8IndependentInitialSDE

open MeasureTheory Set
open scoped BigOperators NNReal
namespace Asakura.Chapter8
open Asakura.Chapter4 Asakura.Chapter3Complete Asakura.FullAudit
open Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

/-- Invariant transition tests transfer to the product-space construction
because the actual deterministic-start solutions coincide there. -/
theorem product_invariant_tests {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
    (P : Measure Ω) [IsProbabilityMeasure P] (ν : Measure A) [IsProbabilityMeasure ν]
    {d n : ℕ} (B : BrownianSystem P n) (B' : BrownianSystem (ν.prod P) n)
    (hW : ∀ j t z,B'.W j t z=B.W j t z.2)
    (b : (Fin d → ℝ) → Fin d → ℝ) (K : ℝ≥0) (hb : LipschitzWith K b)
    (σ : Fin d → Fin n → ℝ)
    (Z : (Fin d → ℝ) → HalfClosedTime → Ω → Fin d → ℝ)
    (Z' : (Fin d → ℝ) → HalfClosedTime → A × Ω → Fin d → ℝ)
    (hZ : ∀ x,VectorSDESolution P B.F B.W (fun i y => b y i) (fun i j _ => σ i j) (fun _ => x) (Z x))
    (hZ' : ∀ x,VectorSDESolution (ν.prod P) B'.F B'.W (fun i y => b y i) (fun i j _ => σ i j) (fun _ => x) (Z' x))
    (π : Measure (Fin d → ℝ))
    (hinv : ∀ t : ℝ,0≤t → ∀ f : (Fin d → ℝ) → ℝ,ContDiff ℝ (⊤:ℕ∞) f → HasCompactSupport f →
      (∫ x,(∫ w,f (Z x (realTimeClamp t) w) ∂P) ∂π)=∫ x,f x ∂π) :
    ∀ t : ℝ,0≤t → ∀ f : (Fin d → ℝ) → ℝ,ContDiff ℝ (⊤:ℕ∞) f → HasCompactSupport f →
      (∫ x,(∫ w,f (Z' x (realTimeClamp t) w) ∂ν.prod P) ∂π)=∫ x,f x ∂π := by
  intro t ht f hf hs
  have he x : (∫ w,f (Z' x (realTimeClamp t) w) ∂ν.prod P)=∫ w,f (Z x (realTimeClamp t) w) ∂P := by
    have hid := product_sde_identification P ν B B' hW b K hb σ x (Z x) (Z' x) (hZ x) (hZ' x)
    rw [integral_congr_ae (hid.mono (fun w hw => congrArg f (hw t ht)))]
    have hm : Measurable (fun w => f (Z x (realTimeClamp t) w)) :=
      hf.continuous.measurable.comp (((hZ x).adapted _ (half_real_time_finite t)).mono (B.le _) le_rfl)
    have hh := integral_map (μ := ν.prod P) measurable_snd.aemeasurable hm.aestronglyMeasurable
    rw [Measure.map_snd_prod,measure_univ,one_smul] at hh
    exact hh.symm
  simp_rw [he]
  exact hinv t ht f hf hs
end Asakura.Chapter8
