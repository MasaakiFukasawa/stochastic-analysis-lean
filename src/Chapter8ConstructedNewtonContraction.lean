import Chapter8ConstructedNewtonFlow
import Chapter8SymmetricNormBound

open MeasureTheory Set
open scoped NNReal
namespace Asakura.Chapter8
open Asakura.FullAudit
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
local instance : MeasurableSpace (WithLp 2 (E × E)) := borel _
local instance : BorelSpace (WithLp 2 (E × E)) := ⟨rfl⟩

/-- Construct the Newton flow from the force derivative bounds and prove the
quadratic-norm transport contraction. No measurable flow or pathwise estimate
is assumed in this theorem. -/
theorem constructed_newton_contraction {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (l u δ : ℝ) (hl : 0<l) (hlu : l≤u)
    (hδ : Real.sqrt u-Real.sqrt l<δ)
    (g : E → E) (H : E → E →L[ℝ] E)
    (hd : ∀ x,HasFDerivAt g (H x) x) (hH : Continuous H)
    (hs : ∀ x,(H x).toLinearMap.IsSymmetric)
    (hb : ∀ x z,l*‖z‖^2≤ inner ℝ z (H x z) ∧ inner ℝ z (H x z)≤u*‖z‖^2)
    (T : ℝ) (hT : 0≤T) (W : ℝ → Ω → E)
    (hWm : ∀ t,Measurable (W t)) (hWc : ∀ w,Continuous (fun t => W t w))
    (hW0 : ∀ w,W 0 w=0) :
    ∃ X : ℝ → (E × E) → Ω → (E × E),
      (∀ t,Measurable (Function.uncurry (X t))) ∧
      (∀ x w,Continuous (fun t => X t x w)) ∧ (∀ x w,X 0 x w=x) ∧
      (∀ x w t,t∈Icc 0 T → (X t x w).1=x.1+∫ s in 0..t,(X s x w).2) ∧
      (∀ x w t,t∈Icc 0 T → (X t x w).2=x.2+
        (∫ s in 0..t,-g (X s x w).1-δ • (X s x w).2)+W t w) ∧
      ∃ b r : ℝ,0<r ∧ ∃ hp : 0<b+δ^2/4,
        ∀ t,t∈Icc 0 T → ∀ (μ ν : Measure (E × E)),
          IsProbabilityMeasure μ → IsProbabilityMeasure ν →
          MemLp (fun z : E × E => z) 2 μ → MemLp (fun z : E × E => z) 2 ν →
          transportDistance ((flowLaw μ P (X t)).map (newtonCoordinateEquiv δ b hp))
            ((flowLaw ν P (X t)).map (newtonCoordinateEquiv δ b hp)) ≤
            Real.exp (-r*t)*transportDistance (μ.map (newtonCoordinateEquiv δ b hp))
              (ν.map (newtonCoordinateEquiv δ b hp)) := by
  have hu : 0≤u := hl.le.trans hlu
  have hg := hessian_bounds_lipschitz g H ⟨u,hu⟩ hd hs (fun x z =>
    ⟨(mul_nonneg hl.le (sq_nonneg _)).trans (hb x z).1,(hb x z).2⟩)
  obtain ⟨X,hm,hc,h₀,hq,hv⟩ := constructed_newton_flow g ⟨u,hu⟩ hg δ T hT W hWm hWc hW0
  refine ⟨X,hm,hc,h₀,hq,hv,?_⟩
  apply newton_finite_shared_noise_transport P l u δ hl hlu hδ g H hd hH hs hb T hT
    X (fun w t => W t w) (fun t _ => hm t)
  intro x
  apply ae_of_all
  intro w
  exact ⟨(hc x w).fst,(hc x w).snd,h₀ x w,hq x w,hv x w⟩

end Asakura.Chapter8
