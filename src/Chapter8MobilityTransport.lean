import Chapter8MobilitySDEContraction
import Chapter8ConjugateFlow

open MeasureTheory
open scoped RealInnerProductSpace
namespace Asakura.Chapter8
open Asakura.FullAudit Asakura.Chapter4 Asakura.Chapter3Complete
open Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

/-- Actual synchronous SDE contraction implies convergence to any invariant
P2 law in precisely the inverse-mobility distance used in the manuscript. -/
theorem mobility_invariant_transport {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (P : Measure Ω) [IsProbabilityMeasure P] {d n : ℕ} (B : BrownianSystem P n)
    (e : (Fin d → ℝ) ≃L[ℝ] E) (M : E ≃L[ℝ] E)
    (hs : M.toContinuousLinearMap.toLinearMap.IsSymmetric)
    (α κ : ℝ) (hα : 0<α) (hκ : 0<κ) (hM : ∀ z,α*‖z‖^2≤⟪z,M z⟫)
    (g : E → E) (hg : Continuous g)
    (hmono : ∀ x y,κ*‖x-y‖^2≤⟪x-y,g x-g y⟫)
    (σ : Fin d → Fin n → ℝ)
    (Z : (Fin d → ℝ) → HalfClosedTime → Ω → Fin d → ℝ)
    (hZ : ∀ x,VectorSDESolution P B.F B.W
      (fun i x => -(e.symm (M (g (e x))) i)) (fun i j _ => σ i j) (fun _ => x) (Z x)) :
    ∃ A : E ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E)),
      (∀ z,‖A z‖^2=⟪z,M.symm z⟫) ∧
      ∀ T≥0,∀ F : (Fin d → ℝ) → Ω → (Fin d → ℝ),
        Measurable (Function.uncurry F) → (∀ x,F x=ᵐ[P] Z x (realTimeClamp T)) →
        ∀ (μ π : Measure (Fin d → ℝ)),IsProbabilityMeasure μ → IsProbabilityMeasure π →
          MemLp (fun z => z) 2 μ → MemLp (fun z => z) 2 π → flowLaw π P F=π →
          transportDistance ((flowLaw μ P F).map (e.trans A)) (π.map (e.trans A))≤
            Real.exp (-(κ*α)*T)*transportDistance (μ.map (e.trans A)) (π.map (e.trans A)) := by
  obtain ⟨A,hAn,hAc⟩ := mobility_sde_contraction P B e M hs α κ hα hκ hM g hg hmono σ
  refine ⟨A,hAn,?_⟩
  intro T hT F hF hFe μ π hμp hπp hμ hπ hInv
  letI := hμp
  letI := hπp
  let C := e.trans A
  have hm (η : Measure (Fin d → ℝ)) (hη : MemLp (fun z => z) 2 η) :
      MemLp (fun z : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) => z) 2 (η.map C) := by
    apply C.toHomeomorph.toMeasurableEquiv.memLp_map_measure_iff.mpr
    exact C.toContinuousLinearMap.comp_memLp' hη
  have hc (x y : Fin d → ℝ) : ∀ᵐ w ∂P,
      ‖C (F x w)-C (F y w)‖≤Real.exp (-(κ*α)*T)*‖C x-C y‖ := by
    filter_upwards [hAc (fun _ => x) (fun _ => y) (Z x) (Z y) (hZ x) (hZ y),hFe x,hFe y]
      with w hw hx hy
    rw [hx,hy]
    exact hw T hT
  have hh := conjugate_shared_noise_contraction C.toHomeomorph.toMeasurableEquiv μ π P F hF
    (hm μ hμ) (hm π hπ) (Real.exp (-(κ*α)*T)) (Real.exp_pos _) hc
  rw [hInv] at hh
  exact hh

end Asakura.Chapter8
