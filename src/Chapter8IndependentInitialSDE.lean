import Chapter8IndependentInitialBrownian
import Chapter8SDEStationaryLaw
import Chapter4DeterministicSDEFamily
import Mathlib.MeasureTheory.Function.LpSeminorm.Prod

open MeasureTheory Set
open scoped NNReal BigOperators
namespace Asakura.Chapter8
open Asakura.FullAudit Asakura.Chapter4 Asakura.Chapter3Complete
open Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

/-- The independent initial state and the actual SDE solution are constructed
on the product space. Invariant transition integrals then give a stationary law. -/
theorem independent_initial_sde {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d n : ℕ} (B : BrownianSystem P n)
    (π : Measure (Fin d → ℝ)) [IsProbabilityMeasure π]
    (hπ : MemLp (fun x : Fin d → ℝ => x) 2 π)
    (L : ℝ) (hL : 0≤L)
    (b : Fin d → (Fin d → ℝ) → ℝ) (σ : Fin d → Fin n → (Fin d → ℝ) → ℝ)
    (hLip : ∀ x y,(∑ i,(b i x-b i y)^2)+(∑ i,∑ j,(σ i j x-σ i j y)^2)≤L*∑ i,(x i-y i)^2) :
    ∃ B' : BrownianSystem (π.prod P) n,
      (∀ j t z,B'.W j t z=B.W j t z.2) ∧
      ∃ (X : HalfClosedTime → (Fin d → ℝ) × Ω → Fin d → ℝ)
        (Z : (Fin d → ℝ) → HalfClosedTime → (Fin d → ℝ) × Ω → Fin d → ℝ),
        VectorSDESolution (π.prod P) B'.F B'.W b σ Prod.fst X ∧
        (∀ x,VectorSDESolution (π.prod P) B'.F B'.W b σ (fun _ => x) (Z x)) ∧
        ((∀ t : ℝ,0≤t → ∀ f : (Fin d → ℝ) → ℝ,
          ContDiff ℝ (⊤:ℕ∞) f → HasCompactSupport f →
          (∫ x,(∫ w,f (Z x (realTimeClamp t) w) ∂π.prod P) ∂π)=∫ x,f x ∂π) →
          ∀ t : ℝ,0≤t → (π.prod P).map (X (realTimeClamp t))=π) := by
  obtain ⟨B',hB',hξm⟩ := independent_initial_brownian π P B
  have hξ : MemLp (Prod.fst : (Fin d → ℝ) × Ω → Fin d → ℝ) 2 (π.prod P) :=
    hπ.comp_fst P
  obtain ⟨X,N,ha,hc,hN,hI,_,he⟩ := Vector.sde_exists_from_manuscript_hypotheses
    (π.prod P) (EReal.coe_lt_top 0) B'.F B'.mono B'.le B'.null B'.W (fun j => B'.C j j)
    B'.martingale (fun j => B'.cov j j) (fun j w r hr _ => B'.diagonal_clock j w r hr)
    L hL b σ hLip Prod.fst (hξm ⊥) hξ
  have hX : VectorSDESolution (π.prod P) B'.F B'.W b σ Prod.fst X :=
    ⟨hξm ⊥,ha,hc,N,hN,hI,he⟩
  obtain ⟨Z,hZ⟩ := deterministic_sde_family_exists (π.prod P) B' L hL b σ hLip
  refine ⟨B',hB',X,Z,hX,hZ,?_⟩
  intro hinv t ht
  apply sde_stationary_law (π.prod P) B' L hL b σ hLip π Prod.fst hξ _ X hX Z hZ hinv t ht
  rw [Measure.map_fst_prod,measure_univ,one_smul]

end Asakura.Chapter8
