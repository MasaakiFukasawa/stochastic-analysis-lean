import Chapter8EuclideanOperatorMatrix
import Chapter8ConvexPotentialCoordinateData
import Chapter8MobilityTransport
import Chapter8GibbsManuscript

open MeasureTheory
open scoped BigOperators RealInnerProductSpace NNReal ENNReal
namespace Asakura.Chapter8
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4
attribute [local instance] scalarOpNormed scalarOpSpace scalarBiNormed scalarBiSpace
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

/-- The positive-mobility paragraph follows from the original potential,
Einstein relation and positive matrix, with the actual Gibbs law and SDE. -/
theorem mobility_gibbs_manuscript {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d n : ℕ} (B : BrownianSystem P n)
    (U : EuclideanSpace ℝ (Fin d) → ℝ) (hU : ContDiff ℝ 3 U)
    (κ L β : ℝ) (hκ : 0<κ) (hκL : κ≤L) (hβ : 0<β)
    (hb : ∀ x z,κ*‖z‖^2≤fderiv ℝ (fderiv ℝ U) x z z ∧
      fderiv ℝ (fderiv ℝ U) x z z≤L*‖z‖^2)
    (A₃ : ℝ≥0) (h₃ : ∀ x,‖fderiv ℝ (fderiv ℝ (fderiv ℝ U)) x‖≤(A₃:ℝ))
    (M : EuclideanSpace ℝ (Fin d) ≃L[ℝ] EuclideanSpace ℝ (Fin d))
    (hs : M.toContinuousLinearMap.toLinearMap.IsSymmetric)
    (α : ℝ) (hα : 0<α) (hM : ∀ z,α*‖z‖^2≤⟪z,M z⟫)
    (σ : Fin d → Fin n → ℝ)
    (hσ : ∀ i j,∑ k,σ i k*σ j k=2*β⁻¹*M (EuclideanSpace.single j 1) i) :
    let e := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).symm
    let V := fun q => U (e q)
    let π := volume.withDensity (fun q : Fin d → ℝ =>
      ENNReal.ofReal ((∫ y : Fin d → ℝ,Real.exp (-β*V y))⁻¹*Real.exp (-β*V q)))
    IsProbabilityMeasure π ∧ MemLp (fun q => q) 2 π ∧
    ∃ (A : EuclideanSpace ℝ (Fin d) ≃L[ℝ]
      EuclideanSpace ℝ (Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)))))
      (Z : (Fin d → ℝ) → HalfClosedTime → Ω → Fin d → ℝ),
      (∀ z,‖A z‖^2=⟪z,M.symm z⟫) ∧
      (∀ x,VectorSDESolution P B.F B.W
        (fun i y => -(∑ j,M (EuclideanSpace.single j 1) i*fderiv ℝ V y (Pi.single j 1)))
        (fun i j _ => σ i j) (fun _ => x) (Z x)) ∧
      ∀ T≥0,∃ F : (Fin d → ℝ) → Ω → (Fin d → ℝ),
        Measurable (Function.uncurry F) ∧ (∀ x,F x=ᵐ[P] Z x (realTimeClamp T)) ∧ flowLaw π P F=π ∧
        ∀ (μ : Measure (Fin d → ℝ)),IsProbabilityMeasure μ → MemLp (fun q => q) 2 μ →
          transportDistance ((flowLaw μ P F).map (e.trans A)) (π.map (e.trans A))≤
            Real.exp (-(κ*α)*T)*transportDistance (μ.map (e.trans A)) (π.map (e.trans A)) := by
  dsimp only
  let e := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).symm
  let V := fun q => U (e q)
  let π := volume.withDensity (fun q : Fin d → ℝ =>
    ENNReal.ofReal ((∫ y : Fin d → ℝ,Real.exp (-β*V y))⁻¹*Real.exp (-β*V q)))
  obtain ⟨g,H,C₂,C₃,hd,hH,hHs,hB,hgrad,hV,h₂,h₃',hi⟩ :=
    convex_potential_coordinate_data U hU κ L β hκ hκL hβ hb A₃ h₃
  have hMs i j := euclidean_operator_matrix_symmetric M.toContinuousLinearMap hs i j
  obtain ⟨hπp,Z,hZ,hinv⟩ := gibbs_manuscript_invariance P B V hV C₂ C₃ h₂ h₃' β hβ hi
    (fun i j => M (EuclideanSpace.single j 1) i) hMs σ hσ
  haveI : IsProbabilityMeasure π := hπp
  have hinorm : Integrable (fun x : Fin d → ℝ => (1+‖x‖^2)*Real.exp (-β*V x)) := by
    apply hi.mono' (by fun_prop)
    apply ae_of_all
    intro x
    rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_right (add_le_add le_rfl (pi_norm_sq_le_sum_sq x)) (Real.exp_pos _).le
  have hπ : MemLp (fun q => q) 2 π := (memLp_two_iff_integrable_sq_norm measurable_id.aestronglyMeasurable).mpr
    (normalized_gibbs_measure V hV.continuous β hinorm).2.2.2.1
  have hc (q : Fin d → ℝ) (i : Fin d) :
      e.symm (M (g (e q))) i=∑ j,M (EuclideanSpace.single j 1) i*fderiv ℝ V q (Pi.single j 1) := by
    change M (g (e q)) i=_
    have ha : M (g (e q)) i=∑ j,M (EuclideanSpace.single j 1) i*g (e q) j :=
      euclidean_operator_matrix_action M.toContinuousLinearMap (g (e q)) i
    rw [ha]
    apply Finset.sum_congr rfl
    intro j _
    have hh := congrArg (fun z : EuclideanSpace ℝ (Fin d) => z j) (hgrad q)
    change g (e q) j=fderiv ℝ V q (Pi.single j 1) at hh
    rw [hh]
  have hZ' x : VectorSDESolution P B.F B.W
      (fun i y => -(e.symm (M (g (e y))) i)) (fun i j _ => σ i j) (fun _ => x) (Z x) := by
    simp_rw [hc]
    exact hZ x
  have hg : Continuous g := continuous_iff_continuousAt.mpr (fun x => (hd x).continuousAt)
  have hmono := langevin_gradient_monotone g H κ hd (fun x z => (hB x z).1)
  obtain ⟨A,hAn,hconv⟩ := mobility_invariant_transport P B e M hs α κ hα hκ hM g hg hmono σ Z hZ'
  refine ⟨hπp,hπ,A,Z,hAn,hZ,?_⟩
  intro T hT
  obtain ⟨Y,hY,hYe,hYi⟩ := hinv T hT
  let F := Function.curry Y
  refine ⟨F,hY,hYe,hYi,?_⟩
  intro μ hμp hμ
  exact hconv T hT F hY hYe μ π hμp hπp hμ hπ hYi

end Asakura.Chapter8
