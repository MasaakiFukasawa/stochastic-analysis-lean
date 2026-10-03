import Chapter8ConvexPotentialCoordinateData
import Chapter8NewtonGibbsMoment
import Chapter8NewtonForceScaling
import Chapter8NewtonDriftLipschitz
import Chapter8QuadraticNewtonPhysicalConvergence
import Chapter8PositiveQuadraticBounds

open MeasureTheory ProbabilityTheory
open scoped BigOperators RealInnerProductSpace NNReal ENNReal
namespace Asakura.Chapter8
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4
attribute [local instance] nestedOpNormed nestedOpSpace nestedBiNormed nestedBiSpace
attribute [local instance] scalarOpNormed scalarOpSpace scalarBiNormed scalarBiSpace
set_option maxHeartbeats 3500000
set_option maxRecDepth 3000
set_option backward.isDefEq.respectTransparency false
local instance {d : ℕ} : MeasurableSpace (WithLp 2 (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d))) := borel _
local instance {d : ℕ} : BorelSpace (WithLp 2 (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d))) := ⟨rfl⟩

/-- The positive quadratic Newton potential admits geometric convergence
for all positive masses, frictions and inverse temperatures. -/
theorem quadratic_newton_manuscript {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} [NeZero d] (B : BrownianSystem P d)
    (K : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (hs : K.toLinearMap.IsSymmetric) (hK : ∀ z≠0,0<⟪z,K z⟫)
    (β m γ : ℝ) (hβ : 0<β) (hm : 0<m) (hγ : 0<γ) :
    let U := fun x => ⟪x,K x⟫/2
    let e := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).symm
    let V := fun q => U (e q)
    let H := newtonHamiltonian V m
    let π := volume.withDensity (fun z : Fin (d+d) → ℝ =>
      ENNReal.ofReal ((∫ y : Fin (d+d) → ℝ,Real.exp (-β*H y))⁻¹*Real.exp (-β*H z)))
    let R := (phaseLinearEquiv e).trans (WithLp.prodContinuousLinearEquiv 2 ℝ _ _).symm
    IsProbabilityMeasure π ∧ MemLp (fun z => z) 2 π ∧
      π.map (phaseMeasurableEquiv d)=
        (volume.withDensity (fun q : Fin d → ℝ => ENNReal.ofReal
          ((∫ y : Fin d → ℝ,Real.exp (-β*V y))⁻¹*Real.exp (-β*V q)))).prod
        (Measure.pi (fun _ : Fin d => gaussianReal 0 ⟨(β*m)⁻¹,by positivity⟩)) ∧
    ∃ Z : (Fin (d+d) → ℝ) → HalfClosedTime → Ω → Fin (d+d) → ℝ,
      (∀ x,VectorSDESolution P B.F B.W
        (Fin.addCases (fun i z => velocityProjection d z i)
          (fun i z => -(fderiv ℝ V (positionProjection d z) (Pi.single i 1)+γ*velocityProjection d z i)/m))
        (fun i j _ => newtonNoise d (Real.sqrt (2*γ*β⁻¹)/m) i j) (fun _ => x) (Z x)) ∧
      ∃ (A : (Fin (d+d) → ℝ) ≃L[ℝ] WithLp 2
        (EuclideanSpace ℝ (Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)))) ×
         EuclideanSpace ℝ (Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin d))))))
        (r : ℝ),0<r ∧
        ∃ C : ℝ,0<C ∧ ∀ T≥0,∃ F : (Fin (d+d) → ℝ) → Ω → (Fin (d+d) → ℝ),
          Measurable (Function.uncurry F) ∧ (∀ x,F x=ᵐ[P] Z x (realTimeClamp T)) ∧ flowLaw π P F=π ∧
          (∀ (μ ν : Measure (Fin (d+d) → ℝ)),IsProbabilityMeasure μ → IsProbabilityMeasure ν →
            MemLp (fun z => z) 2 μ → MemLp (fun z => z) 2 ν →
            transportDistance ((flowLaw μ P F).map A) ((flowLaw ν P F).map A)≤
              Real.exp (-r*T)*transportDistance (μ.map A) (ν.map A)) ∧
          (∀ (μ : Measure (Fin (d+d) → ℝ)),IsProbabilityMeasure μ → MemLp (fun z => z) 2 μ →
            transportDistance ((flowLaw μ P F).map R) (π.map R)≤C*Real.exp (-r*T)*transportDistance (μ.map R) (π.map R)) ∧
          (0<T → ∀ (ν : Measure (Fin (d+d) → ℝ)),IsProbabilityMeasure ν → MemLp (fun z => z) 2 ν →
            flowLaw ν P F=ν → ν=π) := by
  dsimp only
  let U := fun x => ⟪x,K x⟫/2
  let e := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).symm
  let V := fun q => U (e q)
  let Hamil := newtonHamiltonian V m
  let π := volume.withDensity (fun z : Fin (d+d) → ℝ =>
    ENNReal.ofReal ((∫ y : Fin (d+d) → ℝ,Real.exp (-β*Hamil y))⁻¹*Real.exp (-β*Hamil z)))
  obtain ⟨κ,L,hκ,hκL,hB⟩ := positive_quadratic_bounds K hs hK
  obtain ⟨hU,hDU,hD₂,hD₃⟩ := quadratic_potential_derivatives K hs
  have hb x z : κ*‖z‖^2≤fderiv ℝ (fderiv ℝ U) x z z ∧
      fderiv ℝ (fderiv ℝ U) x z z≤L*‖z‖^2 := by
    rw [hD₂,real_inner_comm z (K z)]
    exact hB z
  obtain ⟨g,H,C₂,C₃,hd,hH,hsH,hBH,hgrad,hV,h₂,h₃',hi⟩ :=
    convex_potential_coordinate_data U hU κ L β hκ hκL hβ hb 0
      (fun x => by
        rw [hD₃]
        exact le_of_eq (ContinuousLinearMap.opNorm_zero))
  have hgradK q : K (e q)=e (fun i => fderiv ℝ V q (Pi.single i 1)) := by
    ext i
    have hh := ((hU.differentiable (by norm_num)).differentiableAt.hasFDerivAt).comp q e.hasFDerivAt
    change HasFDerivAt V ((fderiv ℝ U (e q)).comp e.toContinuousLinearMap) q at hh
    rw [hDU] at hh
    have he : fderiv ℝ V q (Pi.single i 1)=K (e q) i := by
      rw [hh.fderiv]
      change ⟪K (e q),EuclideanSpace.single i (1:ℝ)⟫=K (e q) i
      simp only [EuclideanSpace.inner_single_right,conj_trivial,one_mul]
    exact he.symm
  obtain ⟨hπp,hprod,Z,hZ,hinv⟩ := newton_gibbs_maxwell_manuscript P B V hV C₂ C₃ h₂ h₃' β m γ hβ hm hγ hi
  haveI : IsProbabilityMeasure π := hπp
  have hπ := newton_gibbs_memLp V hV.continuous β m hβ hm hi
  refine ⟨hπp,hπ,hprod,Z,hZ,?_⟩
  let K' : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) := m⁻¹ • K
  have hs' : K'.toLinearMap.IsSymmetric := by
    intro q v
    change ⟪m⁻¹ • K q,v⟫=⟪q,m⁻¹ • K v⟫
    rw [real_inner_smul_left,inner_smul_right]
    exact congrArg (fun a : ℝ => m⁻¹*a) (hs q v)
  have hK' z (hz : z≠0) : 0<⟪z,K' z⟫ := by
    change 0<⟪z,m⁻¹ • K z⟫
    rw [inner_smul_right]
    exact mul_pos (inv_pos.mpr hm) (hK z hz)
  let σ := fun i j : Fin d => if i=j then Real.sqrt (2*γ*β⁻¹)/m else 0
  have hdrift := newton_mass_drift_identification e V K' m γ (fun q => by
    change m⁻¹ • K (e q)=_
    rw [hgradK])
  have hnoise : Fin.addCases (motive := fun _ : Fin (d+d) => Fin d → (Fin (d+d) → ℝ) → ℝ)
      (fun _ _ _ => 0) (fun i j _ => σ i j)=(fun i j _ => newtonNoise d (Real.sqrt (2*γ*β⁻¹)/m) i j) := by
    funext i j z
    refine Fin.addCases ?_ ?_ i <;> intro k <;> simp only [Fin.addCases_left,Fin.addCases_right,newtonNoise,σ]
  have hZ' x : VectorSDESolution P B.F B.W
      (Fin.addCases (fun i z => velocityProjection d z i)
        (fun i z => e.symm (-K' (e (positionProjection d z))-(γ/m) • e (velocityProjection d z)) i))
      (Fin.addCases (fun _ _ _ => 0) (fun i j _ => σ i j)) (fun _ => x) (Z x) := by
    rw [hdrift,hnoise]
    exact hZ x
  obtain ⟨L₀,hL₀,hLip⟩ := newton_drift_lipschitz e K' ‖K'‖₊ K'.lipschitz (γ/m)
  obtain ⟨A,r,hr,C,hC,hconv⟩ := quadratic_newton_sde_physical_convergence P B e K' hs' hK' (γ/m)
    (div_pos hγ hm) σ Z hZ' L₀ hL₀ hLip π hπ
  refine ⟨A,r,hr,C,hC,?_⟩
  intro T hT
  obtain ⟨Y,hY,hYe,hYi⟩ := hinv T hT
  let F := Function.curry Y
  have hFm : Measurable (Function.uncurry F) := hY
  have hFe x : F x=ᵐ[P] Z x (realTimeClamp T) := hYe x
  have hFi : flowLaw π P F=π := hYi
  exact ⟨F,hFm,hFe,hFi,hconv T hT F hFm hFe hFi⟩

end Asakura.Chapter8
