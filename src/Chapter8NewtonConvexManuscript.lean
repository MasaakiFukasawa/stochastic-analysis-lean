import Chapter8ConvexPotentialCoordinateData
import Chapter8NewtonGibbsMoment
import Chapter8NewtonForceScaling
import Chapter8NewtonDriftLipschitz
import Chapter8NewtonPhysicalConvergence

open MeasureTheory ProbabilityTheory
open scoped BigOperators RealInnerProductSpace NNReal ENNReal
namespace Asakura.Chapter8
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4
attribute [local instance] scalarOpNormed scalarOpSpace scalarBiNormed scalarBiSpace
set_option maxHeartbeats 3500000
set_option maxRecDepth 3000
set_option backward.isDefEq.respectTransparency false
local instance {d : ℕ} : MeasurableSpace (WithLp 2 (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d))) := borel _
local instance {d : ℕ} : BorelSpace (WithLp 2 (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d))) := ⟨rfl⟩

/-- The uniformly convex Newton theorem, from the original potential and
friction assumptions to actual SDE solutions, Gibbs-Maxwell invariance,
quadratic transport contraction, physical Euclidean convergence and uniqueness. -/
theorem newton_convex_manuscript {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (B : BrownianSystem P d)
    (U : EuclideanSpace ℝ (Fin d) → ℝ) (hU : ContDiff ℝ 3 U)
    (κ L β m γ : ℝ) (hκ : 0<κ) (hκL : κ≤L) (hβ : 0<β) (hm : 0<m)
    (hfr : Real.sqrt m*(Real.sqrt L-Real.sqrt κ)<γ)
    (hb : ∀ x z,κ*‖z‖^2≤fderiv ℝ (fderiv ℝ U) x z z ∧
      fderiv ℝ (fderiv ℝ U) x z z≤L*‖z‖^2)
    (A₃ : ℝ≥0) (h₃ : ∀ x,‖fderiv ℝ (fderiv ℝ (fderiv ℝ U)) x‖≤(A₃:ℝ)) :
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
      ∃ b r : ℝ,0<r ∧ ∃ hp : 0<b+(γ/m)^2/4,
        let A := (phaseLinearEquiv e).trans (newtonCoordinateEquiv (γ/m) b hp)
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
  let e := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).symm
  let V := fun q => U (e q)
  let Hamil := newtonHamiltonian V m
  let π := volume.withDensity (fun z : Fin (d+d) → ℝ =>
    ENNReal.ofReal ((∫ y : Fin (d+d) → ℝ,Real.exp (-β*Hamil y))⁻¹*Real.exp (-β*Hamil z)))
  obtain ⟨g,H,C₂,C₃,hd,hH,hs,hB,hgrad,hV,h₂,h₃',hi⟩ :=
    convex_potential_coordinate_data U hU κ L β hκ hκL hβ hb A₃ h₃
  have hγ : 0<γ := lt_of_le_of_lt
    (mul_nonneg (Real.sqrt_nonneg m) (sub_nonneg.mpr (Real.sqrt_le_sqrt hκL))) hfr
  obtain ⟨hπp,hprod,Z,hZ,hinv⟩ := newton_gibbs_maxwell_manuscript P B V hV C₂ C₃ h₂ h₃' β m γ hβ hm hγ hi
  haveI : IsProbabilityMeasure π := hπp
  have hπ := newton_gibbs_memLp V hV.continuous β m hβ hm hi
  refine ⟨hπp,hπ,hprod,Z,hZ,?_⟩
  let g' := fun x => m⁻¹ • g x
  let H' := fun x => m⁻¹ • H x
  obtain ⟨hd',hH',hB',hfr'⟩ := newton_mass_hessian_scaling g H hd hH κ L m γ hm hκ hκL hB hfr
  have hs' x : (H' x).toLinearMap.IsSymmetric := by
    intro q v
    change ⟪m⁻¹ • H x q,v⟫=⟪q,m⁻¹ • H x v⟫
    rw [real_inner_smul_left,inner_smul_right]
    exact congrArg (fun a : ℝ => m⁻¹*a) (hs x q v)
  let σ := fun i j : Fin d => if i=j then Real.sqrt (2*γ*β⁻¹)/m else 0
  have hdrift := newton_mass_drift_identification e V g' m γ (fun q => by
    change m⁻¹ • g (e q)=_
    rw [hgrad])
  have hnoise : Fin.addCases (motive := fun _ : Fin (d+d) => Fin d → (Fin (d+d) → ℝ) → ℝ)
      (fun _ _ _ => 0) (fun i j _ => σ i j)=(fun i j _ => newtonNoise d (Real.sqrt (2*γ*β⁻¹)/m) i j) := by
    funext i j z
    refine Fin.addCases ?_ ?_ i <;> intro k <;> simp only [Fin.addCases_left,Fin.addCases_right,newtonNoise,σ]
  have hZ' x : VectorSDESolution P B.F B.W
      (Fin.addCases (fun i z => velocityProjection d z i)
        (fun i z => e.symm (-g' (e (positionProjection d z))-(γ/m) • e (velocityProjection d z)) i))
      (Fin.addCases (fun _ _ _ => 0) (fun i j _ => σ i j)) (fun _ => x) (Z x) := by
    rw [hdrift,hnoise]
    exact hZ x
  have hLipg := hessian_bounds_lipschitz g' H' ⟨L/m,div_nonneg (hκ.le.trans hκL) hm.le⟩ hd' hs'
    (fun x z => ⟨(mul_nonneg (div_nonneg hκ.le hm.le) (sq_nonneg _)).trans (hB' x z).1,(hB' x z).2⟩)
  obtain ⟨K,hK,hLip⟩ := newton_drift_lipschitz e g' _ hLipg (γ/m)
  obtain ⟨b,r,hr,hp,C,hC,hconv⟩ := newton_sde_physical_convergence P B e g' H' (κ/m) (L/m) (γ/m)
    (div_pos hκ hm) (div_le_div_of_nonneg_right hκL hm.le) hfr' hd' hH' hs' hB' σ Z hZ' K hK hLip π hπ
  refine ⟨b,r,hr,hp,C,hC,?_⟩
  intro T hT
  obtain ⟨Y,hY,hYe,hYi⟩ := hinv T hT
  let F := Function.curry Y
  have hFm : Measurable (Function.uncurry F) := hY
  have hFe x : F x=ᵐ[P] Z x (realTimeClamp T) := hYe x
  have hFi : flowLaw π P F=π := hYi
  exact ⟨F,hFm,hFe,hFi,hconv T hT F hFm hFe hFi⟩

end Asakura.Chapter8
