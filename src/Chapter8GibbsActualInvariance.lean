import Chapter8SmoothDiffusionInvariantTests
import Chapter8ActualInvariantLaw
import Chapter8NormalizedGibbsMeasure
import Chapter8GibbsGeneratorIdentification
import Chapter8LipschitzGrowthData

open MeasureTheory Set
open scoped NNReal BigOperators ENNReal
namespace Asakura.Chapter8
open Asakura.Chapter4 Asakura.Chapter3Complete Asakura.FullAudit
open Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

/-- Gibbs invariance for a constructed actual SDE family. The coefficient
derivatives are actual derivatives; neither a smooth semigroup, a Dynkin
identity, nor preservation of the density is assumed. Degenerate noise is allowed. -/
theorem gibbs_actual_invariance {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d n : ℕ} (B : BrownianSystem P n)
    (U : (Fin d → ℝ) → ℝ) (DU : (Fin d → ℝ) → (Fin d → ℝ) →L[ℝ] ℝ)
    (hU : ∀ x,HasFDerivAt U (DU x) x) (hDU : Continuous DU)
    (β : ℝ) (hβ : β≠0)
    (hi : Integrable (fun x : Fin d → ℝ => (1+‖x‖^2)*Real.exp (-β*U x)))
    (M : Fin d → Fin d → ℝ) (hM : ∀ i j,M i j=M j i)
    (σ : Fin d → Fin n → ℝ) (hσ : ∀ i j,∑ k,σ i k*σ j k=2*β⁻¹*M i j)
    (b : (Fin d → ℝ) → (Fin d → ℝ))
    (hbform : ∀ x i,b x i= -(∑ j,M i j*DU x (Pi.single j 1)))
    (D : (Fin d → ℝ) → (Fin d → ℝ) →L[ℝ] (Fin d → ℝ))
    (D₂ : (Fin d → ℝ) → (Fin d → ℝ) →L[ℝ] (Fin d → ℝ) →L[ℝ] (Fin d → ℝ))
    (hD : ∀ z,HasFDerivAt b (D z) z) (hD₂ : ∀ z,HasFDerivAt D (D₂ z) z)
    (hcD₂ : Continuous D₂) (C L : ℝ≥0) (hDC : LipschitzWith C D)
    (hL : 0<L) (hDb : ∀ z,‖D z‖ ≤ (L:ℝ))
    (Cg : ℝ) (hCg : 0≤Cg) (hgrad : ∀ i x,|DU x (Pi.single i 1)|≤Cg*(1+‖x‖)) :
    let π := volume.withDensity (fun x : Fin d → ℝ =>
      ENNReal.ofReal ((∫ y : Fin d → ℝ,Real.exp (-β*U y))⁻¹*Real.exp (-β*U x)))
    IsProbabilityMeasure π ∧
    ∃ Z : (Fin d → ℝ) → HalfClosedTime → Ω → Fin d → ℝ,
      (∀ x,VectorSDESolution P B.F B.W (fun i y => b y i) (fun i j _ => σ i j) (fun _ => x) (Z x)) ∧
      ∀ T : ℝ,0≤T → ∃ Y : (Fin d → ℝ) × Ω → (Fin d → ℝ),Measurable Y ∧
        (∀ x,(fun w => Y (x,w))=ᵐ[P] Z x (realTimeClamp T)) ∧ (π.prod P).map Y=π := by
  dsimp only
  let π := volume.withDensity (fun x : Fin d → ℝ =>
    ENNReal.ofReal ((∫ y : Fin d → ℝ,Real.exp (-β*U y))⁻¹*Real.exp (-β*U x)))
  have hUc := continuous_iff_continuousAt.mpr (fun x => (hU x).continuousAt)
  obtain ⟨hpart,hprob,hπ,_,hint⟩ := normalized_gibbs_measure U hUc β hi
  letI : IsProbabilityMeasure π := hprob
  have hb : LipschitzWith L b := by
    apply lipschitzWith_of_nnnorm_fderiv_le (fun z => (hD z).differentiableAt)
    intro z
    rw [(hD z).fderiv]
    exact_mod_cast hDb z
  obtain ⟨Cb,hCb,hbg⟩ := lipschitz_linear_growth b L hb
  let Lip := (d:ℝ)*(L:ℝ)^2
  have hLip : 0≤Lip := by positivity
  have hcoeff := lipschitz_square_coordinates b L hb
  have hcoeff' x y : (∑ i,(b x i-b y i)^2)+(∑ i : Fin d,∑ j : Fin n,(σ i j-σ i j)^2)≤Lip*∑ i,(x i-y i)^2 := by
    simpa only [sub_self,zero_pow (by norm_num : 2≠0),Finset.sum_const_zero,add_zero] using hcoeff x y
  obtain ⟨Z,hZ⟩ := deterministic_sde_family_exists P B Lip hLip (fun i y => b y i) (fun i j _ => σ i j) hcoeff'
  have hzero (g : (Fin d → ℝ) → ℝ) (hg : ContDiff ℝ 2 g) (A K : ℝ) (hA : 0≤A) (hK : 0≤K)
      (h1 : ∀ x,‖fderiv ℝ g x‖≤A) (h2 : ∀ x,‖fderiv ℝ (fderiv ℝ g) x‖≤K) :
      (∫ x,coordinateGenerator (fun i y => b y i) (fun i j _ => σ i j) g x ∂π)=0 := by
    rw [hint]
    have hb' : (fun i y => b y i)=(fun i y => -(∑ j,M i j*DU y (Pi.single j 1))) := by
      funext i y; exact hbform y i
    rw [hb']
    simp_rw [gibbs_generator_identification DU M σ β hM hσ g]
    have he (i : Fin d) : ‖(Pi.single i 1 : Fin d → ℝ)‖≤1 := by
      apply (pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ)≤1)).mpr
      intro j
      by_cases h : j=i <;> simp [h]
    rw [gibbs_C2_generator_zero U DU β hβ hU hDU hi g hg (fun i => Pi.single i 1) he M
      A K Cg hA hK hCg h1 h2 hgrad,mul_zero]
  refine ⟨hprob,Z,hZ,?_⟩
  intro T hT
  apply actual_invariant_law P B b σ L hb Z hZ π T hT
  intro f hf hs
  exact smooth_diffusion_invariant_tests P B b σ D D₂ hD hD₂ hcD₂ C L hDC hL hDb
    Lip hLip hcoeff Cb hCb hbg Z hZ π hπ hzero T hT f hf hs

end Asakura.Chapter8
