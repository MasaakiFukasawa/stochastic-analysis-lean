import EndToEndIndependentBrownianSystem
import EndToEndTwoItoIntegrals
import EndToEndMVNIntegrands
import MandelbrotVanNess

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal
namespace Asakura.EndToEnd
open Asakura Asakura.FullAudit Asakura.Chapter2Complete Asakura.Chapter4
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

/-- The printed independent-Brownian assumptions imply the MVN process,
with the actual scalar Ito integrals and their infinite-horizon L2 limits.
The L2 integrand representatives are identified with the displayed kernels
by restricted_mvn_future_formula and restricted_mvn_past_formula. -/
theorem mandelbrot_van_ness_from_independent_brownian
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : ℝ≥0 → Ω → ℝ) (hX : IsPreBrownianReal X P) (hY : IsPreBrownianReal Y P)
    (hmX : ∀ t, Measurable (X t)) (hmY : ∀ t, Measurable (Y t))
    (hcX : ∀ ω, Continuous (fun t => X t ω)) (hcY : ∀ ω, Continuous (fun t => Y t ω))
    (hI : IndepFun (fun ω t => X t ω) (fun ω t => Y t ω) P)
    (H : ℝ) (hH0 : 0 < H) (hH1 : H < 1) :
    let B := independentBrownianSystem P X Y hX hY hmX hmY hcX hcY hI
    ∃ Z : ℝ≥0 → Ω → ℝ,
      (∀ t, Measurable (Z t)) ∧ (∀ ω, Continuous (fun t => Z t ω)) ∧
      IsGaussianProcess Z P ∧ (∀ t, (∫ ω, Z t ω ∂P) = 0) ∧
      (∀ s t, (∫ ω, Z s ω * Z t ω ∂P) =
        ((s:ℝ)^(2*H)+(t:ℝ)^(2*H)-|(s:ℝ)-(t:ℝ)|^(2*H))/2) ∧
      (∀ᵐ ω ∂P, ∀ α : ℝ, 0 ≤ α → α < H → ∀ n : ℕ,
        ∃ C : ℝ, 0 ≤ C ∧ ∀ s t : ℝ≥0, s ≤ n → t ≤ n →
          dist (Z s ω) (Z t ω) ≤ C * (dist s t)^α) ∧
      0 < mvnNormalization H ∧
      (∀ t, ∃ N : Fin 2 → HalfClosedTime → Ω → ℝ,
        ∃ hN : ∀ i, ContinuousM2Witness P B.F (N i),
          ItoCovarianceFormula P B.F (fun r ω => X (halfTimeReal r) ω)
            (fun z => L2Restriction volume (Ioi 0) (mvnFutureLp H hH0 t) z.2) (N 0) ∧
          ItoCovarianceFormula P B.F (fun r ω => Y (halfTimeReal r) ω)
            (fun z => L2Restriction volume (Ioi 0) (mvnPastLp H hH0 hH1 t) z.2) (N 1) ∧
          Z t =ᵐ[P] (fun ω => mvnNormalization H * (N 0 ⊤ ω + N 1 ⊤ ω)) ∧
          (∀ i, Tendsto (fun r => eLpNorm (N i r - N i ⊤) 2 P)
            (𝓝[<] (⊤ : HalfClosedTime)) (𝓝 0))) := by
  intro B
  obtain ⟨I, hactual⟩ := independent_wiener_two_ito_integrals P B
  obtain ⟨Z,hmZ,hcZ,hZI,hG,hmean,hcov,hHolder⟩ := Asakura.mandelbrot_van_ness P I H hH0 hH1
  refine ⟨Z,hmZ,hcZ,hG,hmean,hcov,hHolder,mvn_normalization_positive H hH0,?_⟩
  intro t
  obtain ⟨N,hN,hN0,hN1,hsum,hlim⟩ := hactual (mvnFutureLp H hH0 t) (mvnPastLp H hH0 hH1 t)
  refine ⟨N,hN,hN0,hN1,?_,hlim⟩
  apply (hZI t).trans
  unfold mvnProcessLp
  rw [hsum]
  filter_upwards [Lp.coeFn_smul (mvnNormalization H)
      (((hN 0).moment ⊤).toLp (N 0 ⊤) + ((hN 1).moment ⊤).toLp (N 1 ⊤)),
    Lp.coeFn_add (((hN 0).moment ⊤).toLp (N 0 ⊤)) (((hN 1).moment ⊤).toLp (N 1 ⊤)),
    ((hN 0).moment ⊤).coeFn_toLp, ((hN 1).moment ⊤).coeFn_toLp] with ω hs ha h0 h1
  simpa only [Pi.smul_apply,smul_eq_mul,Pi.add_apply,ha,h0,h1] using hs

end Asakura.EndToEnd

#print axioms Asakura.EndToEnd.mandelbrot_van_ness_from_independent_brownian
