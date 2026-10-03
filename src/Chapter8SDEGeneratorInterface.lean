import Chapter8SDETimeDerivative
import Chapter8SDERightGenerator
import Chapter4BrownianSystem
import Chapter4ClassicalSolutionData

open MeasureTheory Set Filter
open scoped BigOperators Topology
namespace Asakura.Chapter8
open Asakura.Chapter4 Asakura.Chapter3Complete Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 1800000

noncomputable def coordinateGenerator {d n : ℕ}
    (b : Fin d → (Fin d → ℝ) → ℝ) (σ : Fin d → Fin n → (Fin d → ℝ) → ℝ)
    (f : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) : ℝ :=
  (∑ i,fderiv ℝ f x (Pi.single i 1)*b i x)+
    (∑ i,∑ j,fderiv ℝ (fderiv ℝ f) x (Pi.single i 1) (Pi.single j 1)*
      (∑ k,σ i k x*σ j k x))/2

theorem coordinate_generator_continuous {d n : ℕ}
    (b : Fin d → (Fin d → ℝ) → ℝ) (σ : Fin d → Fin n → (Fin d → ℝ) → ℝ)
    (hb : ∀ i, Continuous (b i)) (hs : ∀ i j, Continuous (σ i j))
    (f : (Fin d → ℝ) → ℝ) (hf : ContDiff ℝ 2 f) :
    Continuous (coordinateGenerator b σ f) := by
  have h1 := hf.continuous_fderiv (by norm_num)
  have hf1 : ContDiff ℝ 1 (fderiv ℝ f) := (contDiff_succ_iff_fderiv (n := 1)).mp hf |>.2.2
  have h2 := hf1.continuous_fderiv (by norm_num)
  unfold coordinateGenerator
  fun_prop

/-- A short interface to the derived generator formulas, using the
existing Chapter 4 structures for an actual Brownian-driven solution. -/
theorem sde_generator_formulas {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d n : ℕ}
    (B : BrownianSystem P n)
    (b : Fin d → (Fin d → ℝ) → ℝ) (σ : Fin d → Fin n → (Fin d → ℝ) → ℝ)
    (L : ℝ) (hL : 0≤L)
    (hLip : ∀ x y,(∑ i,(b i x-b i y)^2)+(∑ i,∑ j,(σ i j x-σ i j y)^2)≤L*∑ i,(x i-y i)^2)
    (x : Fin d → ℝ) (X : HalfClosedTime → Ω → Fin d → ℝ)
    (hX : VectorSDESolution P B.F B.W b σ (fun _ => x) X)
    (f : (Fin d → ℝ) → ℝ) (hf : ContDiff ℝ 2 f)
    (hc : Continuous (coordinateGenerator b σ f))
    (deg : ℕ) (C : ℝ) (hC : 0≤C)
    (hb : ∀ y,|f y|≤C*(1+(Real.sqrt (∑ i,y i^2))^deg))
    (hg : ∀ y,|coordinateGenerator b σ f y|≤C*(1+(Real.sqrt (∑ i,y i^2))^deg)) :
    HasDerivWithinAt (fun r => ∫ w,f (X (realTimeClamp r) w) ∂P)
      (coordinateGenerator b σ f x) (Ici 0) 0 ∧
    (∀ t,0<t → HasDerivAt (fun r => ∫ w,f (X (realTimeClamp r) w) ∂P)
      (∫ w,coordinateGenerator b σ f (X (realTimeClamp t) w) ∂P) t) := by
  obtain ⟨N,hN,hNI,he⟩ := hX.integrals
  constructor
  · exact sde_right_generator P (by simp) rfl B.F B.mono B.le B.null B.W B.C
      B.martingale B.cov (fun j k w r hr _ => B.clock j k w r hr)
      X x hX.adapted hX.path b σ L hL hLip N hN hNI he f (coordinateGenerator b σ f)
      hf hc (fun _ => rfl) deg C hC hb hg
  · intro t ht
    exact sde_transition_time_derivative P (by simp) rfl B.F B.mono B.le B.null B.W B.C
      B.martingale B.cov (fun j k w r hr _ => B.clock j k w r hr)
      X x hX.adapted hX.path b σ L hL hLip N hN hNI t ht (EReal.coe_lt_top t)
      he f (coordinateGenerator b σ f) hf hc (fun _ => rfl) deg C hC hb hg

end Asakura.Chapter8
