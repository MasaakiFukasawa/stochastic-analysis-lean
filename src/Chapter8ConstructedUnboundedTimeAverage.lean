import Chapter8ActualUnboundedTimeAverage
import Chapter8ProductInvariantTests
import Chapter8ProductProbability
import Chapter8ActualSynchronousContraction
import Chapter8InformationErgodicTransfer
import Chapter8SecondMomentL1

open MeasureTheory Set Filter
open scoped NNReal BigOperators RealInnerProductSpace Topology
namespace Asakura.Chapter8
open Asakura.FullAudit Asakura.Chapter4 Asakura.Chapter3Complete
open Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

/-- The cutoff and common-noise argument for the information limit is
applied to actual SDEs, with stationarity, contraction and bounded-observable
convergence all derived rather than assumed. -/
theorem constructed_unbounded_time_average {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (P : Measure Ω) [IsProbabilityMeasure P] {d n : ℕ} (B : BrownianSystem P n)
    (e : (Fin d → ℝ) ≃L[ℝ] E) (g : (Fin d → ℝ) → (Fin d → ℝ)) (Kg : ℝ≥0) (hg : LipschitzWith Kg g)
    (σ : Fin d → Fin n → ℝ) (L : ℝ) (hL : 0≤L)
    (hLip : ∀ x y,(∑ i,(-(g x i)- -(g y i))^2)+
      (∑ i : Fin d,∑ j : Fin n,(σ i j-σ i j)^2)≤L*∑ i,(x i-y i)^2)
    (κ : ℝ) (hκ : 0<κ)
    (hmono : ∀ x y,κ*‖e x-e y‖^2≤⟪e x-e y,e (g x)-e (g y)⟫)
    (π : Measure (Fin d → ℝ)) [IsProbabilityMeasure π] (hπ : MemLp (fun x => x) 2 π)
    (Z : (Fin d → ℝ) → HalfClosedTime → Ω → Fin d → ℝ)
    (hZ : ∀ x,VectorSDESolution P B.F B.W (fun i y => -(g y i)) (fun i j _ => σ i j) (fun _ => x) (Z x))
    (hinv : ∀ t : ℝ,0≤t → ∀ f : (Fin d → ℝ) → ℝ,ContDiff ℝ (⊤:ℕ∞) f → HasCompactSupport f →
      (∫ x,(∫ w,f (Z x (realTimeClamp t) w) ∂P) ∂π)=∫ x,f x ∂π)
    (x : Fin d → ℝ) (T : ℕ → ℝ) (hT : ∀ k,0<T k) (hTlim : Tendsto T atTop atTop)
    (f : E → ℝ) (hf : ContDiff ℝ 1 f) (hi : Integrable f (π.map e))
    (C : ℝ) (hC : 0≤C)
    (hfg : ∀ z z',|f z-f z'|≤C*‖z-z'‖*(1+‖z‖+‖z'‖)) :
    TendstoInMeasure P
      (fun k w => timeAverage (fun t => f (e (Z x (realTimeClamp (max 0 t)) w))) (T k))
      atTop (fun _ => ∫ z,f z ∂π.map e) := by
  obtain ⟨B',hW,Y,Z',hY,hZ',_⟩ := independent_initial_sde P B π hπ L hL
    (fun i y => -(g y i)) (fun i j _ => σ i j) hLip
  have hinv' := product_invariant_tests P π B B' hW (fun y => -g y) Kg hg.neg σ Z Z' hZ hZ' π hinv
  have hξ : MemLp (Prod.fst : (Fin d → ℝ) × Ω → Fin d → ℝ) 2 (π.prod P) := hπ.comp_fst P
  have hξlaw : (π.prod P).map Prod.fst=π := by rw [Measure.map_fst_prod,measure_univ,one_smul]
  have hlim := actual_unbounded_time_average (π.prod P) B' e g hg.continuous σ L hL hLip κ hκ hmono
    π hπ Prod.fst hξ hξlaw Y hY Z' hZ' hinv' x T hT hTlim f hf hi C hC hfg
  let A := fun k w => timeAverage (fun t => f (e (Z x (realTimeClamp (max 0 t)) w))) (T k)
  have hm k : Measurable (A k) := by
    obtain ⟨_,hZm,_,_⟩ := sde_real_path_data P B L hL _ _ hLip (fun _ => x) (memLp_const x) (Z x) (hZ x)
    exact time_average_measurable (fun w t => f (e (Z x (realTimeClamp (max 0 t)) w)))
      (hf.continuous.measurable.comp (e.continuous.measurable.comp hZm)) _ (hT k).le
  apply probability_from_product P π A hm atTop (∫ z,f z ∂π.map e)
  apply TendstoInMeasure.congr _ Filter.EventuallyEq.rfl hlim
  intro k
  filter_upwards [product_sde_identification P π B B' hW (fun y => -g y) Kg hg.neg σ x (Z x) (Z' x) (hZ x) (hZ' x)] with z hz
  dsimp only [A,timeAverage]
  congr 1
  apply intervalIntegral.integral_congr
  intro r _
  exact congrArg (fun a => f (e a)) (hz (max 0 r) (le_max_left _ _))
end Asakura.Chapter8
