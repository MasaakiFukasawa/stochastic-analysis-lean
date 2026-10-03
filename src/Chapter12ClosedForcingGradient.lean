import Chapter12ForcingGradientLpLimit
import Chapter12MalliavinC1Chain

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ContDiff ENNReal
namespace Asakura.Chapter12
set_option maxHeartbeats 3200000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] forcingGradient

theorem closed_forcing_gradient {Ω H E K:Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [Nontrivial H]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace K] [CompactSpace K]
    (P:Measure Ω) [IsProbabilityMeasure P] (W:H →ₗᵢ[ℝ] Lp ℝ 2 P)
    (S₀:Set H) (hS₀:Dense S₀)
    (hcore:∀u∈S₀,HasLaw (W u:Ω → ℝ) (gaussianReal 0 ⟨‖u‖^2,sq_nonneg _⟩) P)
    (D:Lp ℝ 2 P →ₗ.[ℝ] Lp H 2 P) (hD:D.IsClosed)
    (hg:(D.graph:Set _)=closure (range (cylinderPair P W S₀ hS₀ hcore 2 (by simp))))
    (S:C(K,E) → C(K,E)) (hS:ContDiff ℝ ∞ S)
    (C:ℝ) (hC:0≤C) (hb:∀a,‖fderiv ℝ S a‖≤C)
    (ell:E →L[ℝ] ℝ) (t:K) (a₀:C(K,E))
    (N:ℕ → ℕ) (e:∀n,Fin (N n) → H) (L:∀n,(Fin (N n) → ℝ) →L[ℝ] C(K,E))
    (R:ℕ → H →L[ℝ] C(K,E)) (Q:H →L[ℝ] C(K,E))
    (hfact:∀n,R n=(L n).comp (hilbertCoordinates (e n))) (hR:Tendsto R atTop (𝓝 Q))
    (a:Ω → C(K,E)) (ham:AEStronglyMeasurable a P)
    (ha:∀ᵐw∂P,Tendsto (fun n => a₀+L n (fun j => W (e n j) w)) atTop (𝓝 (a w)))
    (f:∀n,GaussianJet (N n)) (hf:∀n,(f n).f=fun z => ell (S (a₀+L n z) t))
    (F:Lp ℝ 2 P)
    (hF:Tendsto (fun n => ((f n).toCylinder (e n)).valueLp P W S₀ hS₀ hcore 2 (by simp)) atTop (𝓝 F)) :
    ∃hU:MemLp (fun w => forcingGradient S (a w) Q ell t) 2 P,
      (F,hU.toLp _)∈D.graph := by
  let b := fun n w => a₀+L n (fun j => W (e n j) w)
  have hbm n:AEStronglyMeasurable (b n) P :=
    (continuous_const.add (L n).continuous).comp_aestronglyMeasurable
      (measurable_pi_lambda (fun j => (Lp.stronglyMeasurable (W (e n j))).measurable)).aestronglyMeasurable
  obtain ⟨hm,hU,hlim⟩ := forcing_gradient_Lp_limit P 2 (by simp) S hS C hC hb ell t b a hbm ham ha R Q hR
  have he n:((f n).toCylinder (e n)).gradientLp P W S₀ hS₀ hcore 2 (by simp)=(hm n).toLp _ := by
    apply Lp.ext
    filter_upwards [((f n).toCylinder (e n)).gradient_memLp P W S₀ hS₀ hcore 2 (by simp) |>.coeFn_toLp,
      (hm n).coeFn_toLp] with w hw hv
    rw [hv]
    exact hw.trans (gaussian_forcing_gradient P W S hS a₀ (e n) (L n) (R n) (hfact n) ell t (f n) (hf n) w)
  refine ⟨hU,?_⟩
  apply hD.mem_of_tendsto (hF.prodMk_nhds hlim)
  apply Eventually.of_forall
  intro n
  rw [←he n]
  change cylinderPair P W S₀ hS₀ hcore 2 (by simp) ((f n).toCylinder (e n))∈(D.graph:Set _)
  rw [hg]
  exact subset_closure (mem_range_self _)
end Asakura.Chapter12
#print axioms Asakura.Chapter12.closed_forcing_gradient
