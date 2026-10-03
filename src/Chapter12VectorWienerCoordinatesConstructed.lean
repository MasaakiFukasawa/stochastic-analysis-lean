import Chapter12RawDeterministicEnergy
import Chapter12PiIsometry
import Chapter12WienerItoConstruction
import Chapter5MultidimensionalIsometry

open MeasureTheory Set
open scoped ENNReal
namespace Asakura.Chapter12
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter4 Asakura.Chapter5
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

/-- The vector Wiener integral is the sum of the actual coordinate Ito
integrals. Its isometry uses the zero cross brackets of Brownian coordinates. -/
theorem vector_wiener_coordinate_isometries {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (B : BrownianSystem P (d+1))
    (c : ℕ → ℝ) (hc : ∀ n, 0 < c n) (hcm : StrictMono c)
    (hct : StrictMono (fun n => realTimeClamp (T := ⊤) (c n)))
    (hcut : ∀ n, realTimeClamp (T := ⊤) (c n) < ⊤)
    (hcc : ∀ t : HalfClosedTime, t < ⊤ → ∃ n, t < realTimeClamp (c n))
    (hco : ∀ r : ℝ, ∃ n, r ≤ c n) :
    ∃ J : Fin (d+1) → Lp ℝ 2 (volume.restrict (Ioi (0:ℝ))) →ₗᵢ[ℝ] Lp ℝ 2 P,
    ∃ W : PiLp 2 (fun _ : Fin (d+1) => Lp ℝ 2 (volume.restrict (Ioi (0:ℝ)))) →ₗᵢ[ℝ] Lp ℝ 2 P,
      (∀ f, W f = ∑ i,J i (f i)) ∧
      ∀ i (f : ℝ → ℝ) (hm : Measurable f) (hi : MemLp f 2 (volume.restrict (Ioi (0:ℝ)))),
        ∃ N : HalfClosedTime → Ω → ℝ, ∃ hN : ContinuousM2Witness P B.F N,
          ItoCovarianceFormula P B.F (B.W i) (fun z => f z.2) N ∧
          J i (hi.toLp f) = (hN.moment ⊤).toLp (N ⊤) := by
  classical
  have hdiag i : LocalCovarianceWitness P B.F (B.W i) (B.W i) (B.C 0 0) := by
    apply (B.cov i i).congr_values_before_terminal P B.F
    intro t ht
    obtain ⟨r,hr,_,he⟩ := finite_closed_time_real t ht
    rw [← he]
    funext w
    rw [B.diagonal_clock i w r hr,B.diagonal_clock 0 w r hr]
  have hcross i j (hij : i ≠ j) :
      LocalCovarianceWitness P B.F (B.W i) (B.W j) (fun _ _ => 0) := by
    apply (B.cov i j).congr_values_before_terminal P B.F
    intro t ht
    obtain ⟨r,hr,_,he⟩ := finite_closed_time_real t ht
    rw [← he]
    funext w
    simpa only [if_neg hij] using B.clock i j w r hr
  obtain ⟨I,L,hL,hI⟩ := multidimensional_brownian_isometry_constructed P
    (by simp : (0:EReal)<⊤) B.F B.mono B.le B.null (d+1) B.W (B.C 0 0)
    B.martingale hdiag hcross c hc hcm (fun _ => EReal.coe_lt_top _) hct hcut hcc
    (fun _ w r hr => B.diagonal_clock 0 w r hr.1) hco
  let J := fun i => (I i).comp (deterministicEnergyEmbedding P B.F c)
  let V := finitePiIsometry (ι := Fin (d+1)) (deterministicEnergyEmbedding P B.F c)
  refine ⟨J,L.comp V,fun f => ?_,fun i f hm hi => ?_⟩
  · exact hL (V f)
  · obtain ⟨N,hN,hNI,he⟩ := hI i (rawDeterministicEnergyIntegrand P B.F c f hm hi)
    refine ⟨N,hN,hNI,?_⟩
    change I i (deterministicEnergyEmbedding P B.F c (hi.toLp f)) = _
    rw [raw_deterministic_energy_realization]
    exact he

end Asakura.Chapter12
