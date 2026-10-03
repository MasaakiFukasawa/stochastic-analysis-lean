import Chapter5FiniteGridRepresentation
import Chapter5MultidimensionalIsometry

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter5
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 3200000
set_option backward.isDefEq.respectTransparency false

/-- The observation integrals are identified with the already constructed
isometry by actual M² covariance uniqueness, including the terminal value. -/
theorem observation_integral_isometry_realization
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0≤T)] (hT : 0<T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t N,MeasurableSet[m] N → P N=0 → MeasurableSet[F t] N)
    {d k : ℕ} (W : Fin d → ClosedTime T → Ω → ℝ)
    (hW : ∀ i,LocalMProcessWitness P F (W i)) (index : Fin k → Fin d)
    (c : ℕ → ℝ) (hc : ∀ j,0≤c j) (hcT : ∀ j,(c j:EReal)<T)
    (J : ObservationIntegralData P F W index)
    (I : Fin d → progressiveEnergyRange F c (P.prod (volume.restrict (Ioi 0))) →ₗᵢ[ℝ] Lp ℝ 2 P)
    (L : PiLp 2 (fun _ : Fin d => progressiveEnergyRange F c (P.prod (volume.restrict (Ioi 0)))) →ₗᵢ[ℝ] Lp ℝ 2 P)
    (hL : ∀ x,L x=∑ i,I i (x i))
    (hI : ∀ i,∀ H : progressiveEnergyIntegrands F c (P.prod (volume.restrict (Ioi 0))),
      ∃ M : ClosedTime T → Ω → ℝ,∃ hM : ContinuousM2Witness P F M,
        ItoCovarianceFormula P F (W i) H.val M ∧
        I i ⟨progressiveEnergyToLp F c _ H,LinearMap.mem_range_self _ H⟩=(hM.moment ⊤).toLp (M ⊤)) :
    ∀ i,∃ x,L x=(J.martingale i |>.moment ⊤).toLp (J.integral i ⊤) := by
  classical
  intro i
  let H : progressiveEnergyIntegrands F c (P.prod (volume.restrict (Ioi 0))) :=
    ⟨J.integrand i,⟨(J.energy i).1,(fun j => J.progressive i (c j) (hc j) (hcT j)),(J.energy i).2⟩⟩
  let x : progressiveEnergyRange F c (P.prod (volume.restrict (Ioi 0))) :=
    ⟨progressiveEnergyToLp F c _ H,LinearMap.mem_range_self _ H⟩
  obtain ⟨M,hM,hMI,he⟩ := hI (index i) H
  have huniq := ito_m2_covariance_unique P hT F hF hle hnull (W (index i)) M (J.integral i)
    H.val (hW (index i)) hM (J.martingale i) hMI (J.formula i)
  have hterm : M ⊤ =ᵐ[P] J.integral i ⊤ := huniq.mono (fun _ hh => hh ⊤)
  have heLp : (hM.moment ⊤).toLp (M ⊤)=(J.martingale i |>.moment ⊤).toLp (J.integral i ⊤) :=
    MemLp.toLp_eq_toLp_iff _ _ |>.mpr hterm
  refine ⟨PiLp.single 2 (index i) x,?_⟩
  rw [hL,Finset.sum_eq_single (index i)]
  · simpa only [PiLp.single_eq_same] using he.trans heLp
  · intro j _ hji
    simp only [PiLp.single_eq_of_ne _ hji,map_zero]
  · simp

end Asakura.Chapter5
