import Chapter5MultidimensionalEnergy
import Chapter5OrthogonalIsometry

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter5
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4
set_option maxHeartbeats 3600000
set_option backward.isDefEq.respectTransparency false

/-- The actual multi-dimensional Brownian integral is a linear isometry
on the complete finite direct sum of progressive L² spaces. -/
theorem multidimensional_brownian_isometry_constructed
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t E, MeasurableSet[m] E → P E = 0 → MeasurableSet[F t] E)
    (d : ℕ) (W : Fin d → ClosedTime T → Ω → ℝ) (A : ClosedTime T → Ω → ℝ)
    (hW : ∀ i,LocalMProcessWitness P F (W i))
    (hA : ∀ i,LocalCovarianceWitness P F (W i) (W i) A)
    (hcross : ∀ i j,i ≠ j → LocalCovarianceWitness P F (W i) (W j) (fun _ _ => 0))
    (c : ℕ → ℝ) (hc : ∀ n, 0 < c n) (hcm : StrictMono c) (hcT : ∀ n, (c n:EReal) < T)
    (hct : StrictMono (fun n => realTimeClamp (T := T) (c n)))
    (hcut : ∀ n, realTimeClamp (T := T) (c n) < ⊤)
    (hcc : ∀ t, t < ⊤ → ∃ n, t < realTimeClamp (T := T) (c n))
    (hclock : ∀ n w r, r ∈ Icc 0 (c n) → A (realTimeClamp r) w = r)
    (hco : ∀ r,∃ n,r ≤ c n) :
    let V := progressiveEnergyRange F c (P.prod (volume.restrict (Ioi 0)))
    ∃ I : Fin d → V →ₗᵢ[ℝ] Lp ℝ 2 P,∃ L : PiLp 2 (fun _ : Fin d => V) →ₗᵢ[ℝ] Lp ℝ 2 P,
      (∀ x,L x = ∑ i,I i (x i)) ∧
      ∀ i,∀ H : progressiveEnergyIntegrands F c (P.prod (volume.restrict (Ioi 0))),
        ∃ M : ClosedTime T → Ω → ℝ,∃ hM : ContinuousM2Witness P F M,
          ItoCovarianceFormula P F (W i) H.val M ∧
          I i ⟨progressiveEnergyToLp F c _ H,LinearMap.mem_range_self _ H⟩ = (hM.moment ⊤).toLp (M ⊤) := by
  classical
  dsimp only
  let ν := P.prod (volume.restrict (Ioi (0:ℝ)))
  choose I hI using fun i => brownian_L2_isometry_constructed P hT F hF hle hnull
    (W i) A (hW i) (hA i) c hc hcm hcT hct hcut hcc hclock hco
  have ho i j (hij : i ≠ j) (x y : progressiveEnergyRange F c ν) : inner ℝ (I i x) (I j y) = 0 := by
    obtain ⟨H,hHx⟩ := x.property
    obtain ⟨G,hGy⟩ := y.property
    have hx : (⟨progressiveEnergyToLp F c ν H,LinearMap.mem_range_self _ H⟩ : progressiveEnergyRange F c ν) = x := Subtype.ext hHx
    have hy : (⟨progressiveEnergyToLp F c ν G,LinearMap.mem_range_self _ G⟩ : progressiveEnergyRange F c ν) = y := Subtype.ext hGy
    obtain ⟨M,hM,hMI,heM⟩ := hI i H
    obtain ⟨N,hN,hNI,heN⟩ := hI j G
    rw [hx] at heM
    rw [hy] at heN
    rw [heM,heN,terminal_L2_inner]
    exact ito_integrals_terminal_orthogonal P hT F hF hle (W i) (W j) M N
      (hW i) (hW j) hM hN (hcross i j hij) H.val G.val
      (fun _ => H.property.1.comp measurable_prodMk_left) (fun _ => G.property.1.comp measurable_prodMk_left) hMI hNI
  obtain ⟨L,hL⟩ := orthogonal_sum_linear_isometry I ho
  exact ⟨I,L,hL,hI⟩

end Asakura.Chapter5
