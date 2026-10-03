import Chapter5ItoRepresentationConstructed

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter5
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 4800000
set_option backward.isDefEq.respectTransparency false

/-- The representation in the manuscript's concrete form: actual
progressive L² integrands and their actual M² stochastic integrals. -/
theorem brownian_ito_representation_actual
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0≤T)] (hT : 0<T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t N,MeasurableSet[m] N → P N=0 → MeasurableSet[F t] N)
    {n : ℕ} (W : Fin (n+1) → ClosedTime T → Ω → ℝ) (A : ClosedTime T → Ω → ℝ)
    (hW : ∀ i,LocalMProcessWitness P F (W i))
    (hC : ∀ i j,LocalCovarianceWitness P F (W i) (W j) (fun t w => if i=j then A t w else 0))
    (hclock : ∀ w (r : ℝ),0≤r → (r:EReal)<T → A (realTimeClamp r) w=r)
    (c : ℕ → ℝ) (hc : ∀ j,0<c j) (hcm : StrictMono c) (hcT : ∀ j,(c j:EReal)<T)
    (hct : StrictMono (fun j => realTimeClamp (T := T) (c j)))
    (hcut : ∀ j,realTimeClamp (T := T) (c j)<⊤)
    (hcc : ∀ t,t<⊤ → ∃ j,t<realTimeClamp (T := T) (c j))
    (hco : ∀ r,∃ j,r≤c j) :
    let K := Σ _ : Fin (n+1),{r : ℝ // 0≤r ∧ (r:EReal)<T}
    ∀ U : Lp ℝ 2 P,
      AEStronglyMeasurable[MeasurableSpace.comap
        (fun w (t : K) => W t.1 (realTimeClamp t.2.val) w) inferInstance] U P →
      ∃ H : Fin (n+1) → progressiveEnergyIntegrands F c (P.prod (volume.restrict (Ioi 0))),
      ∃ M : Fin (n+1) → ClosedTime T → Ω → ℝ,
        (∀ i,ContinuousM2Witness P F (M i)) ∧
        (∀ i,ItoCovarianceFormula P F (W i) (H i).val (M i)) ∧
        (U : Ω → ℝ) =ᵐ[P] fun w => (∫ z,U z ∂P)+∑ i,M i ⊤ w := by
  classical
  dsimp only
  obtain ⟨I,L,hL,hI,hrep⟩ := brownian_ito_representation_constructed P hT F hF hle hnull W A hW hC hclock
    c hc hcm hcT hct hcut hcc hco
  intro U hU
  obtain ⟨x,hx,_⟩ := hrep U hU
  choose H hH using fun i => (x i).property
  have he i : (⟨progressiveEnergyToLp F c _ (H i),LinearMap.mem_range_self _ (H i)⟩ :
      progressiveEnergyRange F c (P.prod (volume.restrict (Ioi 0))))=x i := Subtype.ext (hH i)
  choose M hM hMI hME using fun i => hI i (H i)
  have hIe i : I i (x i)=(hM i |>.moment ⊤).toLp (M i ⊤) := by
    rw [← he i]
    exact hME i
  have hs : (∑ i,(hM i |>.moment ⊤).toLp (M i ⊤))=
      U-(condExpL2 ℝ ℝ bot_le U : Lp ℝ 2 P) := by
    simpa only [hL,hIe] using hx
  have hcoe := Lp.coeFn_fun_finsetSum Finset.univ (fun i => (hM i |>.moment ⊤).toLp (M i ⊤))
  have hcoei : ∀ᵐ w ∂P,∀ i,((hM i |>.moment ⊤).toLp (M i ⊤)) w=M i ⊤ w :=
    ae_all_iff.mpr (fun i => (hM i |>.moment ⊤).coeFn_toLp)
  rw [hs] at hcoe
  refine ⟨H,M,hM,hMI,?_⟩
  filter_upwards [hcoe,hcoei,centered_L2_is_subtract_expectation P U] with w hsw hiw hcw
  have hh : U w-(∫ z,U z ∂P)=∑ i,M i ⊤ w := by simpa only [hcw,hiw] using hsw
  linarith only [hh]

end Asakura.Chapter5
