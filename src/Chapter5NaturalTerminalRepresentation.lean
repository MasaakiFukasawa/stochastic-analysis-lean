import Chapter5FrozenBrownianBSDE

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter5
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 4800000
set_option backward.isDefEq.respectTransparency false

/-- Actual representation of an arbitrary square-integrable variable
measurable at the finite terminal time in the completed Brownian filtration. -/
theorem natural_terminal_brownian_representation
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0≤T)] (hT : 0<T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t N,MeasurableSet[m] N → P N=0 → MeasurableSet[F t] N)
    (W A : ClosedTime T → Ω → ℝ)
    (hW : LocalMProcessWitness P F W)
    (hA : LocalCovarianceWitness P F W W A)
    (hclock : ∀ w (r : ℝ),0≤r → (r:EReal)<T → A (realTimeClamp r) w=r)
    (c : ℕ → ℝ) (hc : ∀ j,0<c j) (hcm : StrictMono c) (hcT : ∀ j,(c j:EReal)<T)
    (hct : StrictMono (fun j => realTimeClamp (T := T) (c j)))
    (hcut : ∀ j,realTimeClamp (T := T) (c j)<⊤)
    (hcc : ∀ t,t<⊤ → ∃ j,t<realTimeClamp (T := T) (c j))
    (hco : ∀ r,∃ j,r≤c j)
    (R : ℝ) (hR : 0≤R) (hRT : (R:EReal)<T)
    (hFnat : F (realTimeClamp R)=Asakura.nullAugmentation (m := m) P (pastSigma W (realTimeClamp R)))
    (U : Ω → ℝ) (hU : MemLp U 2 P) (hUm : Measurable[F (realTimeClamp R)] U) :
    ∃ G : Ω × ℝ → ℝ,∃ M : ClosedTime T → Ω → ℝ,
      ContinuousM2Witness P F M ∧ ItoCovarianceFormula P F W G M ∧ Measurable G ∧
      MemLp G 2 (P.prod (volume.restrict (Ioi 0))) ∧
      (∀ j,@Measurable _ _ (progressiveSpace (fun t : Icc (0:ℝ) (c j) => F (realTimeClamp t.val))) inferInstance
        (fun z : Ω × Icc (0:ℝ) (c j) => G (z.1,z.2.val))) ∧
      (U =ᵐ[P] fun w => (∫ w,U w ∂P)+M ⊤ w) := by
  have hRt : realTimeClamp (T := T) R<⊤ := by
    change (realTimeClamp R:EReal)<T
    rw [real_time_clamp_eq R hR hRT.le]
    exact hRT
  have hUg := (natural_observation_aestronglyMeasurable P F W (realTimeClamp R) hRt hFnat U hUm).congr hU.coeFn_toLp.symm
  have hCs (i j : Fin 1) : LocalCovarianceWitness P F W W (fun t w => if i=j then A t w else 0) := by
    have he : i=j := Subsingleton.elim _ _
    simpa only [he,ite_true] using hA
  obtain ⟨H,M,hM,hMI,he⟩ := brownian_ito_representation_actual P hT F hF hle hnull (fun _ : Fin 1 => W) A
    (fun _ => hW) hCs hclock c hc hcm hcT hct hcut hcc hco (hU.toLp U) hUg
  have hmean : (∫ w,(hU.toLp U) w ∂P)=∫ w,U w ∂P := integral_congr_ae hU.coeFn_toLp
  refine ⟨(H 0).val,M 0,hM 0,hMI 0,(H 0).property.1,(H 0).property.2.2,(H 0).property.2.1,?_⟩
  filter_upwards [he,hU.coeFn_toLp] with w hw huw
  simpa only [huw,hmean,Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero] using hw

end Asakura.Chapter5
