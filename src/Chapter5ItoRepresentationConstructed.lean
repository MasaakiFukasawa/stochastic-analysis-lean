import Chapter5ItoRepresentationDense

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter5
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 4800000
set_option backward.isDefEq.respectTransparency false

/-- Ito representation assembled from the actual Brownian integrals,
compact smooth approximation, finite Gaussian recursion and closed range.
No smooth representation or abstract integration operator is an input. -/
theorem brownian_ito_representation_constructed
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
    let V := progressiveEnergyRange F c (P.prod (volume.restrict (Ioi 0)))
    let K := Σ _ : Fin (n+1),{r : ℝ // 0≤r ∧ (r:EReal)<T}
    ∃ I : Fin (n+1) → V →ₗᵢ[ℝ] Lp ℝ 2 P,
    ∃ L : PiLp 2 (fun _ : Fin (n+1) => V) →ₗᵢ[ℝ] Lp ℝ 2 P,
      (∀ x,L x=∑ i,I i (x i)) ∧
      (∀ i,∀ H : progressiveEnergyIntegrands F c (P.prod (volume.restrict (Ioi 0))),
        ∃ M : ClosedTime T → Ω → ℝ,∃ hM : ContinuousM2Witness P F M,
          ItoCovarianceFormula P F (W i) H.val M ∧
          I i ⟨progressiveEnergyToLp F c _ H,LinearMap.mem_range_self _ H⟩=(hM.moment ⊤).toLp (M ⊤)) ∧
      ∀ U : Lp ℝ 2 P,
        AEStronglyMeasurable[MeasurableSpace.comap
          (fun w (t : K) => W t.1 (realTimeClamp t.2.val) w) inferInstance] U P →
        ∃! x,L x=U-(condExpL2 ℝ ℝ bot_le U : Lp ℝ 2 P) := by
  classical
  dsimp only
  have hA i : LocalCovarianceWitness P F (W i) (W i) A := by
    simpa only [ite_true] using hC i i
  have hcross i j (hij : i≠j) : LocalCovarianceWitness P F (W i) (W j) (fun _ _ => 0) := by
    simpa only [hij,ite_false] using hC i j
  obtain ⟨I,L,hL,hI⟩ := multidimensional_brownian_isometry_constructed P hT F hF hle hnull (n+1) W A hW hA hcross
    c hc hcm hcT hct hcut hcc
    (fun j w r hr => hclock w r hr.1 ((EReal.coe_le_coe hr.2).trans_lt (hcT j))) hco
  refine ⟨I,L,hL,hI,?_⟩
  let K := Σ _ : Fin (n+1),{r : ℝ // 0≤r ∧ (r:EReal)<T}
  let X : K → Ω → ℝ := fun t w => W t.1 (realTimeClamp t.2.val) w
  have ht (r : {r : ℝ // 0≤r ∧ (r:EReal)<T}) : realTimeClamp (T := T) r.val<⊤ := by
    change (realTimeClamp r.val:EReal)<T
    rw [real_time_clamp_eq r.val r.property.1 r.property.2.le]
    exact r.property.2
  have hXm t : Measurable (X t) := ((hW t.1).adapted P F _ (ht t.2)).mono (hle _) le_rfl
  have hXc w : Continuous (fun t : K => X t w) := by
    apply continuous_sigma
    intro i
    apply continuous_iff_continuousAt.mpr
    intro r
    have hm : Continuous (fun r : {r : ℝ // 0≤r ∧ (r:EReal)<T} => realTimeClamp (T := T) r.val) :=
      real_time_clamp_continuous.comp continuous_subtype_val
    have hh := ((hW i).path P F w _ (ht r)).tendsto.comp (hm.tendsto r)
    simpa only [ContinuousAt,X,Function.comp_def] using hh
  letI : Nonempty K := ⟨⟨0,⟨0,le_rfl,by simpa using hT⟩⟩⟩
  obtain ⟨q,hq⟩ := TopologicalSpace.exists_dense_seq K
  intro U hU
  exact ito_representation_continuous_observations P hT F hF hle hnull W A hW hC hclock
    c (fun j => (hc j).le) hcm.monotone hcT hcc (fun t : K => t.1) (fun t : K => t.2.val)
    (fun t => t.2.property.1) (fun t => t.2.property.2) hXm hXc q hq I L hL hI U hU

end Asakura.Chapter5
