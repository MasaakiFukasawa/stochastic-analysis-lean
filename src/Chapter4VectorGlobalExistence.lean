import Chapter4VectorSDERestriction
import Chapter4VectorGluing
import Chapter4VectorRealPath

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter4.Vector
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete
set_option maxHeartbeats 6000000
set_option backward.isDefEq.respectTransparency false

/-- Vector SDE existence on the whole preterminal time domain, obtained
by compatible finite-horizon solutions. The global Ito integral is newly
constructed and identified with each finite-horizon integral. -/
theorem vector_sde_global_exists
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0≤T)] (hT : 0<T) {dim noise : ℕ}
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t E,MeasurableSet[m] E → P E=0 → MeasurableSet[F t] E)
    (W C : Fin noise → ClosedTime T → Ω → ℝ)
    (hW : ∀ j,LocalMProcessWitness P F (W j))
    (hC : ∀ j,LocalCovarianceWitness P F (W j) (W j) (C j))
    (hclock : ∀ j w (r : ℝ),0≤r → (r:EReal)<T → C j (realTimeClamp r) w=r)
    (L : ℝ) (hL : 0≤L)
    (μ : Fin dim → (Fin dim → ℝ) → ℝ) (σ : Fin dim → Fin noise → (Fin dim → ℝ) → ℝ)
    (hμ : ∀ i,Continuous (μ i)) (hσ : ∀ i j,Continuous (σ i j))
    (hμLip : ∀ i x y,(μ i x-μ i y)^2≤L*‖x-y‖^2)
    (hσLip : ∀ i j x y,(σ i j x-σ i j y)^2≤L*‖x-y‖^2)
    (ξ : Ω → Fin dim → ℝ) (hξ : Measurable[F ⊥] ξ) (hξi : MemLp ξ 2 P)
    : ∃ (X : ClosedTime T → Ω → Fin dim → ℝ)
        (N : Fin dim → Fin noise → ClosedTime T → Ω → ℝ),
      (∀ t,t<⊤ → Measurable[F t] (X t)) ∧
      (∀ w t,t<⊤ → ContinuousAt (fun s => X s w) t) ∧
      (∀ i j,LocalMProcessWitness P F (N i j)) ∧
      (∀ i j,ItoCovarianceFormula P F (W j) (fun z => σ i j (X (realTimeClamp z.2) z.1)) (N i j)) ∧
      (∀ R : ℝ,0≤R → (R:EReal)<T → ∃ V : Ω → C(Icc (0:ℝ) R,Fin dim → ℝ),
        MemLp V 2 P ∧ ∀ w r,V w r=X (realTimeClamp r.val) w) ∧
      ∀ᵐ w ∂P,∀ r : ℝ,0≤r → (r:EReal)<T → ∀ i,
        X (realTimeClamp r) w i=ξ w i+(∫ s in 0..r,μ i (X (realTimeClamp s) w))+∑ j,N i j (realTimeClamp r) w := by
  classical
  letI : MeasurableSpace Ω := m
  obtain ⟨c,hc,hcm,hcT,hct,hcut,hcc⟩ := positive_real_time_exhaustion hT
  have hex n := vector_sde_finite_exists P hT F hF hle hnull W C hW hC hclock
    (c n) (hc n).le (hcT n) L hL μ σ hμ hσ hμLip hσLip ξ hξ hξi
  choose Y Z hm hi ha hZ hZI hrep using hex
  have hcompat n k (hnk : n≤k) : Y n=ᵐ[P] fun w => restrictRealPath (hcm.monotone hnk) (Y k w) := by
    obtain ⟨N,hN,hNI,hNr⟩ := finite_sde_restriction P hT F hF hle hnull W C hW hC hclock
      (c k) (hc k).le (hcT k) μ σ hσ ξ (Y k) (ha k) (Z k) (hZ k) (hZI k) (hrep k)
      (c n) (hc n).le (hcm.monotone hnk)
    exact vector_sde_finite_unique_L2 P hT F hF hle hnull W C hW hC hclock
      (c n) (hc n).le (hcT n) L hL μ σ hμ hσ hμLip hσLip ξ (Y n)
      (fun w => restrictRealPath (hcm.monotone hnk) (Y k w)) (hm n)
      (restrict_real_path_measurable (hcm.monotone hnk) (Y k) (hm k))
      (hi n) (restrict_real_path_memLp P (hcm.monotone hnk) (Y k) (hm k) (hi k))
      (ha n) (fun r => ha k ⟨r.val,r.property.1,r.property.2.trans (hcm.monotone hnk)⟩)
      (Z n) N (hZ n) hN (hZI n) hNI (hrep n) hNr
  let A := fun n t w => Y n w (finitePrefixTime (T := T) (c n) (hc n).le t)
  have hA n := finite_path_lift_regular F hF (c n) (hc n).le (hcT n).le (Y n) (ha n)
  have hpair n k : ∀ᵐ w ∂P,∀ hnk : n≤k,Y n w=restrictRealPath (hcm.monotone hnk) (Y k w) := by
    by_cases hnk : n≤k
    · exact (hcompat n k hnk).mono (fun w hw _ => hw)
    · exact .of_forall (fun _ h => (hnk h).elim)
  have hall : ∀ᵐ w ∂P,∀ n k,n≤k → ∀ t,A k (min (realTimeClamp (c n)) t) w=A n t w := by
    filter_upwards [ae_all_iff.mpr (fun n => ae_all_iff.mpr (hpair n))] with w hw
    intro n k hnk t
    dsimp only [A]
    rw [hw n k hnk]
    dsimp only [restrictRealPath,ContinuousMap.coe_mk]
    congr 1
    apply Subtype.ext
    exact finite_prefix_time_stop (c n) (c k) (hc n).le (hcm.monotone hnk) (hcT n).le t
  obtain ⟨X,hXm,hXc,hXp⟩ := continuous_adapted_pieces_glue P F hnull
    (fun n _ => realTimeClamp (c n)) (fun _ => hct.monotone) (fun n _ => hcut n)
    (fun _ => hcc) A (fun n => (hA n).1) (fun n => (hA n).2) hall
  have hreg i j := open_process_real_regularity F (fun t w => σ i j (X t w))
    (fun t ht => (hσ i j).measurable.comp (hXm t ht))
    (fun w t ht => (hσ i j).continuousAt.comp (hXc w t ht))
  have hexN i j := continuous_adapted_ito_exists P hT F hF hle hnull (W j) (hW j)
    (fun z => σ i j (X (realTimeClamp z.2) z.1)) (hreg i j).1 (hreg i j).2
  choose N hN hNI using hexN
  have hsame n : ∀ᵐ w ∂P,∀ r,r∈Icc 0 (c n) →
      X (realTimeClamp r) w=Y n w (projIcc 0 (c n) (hc n).le r) := by
    filter_upwards [hXp] with w hw
    intro r hr
    have h := hw n (realTimeClamp r)
    rw [min_eq_right (real_time_clamp_mono hr.2)] at h
    dsimp only [A] at h
    rw [finite_path_lift_real (c n) (hc n).le (hcT n).le (Y n) w r hr] at h
    exact h
  have hnoise n i j : ∀ᵐ w ∂P,∀ r,r∈Icc 0 (c n) → N i j (realTimeClamp r) w=Z n i j (realTimeClamp r) w := by
    apply brownian_ito_prefix_congr P hT F hF hle hnull (W j) (C j) (hW j) (hC j) (hclock j)
      (fun t w => σ i j (X t w)) (fun t w => σ i j (A n t w)) (N i j) (Z n i j)
      (fun t ht => (hσ i j).measurable.comp (hXm t ht)) (fun t _ => (hσ i j).measurable.comp ((hA n).1 t))
      (fun w t ht => (hσ i j).continuousAt.comp (hXc w t ht)) (fun w t _ => ((hσ i j).comp ((hA n).2 w)).continuousAt)
      (hN i j) (hZ n i j) (hNI i j) (hZI n i j) (c n) (hc n).le (hcT n)
    filter_upwards [hsame n] with w hw
    intro r hr
    dsimp only [A]
    rw [hw r hr,finite_path_lift_real (c n) (hc n).le (hcT n).le (Y n) w r hr]
  have hmoment (R : ℝ) (hR : 0≤R) (hRT : (R:EReal)<T) :
      ∃ V : Ω → C(Icc (0:ℝ) R,Fin dim → ℝ),MemLp V 2 P ∧ ∀ w r,V w r=X (realTimeClamp r.val) w := by
    obtain ⟨n,hnr⟩ := hcc (realTimeClamp R) (real_time_below R hR hRT)
    have hRn : R≤c n := by
      change (realTimeClamp R:EReal)<(realTimeClamp (c n):EReal) at hnr
      rw [real_time_clamp_eq R hR hRT.le,real_time_clamp_eq (c n) (hc n).le (hcT n).le] at hnr
      exact EReal.coe_le_coe_iff.mp hnr.le
    refine ⟨realVectorPath X hXc R hRT,?_,fun _ _ => rfl⟩
    apply real_vector_path_memLp_of_agreement P X hXc (c n) R hR hRn hRT (Y n) (hm n) (hi n)
    exact (hsame n).mono (fun w hw r hr => hw r ⟨hr.1,hr.2.trans hRn⟩)
  refine ⟨X,N,hXm,hXc,hN,hNI,hmoment,?_⟩
  filter_upwards [ae_all_iff.mpr hsame,ae_all_iff.mpr (fun n => ae_all_iff.mpr (fun i => ae_all_iff.mpr (hnoise n i))),ae_all_iff.mpr hrep] with w hs hn hr
  intro r hr0 hrT i
  obtain ⟨n,hnr⟩ := hcc (realTimeClamp r) (real_time_below r hr0 hrT)
  have hrn : r≤c n := by
    change (realTimeClamp r:EReal)<(realTimeClamp (c n):EReal) at hnr
    rw [real_time_clamp_eq r hr0 hrT.le,real_time_clamp_eq (c n) (hc n).le (hcT n).le] at hnr
    exact EReal.coe_le_coe_iff.mp hnr.le
  have h := hr n ⟨r,hr0,hrn⟩ i
  have hint : (∫ s in 0..r,μ i (X (realTimeClamp s) w))=
      ∫ s in 0..r,μ i (Y n w (projIcc 0 (c n) (hc n).le s)) := by
    apply intervalIntegral.integral_congr
    intro s hs'
    have hsr : s∈Icc 0 (c n) := Icc_subset_Icc_right hrn (by simpa [uIcc_of_le hr0] using hs')
    dsimp only
    rw [hs n s hsr]
  rw [hs n r ⟨hr0,hrn⟩,hint,projIcc_of_mem _ ⟨hr0,hrn⟩]
  simp_rw [fun j => hn n i j r ⟨hr0,hrn⟩]
  exact h

end Asakura.Chapter4.Vector
