import Chapter4FiniteSDERestriction
import Chapter4ContinuousGluing

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter4
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete
set_option maxHeartbeats 6000000
set_option backward.isDefEq.respectTransparency false

/-- Scalar SDE existence on the whole preterminal time domain, obtained
by compatible finite-horizon solutions. The global Ito integral is newly
constructed and identified with each finite-horizon integral. -/
theorem scalar_sde_global_exists
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0≤T)] (hT : 0<T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t E,MeasurableSet[m] E → P E=0 → MeasurableSet[F t] E)
    (W C : ClosedTime T → Ω → ℝ) (hW : LocalMProcessWitness P F W)
    (hC : LocalCovarianceWitness P F W W C)
    (hclock : ∀ w (r : ℝ),0≤r → (r:EReal)<T → C (realTimeClamp r) w=r)
    (L : ℝ) (hL : 0≤L) (μ σ : ℝ → ℝ) (hμ : Continuous μ) (hσ : Continuous σ)
    (hLip : ∀ x y,(μ x-μ y)^2+(σ x-σ y)^2≤L*(x-y)^2)
    (ξ : Ω → ℝ) (hξ : Measurable[F ⊥] ξ) (hξi : MemLp ξ 2 P)
    : ∃ X N : ClosedTime T → Ω → ℝ,
      (∀ t,t<⊤ → Measurable[F t] (X t)) ∧
      (∀ w t,t<⊤ → ContinuousAt (fun s => X s w) t) ∧
      LocalMProcessWitness P F N ∧
      ItoCovarianceFormula P F W (fun z => σ (X (realTimeClamp z.2) z.1)) N ∧
      ∀ᵐ w ∂P,∀ r : ℝ,0≤r → (r:EReal)<T →
        X (realTimeClamp r) w=ξ w+(∫ s in 0..r,μ (X (realTimeClamp s) w))+N (realTimeClamp r) w := by
  classical
  letI : MeasurableSpace Ω := m
  obtain ⟨c,hc,hcm,hcT,hct,hcut,hcc⟩ := positive_real_time_exhaustion hT
  have hex n := scalar_sde_finite_exists P hT F hF hle hnull W C hW hC hclock
    (c n) (hc n).le (hcT n) L hL μ σ hμ hσ hLip ξ hξ hξi
  choose Y Z hm hi ha hZ hZI hrep using hex
  obtain ⟨hCm,hCc⟩ := clock_regular_from_identity C hclock
  have hcompat n k (hnk : n≤k) : Y n=ᵐ[P] fun w => restrictRealPath (hcm.monotone hnk) (Y k w) := by
    obtain ⟨N,hN,hNI,hNr⟩ := finite_sde_restriction P hT F hF hle hnull W C hW hC hclock
      (c k) (hc k).le (hcT k) μ σ hσ ξ (Y k) (ha k) (Z k) (hZ k) (hZI k) (hrep k)
      (c n) (hc n).le (hcm.monotone hnk)
    exact scalar_sde_finite_unique_L2 P hT F hF hle hnull W C hW hC hCm hCc hclock
      (c n) (hc n).le (hcT n) L hL μ σ hμ hσ hLip ξ (Y n)
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
  obtain ⟨X,hXm,hXc,hXp,hXe,hXsm,hXsc⟩ := continuous_adapted_pieces_glue P F hnull
    (fun n _ => realTimeClamp (c n)) (fun _ => hct.monotone) (fun n _ => hcut n)
    (fun _ => hcc) A (fun n => (hA n).1) (fun n => (hA n).2) hall
  have hreg := open_process_real_regularity F (fun t w => σ (X t w))
    (fun t ht => hσ.measurable.comp (hXm t ht))
    (fun w t ht => hσ.continuousAt.comp (hXc w t ht))
  obtain ⟨N,hN,hNI⟩ := continuous_adapted_ito_exists P hT F hF hle hnull W hW
    (fun z => σ (X (realTimeClamp z.2) z.1)) hreg.1 hreg.2
  have hsame n : ∀ᵐ w ∂P,∀ r,r∈Icc 0 (c n) →
      X (realTimeClamp r) w=Y n w (projIcc 0 (c n) (hc n).le r) := by
    filter_upwards [hXp] with w hw
    intro r hr
    have h := hw n (realTimeClamp r)
    rw [min_eq_right (real_time_clamp_mono hr.2)] at h
    dsimp only [A] at h
    rw [finite_path_lift_real (c n) (hc n).le (hcT n).le (Y n) w r hr] at h
    exact h
  have hnoise n : ∀ᵐ w ∂P,∀ r,r∈Icc 0 (c n) → N (realTimeClamp r) w=Z n (realTimeClamp r) w := by
    apply brownian_ito_prefix_congr P hT F hF hle hnull W C hW hC hclock
      (fun t w => σ (X t w)) (fun t w => σ (A n t w)) N (Z n)
      (fun t ht => hσ.measurable.comp (hXm t ht)) (fun t _ => hσ.measurable.comp ((hA n).1 t))
      (fun w t ht => hσ.continuousAt.comp (hXc w t ht)) (fun w t _ => (hσ.comp ((hA n).2 w)).continuousAt)
      hN (hZ n) hNI (hZI n) (c n) (hc n).le (hcT n)
    filter_upwards [hsame n] with w hw
    intro r hr
    dsimp only [A]
    rw [hw r hr,finite_path_lift_real (c n) (hc n).le (hcT n).le (Y n) w r hr]
  refine ⟨X,N,hXm,hXc,hN,hNI,?_⟩
  filter_upwards [ae_all_iff.mpr hsame,ae_all_iff.mpr hnoise,ae_all_iff.mpr hrep] with w hs hn hr
  intro r hr0 hrT
  obtain ⟨n,hnr⟩ := hcc (realTimeClamp r) (real_time_below r hr0 hrT)
  have hrn : r≤c n := by
    change (realTimeClamp r:EReal)<(realTimeClamp (c n):EReal) at hnr
    rw [real_time_clamp_eq r hr0 hrT.le,real_time_clamp_eq (c n) (hc n).le (hcT n).le] at hnr
    exact EReal.coe_le_coe_iff.mp hnr.le
  have h := hr n ⟨r,hr0,hrn⟩
  have hint : (∫ s in 0..r,μ (X (realTimeClamp s) w))=
      ∫ s in 0..r,μ (Y n w (projIcc 0 (c n) (hc n).le s)) := by
    apply intervalIntegral.integral_congr
    intro s hs'
    have hsr : s∈Icc 0 (c n) := Icc_subset_Icc_right hrn (by simpa [uIcc_of_le hr0] using hs')
    dsimp only
    rw [hs n s hsr]
  rw [hs n r ⟨hr0,hrn⟩,hn n r ⟨hr0,hrn⟩,hint,projIcc_of_mem _ ⟨hr0,hrn⟩]
  exact h

end Asakura.Chapter4
