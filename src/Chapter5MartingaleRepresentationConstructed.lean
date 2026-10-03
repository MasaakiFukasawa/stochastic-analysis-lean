import Chapter5ItoRepresentationActual
import Chapter5MartingaleModification
import Chapter5DeterministicM2Stop

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter5
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 4800000
set_option backward.isDefEq.respectTransparency false

/-- Martingale representation from the actual Ito representation theorem.
`hgen` expresses the completed natural-filtration hypothesis: an adapted
variable is a.e. measurable for the full Brownian observation sigma algebra.
The original martingale need not be continuous or have a value at infinity. -/
theorem brownian_martingale_representation_constructed
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
    (hgen : ∀ t,t<⊤ → ∀ X : Ω → ℝ,Measurable[F t] X →
      AEStronglyMeasurable[MeasurableSpace.comap
        (fun w (s : Σ _ : Fin 1,{r : ℝ // 0≤r ∧ (r:EReal)<T}) => W (realTimeClamp s.2.val) w) inferInstance] X P)
    (Y : ClosedTime T → Ω → ℝ)
    (hYm : ∀ t,t<⊤ → Measurable[F t] (Y t))
    (hY2 : ∀ t,t<⊤ → MemLp (Y t) 2 P)
    (hY : ∀ s t,t<⊤ → s≤t → P[Y t|F s] =ᵐ[P] Y s) :
    ∃ G : Ω × ℝ → ℝ,∃ J : ClosedTime T → Ω → ℝ,
      Measurable G ∧
      (∀ l,@Measurable _ _ (progressiveSpace (fun t : Icc (0:ℝ) (c l) => F (realTimeClamp t.val))) inferInstance
        (fun z : Ω × Icc (0:ℝ) (c l) => G (z.1,z.2.val))) ∧
      LocalMProcessWitness P F J ∧ ItoCovarianceFormula P F W G J ∧
      (∀ R : ℝ,MemLp G 2 (P.prod (volume.restrict (Ioc 0 R)))) ∧
      ∀ t,t<⊤ → Y t =ᵐ[P] fun w => Y ⊥ w+J t w := by
  classical
  have hCs (i j : Fin 1) : LocalCovarianceWitness P F W W (fun t w => if i=j then A t w else 0) := by
    have he : i=j := Subsingleton.elim _ _
    simpa only [he,ite_true] using hA
  have hrep := brownian_ito_representation_actual P hT F hF hle hnull (fun _ : Fin 1 => W) A
    (fun _ => hW) hCs hclock c hc hcm hcT hct hcut hcc hco
  have hNat (N : ℕ) : ((N:ℝ):EReal)<T := by
    obtain ⟨l,hl⟩ := hco (N:ℝ)
    exact (EReal.coe_le_coe hl).trans_lt (hcT l)
  have hq (N : ℕ) : realTimeClamp (T := T) (N:ℝ)<⊤ := by
    change (realTimeClamp (N:ℝ):EReal)<T
    rw [real_time_clamp_eq _ (Nat.cast_nonneg N) (hNat N).le]
    exact hNat N
  have hYi t ht : Integrable (Y t) P := (hY2 t ht).integrable (by norm_num)
  have hstep (j : ℕ) :
      ∃ H : progressiveEnergyIntegrands F c (P.prod (volume.restrict (Ioi 0))),
      ∃ M : ClosedTime T → Ω → ℝ,
        ContinuousM2Witness P F M ∧
        ItoCovarianceFormula P F W (fun z => (Ioc (j:ℝ) (j+1)).indicator (fun r => H.val (z.1,r)) z.2) M ∧
        M ⊤ =ᵐ[P] fun w => Y (realTimeClamp ((j+1:ℕ):ℝ)) w-Y (realTimeClamp (j:ℝ)) w := by
    let a := realTimeClamp (T := T) (j:ℝ)
    let b := realTimeClamp (T := T) ((j+1:ℕ):ℝ)
    have hab : a≤b := real_time_clamp_mono (by exact_mod_cast Nat.le_succ j)
    let ξ := fun w => Y b w-Y a w
    have hξL : MemLp ξ 2 P := (hY2 b (hq (j+1))).sub (hY2 a (hq j))
    have hξi : Integrable ξ P := hξL.integrable (by norm_num)
    have hξm : Measurable[F b] ξ := (hYm b (hq (j+1))).sub ((hYm a (hq j)).mono (hF hab) le_rfl)
    have hξ0 : P[ξ|F a] =ᵐ[P] 0 := by
      have hh := condExp_sub (m := F a) (hYi b (hq (j+1))) (hYi a (hq j))
      rw [condExp_of_stronglyMeasurable (hle a) (hYm a (hq j)).stronglyMeasurable (hYi a (hq j))] at hh
      filter_upwards [hh,hY a b (hq (j+1)) hab] with w hw hyw
      simpa only [ξ,Pi.sub_def,Pi.sub_apply,hyw,sub_self,Pi.zero_apply] using hw
    have hmean : (∫ w,ξ w ∂P)=0 := by
      have hh := integral_congr_ae hξ0
      rw [integral_condExp (hle a)] at hh
      simpa using hh
    have hUg := (hgen b (hq (j+1)) ξ hξm).congr hξL.coeFn_toLp.symm
    obtain ⟨H,M,hM,hMI,he⟩ := hrep (hξL.toLp ξ) hUg
    have hUmean : (∫ w,(hξL.toLp ξ) w ∂P)=0 := (integral_congr_ae hξL.coeFn_toLp).trans hmean
    have hend : M 0 ⊤ =ᵐ[P] ξ := by
      filter_upwards [he,hξL.coeFn_toLp] with w hw hξw
      simpa only [hξw,hUmean,zero_add,Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero] using hw.symm
    obtain ⟨hMa,hMb⟩ := representation_increment_endpoints P F hle (M 0) (hM 0) a b ξ hξi hξm hξ0 hend
    have hMl := continuous_m2_is_local P F hF hle (fun l => realTimeClamp (T := T) (c l))
      hct.monotone hcut hcc (M 0) (hM 0)
    obtain ⟨Z,hZ,_,hZI,hZt⟩ := represented_M2_interval_restriction P hT F hF hle hnull W (M 0) hW (hM 0) hMl
      (H 0).val (fun w => (H 0).property.1.comp measurable_prodMk_left) (hMI 0)
      (j:ℝ) ((j+1:ℕ):ℝ) (Nat.cast_nonneg j) (by exact_mod_cast Nat.le_succ j) ξ hMa hMb
    exact ⟨H 0,Z,hZ,by simpa only [Nat.cast_add,Nat.cast_one] using hZI,hZt⟩
  choose H M hM hMI hMt using hstep
  obtain ⟨J,hJ,hJI,hL,hmod⟩ := martingale_modification_from_interval_representations P hT F hF hle hnull
    W A hW hA c hc hcm hcT hct hcut hcc
    (fun l w r hr => hclock w r hr.1 ((EReal.coe_le_coe hr.2).trans_lt (hcT l)))
    (fun j => (H j).val) (fun j => (H j).property.1) (fun j => (H j).property.2.1)
    (fun j => (H j).property.2.2) hNat Y hYm hYi hY M hM hMI hMt
  let G := fun z : Ω × ℝ => (H (Nat.ceil z.2-1)).val z
  have hgm : Measurable G := by
    have hh : Measurable (fun p : (Ω × ℝ) × ℕ => (H (p.2-1)).val p.1) :=
      measurable_from_prod_countable_left (fun j => (H (j-1)).property.1)
    exact hh.comp (measurable_id.prodMk (Nat.measurable_ceil.comp measurable_snd))
  refine ⟨G,J,hgm,?_,hJ,hJI,hL,hmod⟩
  intro l
  exact ceil_integrand_progressive (c l) (fun t : Icc (0:ℝ) (c l) => F (realTimeClamp t.val))
    (fun j => (H (j-1)).val) (fun j => (H (j-1)).property.2.1 l)

end Asakura.Chapter5
