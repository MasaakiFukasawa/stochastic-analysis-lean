import Chapter11C12ExtensionDerivatives
import Chapter11StoppedC12Martingale

open MeasureTheory Set Filter
open scoped Topology
namespace Asakura.Chapter11
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter5
set_option maxHeartbeats 4800000
set_option backward.isDefEq.respectTransparency false

/-- The local C1,2 stopped PDE argument. Extension outside the stopping
 rectangle is constructed and all Ito integrals are constructed. -/
theorem local_c12_stopped_representation
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0≤T)] (hT : 0<T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t E,MeasurableSet[m] E → P E=0 → MeasurableSet[F t] E)
    (X A M C : ClosedTime T → Ω → ℝ) (hX : SemimartingaleDecomposition P F X A M)
    (hC : LocalCovarianceWitness P F M M C)
    (a R U l x0 x1 u : ℝ) (ha : a<0) (hR : 0≤R) (hRU : R<U)
    (hl : l<x0) (hx : x0≤x1) (hu : x1<u)
    (v : ℝ → ℝ → ℝ) (vt : ℝ × ℝ → ℝ)
    (hv : ∀ t∈Ioo a U,ContDiffOn ℝ 2 (v t) (Ioo l u))
    (hvt : ∀ t∈Ioo a U,∀ x∈Ioo l u,HasDerivAt (fun s => v s x) (vt (t,x)) t)
    (hvc : ContinuousOn (fun z : ℝ × ℝ => v z.1 z.2) (Ioo a U ×ˢ Ioo l u))
    (hvtc : ContinuousOn vt (Ioo a U ×ˢ Ioo l u))
    (hdxc : ContinuousOn (fun z : ℝ × ℝ => deriv (v z.1) z.2) (Ioo a U ×ˢ Ioo l u))
    (hxxc : ContinuousOn (fun z : ℝ × ℝ => deriv (deriv (v z.1)) z.2) (Ioo a U ×ˢ Ioo l u))
    (hRT : (R:EReal)<T)
    (c : ℕ → ℝ) (hc : ∀ n,0≤c n) (hcm : Monotone c) (hcT : ∀ n,(c n:EReal)<T)
    (hcc : ∀ t,t<⊤ → ∃ n,t<realTimeClamp (T:=T) (c n))
    (b q : Ω × ℝ → ℝ) (hbm : ∀ w,Measurable (fun r => b (w,r)))
    (hqm : ∀ w,Measurable (fun r => q (w,r)))
    (hbi : ∀ n,∀ᵐ w ∂P,IntervalIntegrable (fun r => b (w,r)) volume 0 (c n))
    (hqi : ∀ n,∀ᵐ w ∂P,IntervalIntegrable (fun r => q (w,r)) volume 0 (c n))
    (hAe : ∀ n,∀ᵐ w ∂P,∀ r∈Icc 0 (c n),A (realTimeClamp r) w=A ⊥ w+∫ s in 0..r,b (w,s))
    (hCe : ∀ n,∀ᵐ w ∂P,∀ r∈Icc 0 (c n),C (realTimeClamp r) w=∫ s in 0..r,q (w,s))
    (τ : Ω → Icc (0:ℝ) R)
    (hτ : ∀ t,MeasurableSet[F t] {w | realTimeClamp (τ w).val≤t})
    (hpath : ∀ᵐ w ∂P,∀ r∈Icc 0 (τ w).val,X (realTimeClamp r) w∈Icc x0 x1)
    (hpde : ∀ᵐ w ∂P,∀ r∈Icc 0 (τ w).val,
      vt (r,X (realTimeClamp r) w)+deriv (v r) (X (realTimeClamp r) w)*b (w,r)+
        deriv (deriv (v r)) (X (realTimeClamp r) w)*q (w,r)/2=0)
    (K : ℝ) (hbound : ∀ᵐ w ∂P,∀ r∈Icc 0 (τ w).val,|v r (X (realTimeClamp r) w)|≤K) :
    ∃ N : ClosedTime T → Ω → ℝ,ContinuousM2Witness P F N ∧
      (∀ᵐ w ∂P,∀ r∈Icc 0 R,
        v (min (τ w).val r) (X (realTimeClamp (min (τ w).val r)) w)=
          v 0 (X ⊥ w)+N (realTimeClamp r) w) := by
  obtain ⟨g,gt,hg,hgt,hgc,hgtc,hdc,hddc,hge⟩ := c12_rectangle_extension
    a 0 R U l x0 x1 u ha hR hRU hl hx hu v vt hv hvt hvc hvtc hdxc hxxc
  obtain ⟨N,hN,hNI,he⟩ := scalar_c12_density_ito P hT F hF hle hnull X A M C hX hC
    g gt hg hgt hgc hgtc hdc hddc R hR hRT c hc hcm hcT hcc b q hbm hqm hbi hqi hAe hCe
  have hz : realTimeClamp (T:=T) 0=⊥ := by
    apply Subtype.ext
    change (realTimeClamp (T:=T) 0:EReal)=0
    simpa only [EReal.coe_zero] using real_time_clamp_eq (T:=T) 0 le_rfl hT.le
  have hXa t (ht : t<⊤) : Measurable[F t] (X t) := by
    have hh : X t=fun w => A t w+M t w := funext (hX.decomposition t ht)
    rw [hh]
    exact (hX.variation.adapted t ht).add (hX.martingale.adapted P F t ht)
  have hXr := (open_process_real_regularity F X hXa hX.continuous).2 R hR hRT
  have hNr := (open_process_real_regularity F N (hN.adapted P F) (hN.path P F)).2 R hR hRT
  obtain ⟨n,hn⟩ := hcc _ (real_time_below R hR hRT)
  have hRn : R≤c n := by
    change (realTimeClamp R:EReal)<(realTimeClamp (c n):EReal) at hn
    rw [real_time_clamp_eq R hR hRT.le,real_time_clamp_eq (c n) (hc n) (hcT n).le] at hn
    exact EReal.coe_le_coe_iff.mp hn.le
  have hsub : uIcc 0 R⊆uIcc 0 (c n) := by
    rw [uIcc_of_le hR,uIcc_of_le (hc n)]
    exact Icc_subset_Icc_right hRn
  have hbR := (hbi n).mono (fun w hw => hw.mono_set hsub)
  have hqR := (hqi n).mono (fun w hw => hw.mono_set hsub)
  have hcommon := c12_ito_common_representation P R hR
    (fun r => X (realTimeClamp r)) (fun r => N (realTimeClamp r)) hXr hNr
    g gt hgc hgtc hdc hddc b q hbR hqR (by simpa only [hz] using he)
  simp only [hz] at hcommon
  let G := fun w r => gt (r,X (realTimeClamp r) w)+deriv (g r) (X (realTimeClamp r) w)*b (w,r)+
    deriv (deriv (g r)) (X (realTimeClamp r) w)*q (w,r)/2
  have hG : ∀ᵐ w ∂P,∀ r∈Icc 0 (τ w).val,G w r=0 := by
    filter_upwards [hpath,hpde] with w hw hp
    intro r hr
    obtain ⟨hnear,hgtv⟩ := hge r ⟨hr.1,hr.2.trans (τ w).property.2⟩ _ (hw r hr)
    obtain ⟨_,hd,hdd⟩ := local_c12_extension_derivatives g v r _ hnear
    dsimp only [G]
    rw [hgtv,hd,hdd]
    exact hp r hr
  have hgb : ∀ᵐ w ∂P,∀ r∈Icc 0 (τ w).val,|g r (X (realTimeClamp r) w)|≤K := by
    filter_upwards [hpath,hbound] with w hw hb
    intro r hr
    have hh := (hge r ⟨hr.1,hr.2.trans (τ w).property.2⟩ _ (hw r hr)).1.eq_of_nhds
    rw [hh]
    exact hb r hr
  obtain ⟨hstop,hrep⟩ := bounded_stopped_c12_martingale P F hF hle R hR hRT X N hN g G τ hτ hcommon hG K hgb
  refine ⟨(fun t w => N (min (realTimeClamp (τ w).val) t) w),hstop,?_⟩
  filter_upwards [hrep,hpath] with w hw hp
  intro r hr
  have hmin : min (τ w).val r∈Icc 0 (τ w).val := ⟨le_min (τ w).property.1 hr.1,min_le_left _ _⟩
  have hnow := (hge _ ⟨hmin.1,hmin.2.trans (τ w).property.2⟩ _ (hp _ hmin)).1.eq_of_nhds
  have hzero := (hge 0 ⟨le_rfl,hR⟩ _ (hp 0 ⟨le_rfl,(τ w).property.1⟩)).1.eq_of_nhds
  rw [hz] at hzero
  simpa only [hnow,hzero] using hw r hr

end Asakura.Chapter11
