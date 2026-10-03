import Chapter11ProductConstruction
import Chapter11InverseNoiseCancellation
import Chapter4ItoPairDensity
import Chapter5TimeDensityInitial

open MeasureTheory Set Filter
open scoped Topology
namespace Asakura.Chapter11
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter5 Asakura.Chapter6
set_option maxHeartbeats 4800000
set_option backward.isDefEq.respectTransparency false

/-- The integrating factor identity for a linear SDE with random,
 merely integrable drift. Covariation and both stochastic product terms
 are derived from the actual Ito formulas. -/
theorem inverse_factor_product_constant
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0≤T)] (hT : 0<T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t E,MeasurableSet[m] E → P E=0 → MeasurableSet[F t] E)
    (D Q X Y A B M N : ClosedTime T → Ω → ℝ)
    (hD : LocalMProcessWitness P F D) (hQ : LocalCovarianceWitness P F D D Q)
    (hX : SemimartingaleDecomposition P F X A M)
    (hY : SemimartingaleDecomposition P F Y B N)
    (hMI : ItoCovarianceFormula P F D (fun z => X (realTimeClamp z.2) z.1) M)
    (hNI : ItoCovarianceFormula P F D (fun z => -Y (realTimeClamp z.2) z.1) N)
    (c : ℕ → ℝ) (hc : ∀ n,0≤c n) (hcm : Monotone c) (hcT : ∀ n,(c n:EReal)<T)
    (hcc : ∀ t,t<⊤ → ∃ n,t<realTimeClamp (T:=T) (c n))
    (b q : Ω × ℝ → ℝ) (hbm : ∀ w,Measurable (fun r => b (w,r)))
    (hqm : ∀ w,Measurable (fun r => q (w,r)))
    (hbi : ∀ n,∀ᵐ w ∂P,IntervalIntegrable (fun r => b (w,r)) volume 0 (c n))
    (hqi : ∀ n,∀ᵐ w ∂P,IntervalIntegrable (fun r => q (w,r)) volume 0 (c n))
    (hQe : ∀ n,∀ᵐ w ∂P,∀ r∈Icc 0 (c n),Q (realTimeClamp r) w=∫ s in 0..r,q (w,s))
    (hAe : ∀ n,∀ᵐ w ∂P,∀ r∈Icc 0 (c n),A (realTimeClamp r) w=A ⊥ w+∫ s in 0..r,X (realTimeClamp s) w*b (w,s))
    (hBe : ∀ n,∀ᵐ w ∂P,∀ r∈Icc 0 (c n),B (realTimeClamp r) w=B ⊥ w+∫ s in 0..r,Y (realTimeClamp s) w*(-b (w,s)+q (w,s))) :
    ∀ r : ℝ,0≤r → (r:EReal)<T →
      (fun w => X (realTimeClamp r) w*Y (realTimeClamp r) w)=ᵐ[P] fun w => X ⊥ w*Y ⊥ w := by
  have hXa t (ht : t<⊤) : Measurable[F t] (X t) := by
    have he : X t=fun w => A t w+M t w := funext (hX.decomposition t ht)
    rw [he]
    exact (hX.variation.adapted t ht).add (hX.martingale.adapted P F t ht)
  have hYa t (ht : t<⊤) : Measurable[F t] (Y t) := by
    have he : Y t=fun w => B t w+N t w := funext (hY.decomposition t ht)
    rw [he]
    exact (hY.variation.adapted t ht).add (hY.martingale.adapted P F t ht)
  have hXr := (open_process_real_regularity F X hXa hX.continuous).2
  have hYr := (open_process_real_regularity F Y hYa hY.continuous).2
  have hXm w := open_path_real_measurable _ (hX.continuous w)
  have hYm w := open_path_real_measurable _ (hY.continuous w)
  obtain ⟨C,hC,hCe⟩ := continuous_ito_pair_density P hT F hF hle hnull D D M N Q
    hD hD hX.martingale hY.martingale hQ X (fun t w => -Y t w)
    hXa hX.continuous (fun t ht => (hYa t ht).neg) (fun w t ht => (hY.continuous w t ht).neg)
    hMI hNI q hqm c hc hcm hcT hcc hqi hQe
  obtain ⟨I,J,U,V,hU,hV,hI,hJ,hUI,hVI,hp⟩ := semimartingale_product_constructed P hT F hF hle hnull
    X Y A B M N C hX hY hC c hc hcm hcT hcc
  have hz := inverse_product_noise_cancels P hT F hF hle hnull D X Y M N U V hD
    hX.martingale hY.martingale hU hV hXa hYa hX.continuous hY.continuous hMI hNI hUI hVI
  have hXi n : ∀ᵐ w ∂P,IntervalIntegrable (fun r => X (realTimeClamp r) w*b (w,r)) volume 0 (c n) := by
    filter_upwards [hbi n] with w hw
    exact hw.continuousOn_mul (by rw [uIcc_of_le (hc n)];exact hXr _ (hc n) (hcT n) w)
  have hYi n : ∀ᵐ w ∂P,IntervalIntegrable (fun r => Y (realTimeClamp r) w*(-b (w,r)+q (w,r))) volume 0 (c n) := by
    filter_upwards [hbi n,hqi n] with w hb hq
    exact (hb.neg.add hq).continuousOn_mul (by rw [uIcc_of_le (hc n)];exact hYr _ (hc n) (hcT n) w)
  intro r hr hrT
  have hi := time_density_variation_integral_with_initial P A I (A ⊥)
    (fun z => X (realTimeClamp z.2) z.1*b z) (fun z => Y (realTimeClamp z.2) z.1)
    c hc hcT hcc hAe (fun w => (hXm w).mul (hbm w)) hXi hYm
    (fun n => hYr _ (hc n) (hcT n)) hI r hr hrT
  have hj := time_density_variation_integral_with_initial P B J (B ⊥)
    (fun z => Y (realTimeClamp z.2) z.1*(-b z+q z)) (fun z => X (realTimeClamp z.2) z.1)
    c hc hcT hcc hBe (fun w => (hYm w).mul ((hbm w).neg.add (hqm w))) hYi hXm
    (fun n => hXr _ (hc n) (hcT n)) hJ r hr hrT
  obtain ⟨n,hn⟩ := hcc _ (real_time_below r hr hrT)
  have hrn : r≤c n := by
    change (realTimeClamp r:EReal)<(realTimeClamp (c n):EReal) at hn
    rw [real_time_clamp_eq r hr hrT.le,real_time_clamp_eq (c n) (hc n) (hcT n).le] at hn
    exact EReal.coe_le_coe_iff.mp hn.le
  filter_upwards [hp,hz,hi,hj,hCe n,hXi n,hYi n,hqi n] with w hpw hzw hiw hjw hcw hxi hyi hqi
  have hsub : uIcc 0 r⊆uIcc 0 (c n) := by
    rw [uIcc_of_le hr,uIcc_of_le (hc n)]
    exact Icc_subset_Icc_right hrn
  have hYrc : ContinuousOn (fun s => Y (realTimeClamp s) w) (uIcc 0 r) := by
    rw [uIcc_of_le hr];exact hYr r hr hrT w
  have hXrc : ContinuousOn (fun s => X (realTimeClamp s) w) (uIcc 0 r) := by
    rw [uIcc_of_le hr];exact hXr r hr hrT w
  have hiint := (hxi.mono_set hsub).continuousOn_mul hYrc
  have hjint := (hyi.mono_set hsub).continuousOn_mul hXrc
  have hcint := (hqi.mono_set hsub).continuousOn_mul (hXrc.mul hYrc.neg)
  change IntervalIntegrable (fun s => X (realTimeClamp s) w*(-Y (realTimeClamp s) w)*q (w,s)) volume 0 r at hcint
  have hsum : (∫ s in 0..r,Y (realTimeClamp s) w*(X (realTimeClamp s) w*b (w,s)))+
      (∫ s in 0..r,X (realTimeClamp s) w*(Y (realTimeClamp s) w*(-b (w,s)+q (w,s))))+
      (∫ s in 0..r,X (realTimeClamp s) w*(-Y (realTimeClamp s) w)*q (w,s))=0 := by
    rw [←intervalIntegral.integral_add hiint hjint,←intervalIntegral.integral_add (hiint.add hjint) hcint]
    convert intervalIntegral.integral_zero (a:=(0:ℝ)) (b:=r) using 1
    congr 1
    funext s
    ring
  have hh := hpw _ (real_time_below r hr hrT)
  rw [hiw,hjw,hcw r ⟨hr,hrn⟩] at hh
  have hzero := hzw _ (real_time_below r hr hrT)
  linarith

theorem linear_sde_unique_with_inverse_factor
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0≤T)] (hT : 0<T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t E,MeasurableSet[m] E → P E=0 → MeasurableSet[F t] E)
    (D Q X Y A B M N : ClosedTime T → Ω → ℝ)
    (hD : LocalMProcessWitness P F D) (hQ : LocalCovarianceWitness P F D D Q)
    (hX : SemimartingaleDecomposition P F X A M)
    (hY : SemimartingaleDecomposition P F Y B N)
    (Z A2 M2 : ClosedTime T → Ω → ℝ)
    (hZ : SemimartingaleDecomposition P F Z A2 M2)
    (hM2I : ItoCovarianceFormula P F D (fun z => Z (realTimeClamp z.2) z.1) M2)
    (hinit : X ⊥=ᵐ[P] Z ⊥)
    (hYpos : ∀ᵐ w ∂P,∀ t,t<⊤ → Y t w≠0)
    (hMI : ItoCovarianceFormula P F D (fun z => X (realTimeClamp z.2) z.1) M)
    (hNI : ItoCovarianceFormula P F D (fun z => -Y (realTimeClamp z.2) z.1) N)
    (c : ℕ → ℝ) (hc : ∀ n,0≤c n) (hcm : Monotone c) (hcT : ∀ n,(c n:EReal)<T)
    (hcc : ∀ t,t<⊤ → ∃ n,t<realTimeClamp (T:=T) (c n))
    (b q : Ω × ℝ → ℝ) (hbm : ∀ w,Measurable (fun r => b (w,r)))
    (hqm : ∀ w,Measurable (fun r => q (w,r)))
    (hbi : ∀ n,∀ᵐ w ∂P,IntervalIntegrable (fun r => b (w,r)) volume 0 (c n))
    (hqi : ∀ n,∀ᵐ w ∂P,IntervalIntegrable (fun r => q (w,r)) volume 0 (c n))
    (hQe : ∀ n,∀ᵐ w ∂P,∀ r∈Icc 0 (c n),Q (realTimeClamp r) w=∫ s in 0..r,q (w,s))
    (hAe : ∀ n,∀ᵐ w ∂P,∀ r∈Icc 0 (c n),A (realTimeClamp r) w=A ⊥ w+∫ s in 0..r,X (realTimeClamp s) w*b (w,s))
    (hBe : ∀ n,∀ᵐ w ∂P,∀ r∈Icc 0 (c n),B (realTimeClamp r) w=B ⊥ w+∫ s in 0..r,Y (realTimeClamp s) w*(-b (w,s)+q (w,s)))
    (hA2e : ∀ n,∀ᵐ w ∂P,∀ r∈Icc 0 (c n),A2 (realTimeClamp r) w=A2 ⊥ w+∫ s in 0..r,Z (realTimeClamp s) w*b (w,s)) :
    ∀ r : ℝ,0≤r → (r:EReal)<T →
      X (realTimeClamp r)=ᵐ[P] Z (realTimeClamp r) := by
  have hx := inverse_factor_product_constant P hT F hF hle hnull D Q X Y A B M N hD hQ hX hY
    hMI hNI c hc hcm hcT hcc b q hbm hqm hbi hqi hQe hAe hBe
  have hz := inverse_factor_product_constant P hT F hF hle hnull D Q Z Y A2 B M2 N hD hQ hZ hY
    hM2I hNI c hc hcm hcT hcc b q hbm hqm hbi hqi hQe hA2e hBe
  intro r hr hrT
  filter_upwards [hx r hr hrT,hz r hr hrT,hinit,hYpos] with w hxw hzw hi hp
  apply mul_right_cancel₀ (hp _ (real_time_below r hr hrT))
  rw [hxw,hzw,hi]

end Asakura.Chapter11
