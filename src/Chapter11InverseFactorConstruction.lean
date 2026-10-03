import Chapter11ExponentialDensityDecomposition
import Chapter11ConstantIntegral
import Chapter2ItoAssociativity

open MeasureTheory Set Filter
namespace Asakura.Chapter11
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter5 Asakura.Chapter6
set_option maxHeartbeats 4800000
set_option backward.isDefEq.respectTransparency false

/-- Construct the positive inverse factor exp(-K+Q/2-D) from the drift
 primitive K and the driving local martingale D with bracket Q. -/
theorem inverse_factor_constructed
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0≤T)] (hT : 0<T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t E,MeasurableSet[m] E → P E=0 → MeasurableSet[F t] E)
    (D Q K : ClosedTime T → Ω → ℝ)
    (hD : LocalMProcessWitness P F D) (hQ : LocalCovarianceWitness P F D D Q)
    (hK : AdaptedLocalVariationWitness F K)
    (hKc : ∀ w t,t<⊤ → ContinuousAt (fun s => K s w) t)
    (c : ℕ → ℝ) (hc : ∀ n,0<c n) (hcm : Monotone c) (hcT : ∀ n,(c n:EReal)<T)
    (hcc : ∀ t,t<⊤ → ∃ n,t<realTimeClamp (T:=T) (c n))
    (b q : Ω × ℝ → ℝ) (hbm : ∀ w,Measurable (fun r => b (w,r)))
    (hqm : ∀ w,Measurable (fun r => q (w,r)))
    (hbi : ∀ n,∀ᵐ w ∂P,IntervalIntegrable (fun r => b (w,r)) volume 0 (c n))
    (hqi : ∀ n,∀ᵐ w ∂P,IntervalIntegrable (fun r => q (w,r)) volume 0 (c n))
    (hKe : ∀ n,∀ᵐ w ∂P,∀ r∈Icc 0 (c n),K (realTimeClamp r) w=K ⊥ w+∫ s in 0..r,b (w,s))
    (hQe : ∀ n,∀ᵐ w ∂P,∀ r∈Icc 0 (c n),Q (realTimeClamp r) w=∫ s in 0..r,q (w,s)) :
    ∃ Y B N : ClosedTime T → Ω → ℝ,
      SemimartingaleDecomposition P F Y B N ∧
      ItoCovarianceFormula P F D (fun z => -Y (realTimeClamp z.2) z.1) N ∧
      (∀ t w,Y t w=Real.exp (-K t w+Q t w/2-D t w)) ∧
      (∀ t w,0<Y t w) ∧
      (∀ n,∀ᵐ w ∂P,∀ r∈Icc 0 (c n),B (realTimeClamp r) w=B ⊥ w+
        ∫ s in 0..r,Y (realTimeClamp s) w*(-b (w,s)+q (w,s))) := by
  have hQv := covariance_adapted_variation P F hF hle hD hD hQ
  have hQc := local_covariance_path_continuous P F D D Q hD hD hQ
  let A := fun t w => -K t w+Q t w/2
  let X := fun t w => A t w-D t w
  have hA : AdaptedLocalVariationWitness F A := by
    convert (hK.smul (-1)).add (hQv.smul (1/2)) hF using 1
    funext t w
    dsimp only [A]
    ring
  have hAc w t ht : ContinuousAt (fun s => A s w) t :=
    (hKc w t ht).neg.add ((hQc w t ht).div_const 2)
  have hneg : LocalMProcessWitness P F (fun t w => -D t w) := by
    simpa only [neg_one_mul] using hD.smul P F (-1)
  have hQD : LocalCovarianceWitness P F (fun t w => -D t w) D (fun t w => -Q t w) := by
    convert hQ.bilinear P F hF hle hQ (-2) using 1 <;> funext <;> ring
  have hQQ : LocalCovarianceWitness P F (fun t w => -D t w) (fun t w => -D t w) Q := by
    convert (hQD.symm P F).bilinear P F hF hle (hQD.symm P F) (-2) using 1 <;> funext <;> ring
  have hX : SemimartingaleDecomposition P F X A (fun t w => -D t w) :=
    ⟨hA,hneg,fun w t ht => (hAc w t ht).sub (hD.path P F w t ht),fun _ _ _ => sub_eq_add_neg _ _⟩
  have hAe n : ∀ᵐ w ∂P,∀ r∈Icc 0 (c n),A (realTimeClamp r) w=A ⊥ w+
      ∫ s in 0..r,-b (w,s)+q (w,s)/2 := by
    have hz : realTimeClamp (T:=T) 0=⊥ := by
      apply Subtype.ext
      change (realTimeClamp (T:=T) 0:EReal)=0
      simpa only [EReal.coe_zero] using real_time_clamp_eq (T:=T) 0 le_rfl hT.le
    filter_upwards [hKe n,hQe n,hbi n,hqi n] with w hk hq hb hqi
    have h0 := hq 0 ⟨le_rfl,(hc n).le⟩
    rw [hz,intervalIntegral.integral_same] at h0
    intro r hr
    have hsub : uIcc 0 r⊆uIcc 0 (c n) := by
      rw [uIcc_of_le hr.1,uIcc_of_le (hc n).le]
      exact Icc_subset_Icc_right hr.2
    have hbn : IntervalIntegrable (fun s => -b (w,s)) volume 0 r := (hb.mono_set hsub).neg
    dsimp only [A]
    rw [hk r hr,hq r hr,h0,intervalIntegral.integral_add hbn ((hqi.mono_set hsub).div_const 2),
      intervalIntegral.integral_neg,intervalIntegral.integral_div]
    ring
  obtain ⟨B,N,hY,hNI,hBe⟩ := exponential_density_decomposition P hT F hF hle hnull
    X A (fun t w => -D t w) Q hX hQQ c hc hcm hcT hcc
    (fun z => -b z+q z/2) q (fun w => (hbm w).neg.add ((hqm w).div_const 2)) hqm
    (fun n => by filter_upwards [hbi n,hqi n] with w hb hq;exact hb.neg.add (hq.div_const 2)) hqi hAe hQe
  let Y := fun t w => Real.exp (X t w)
  have hYa t (ht : t<⊤) : Measurable[F t] (Y t) := by
    have hh : X t=fun w => A t w+(-D t w) := funext (hX.decomposition t ht)
    dsimp only [Y]
    rw [hh]
    exact ((hA.adapted t ht).add ((hD.adapted P F t ht).neg)).exp
  have hYc w t ht : ContinuousAt (fun s => Y s w) t :=
    Real.continuous_exp.continuousAt.comp (hX.continuous w t ht)
  have hr := open_process_real_regularity F (fun t w => -Y t w)
    (fun t ht => (hYa t ht).neg) (fun w t ht => (hYc w t ht).neg)
  obtain ⟨L,hL,hLI⟩ := continuous_adapted_ito_exists P hT F hF hle hnull D hD
    (fun z => -Y (realTimeClamp z.2) z.1) hr.1 hr.2
  have hid : ItoCovarianceFormula P F D (fun _ => (-1:ℝ)) (fun t w => -D t w) := by
    simpa only [neg_one_mul] using constant_ito_integral P hT F hF hle hnull D hD (-1)
  have hLI' : ItoCovarianceFormula P F D (fun z => Y (realTimeClamp z.2) z.1*(-1)) L := by
    simpa only [mul_neg_one] using hLI
  have he := ito_integral_associativity P hT F hF hle hnull D (fun t w => -D t w) N L
    (fun _ => (-1:ℝ)) (fun z => Y (realTimeClamp z.2) z.1) hD hneg hY.martingale hL
    (fun _ => measurable_const) (fun w => open_path_real_measurable _ (hYc w)) hid hNI hLI'
  refine ⟨Y,B,N,hY,?_,fun _ _ => rfl,fun _ _ => Real.exp_pos _,?_⟩
  · exact hLI.congr_integral P F hF hle D L N _ hL hY.martingale
      (he.mono fun w hw t ht => (hw t ht).symm)
  · intro n
    filter_upwards [hBe n] with w hw
    intro r hr
    rw [hw r hr]
    congr 1
    apply intervalIntegral.integral_congr
    intro s _
    dsimp only [Y]
    ring

end Asakura.Chapter11
