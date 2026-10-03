import Chapter13IntegralPrefixLocality
import Chapter13CovariationPrefixLocality
import Chapter4ConstructedScalarIto
import Chapter5LogExtension

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter13
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter5
set_option maxHeartbeats 5500000
set_option backward.isDefEq.respectTransparency false

theorem positive_log_ito_constructed {Ω:Type*} {m:MeasurableSpace Ω}
    (P:Measure Ω) [IsProbabilityMeasure P] {T:EReal} [Fact (0≤T)] (hT:0<T)
    (F:ClosedTime T → MeasurableSpace Ω) (hF:Monotone F) (hle:∀t,F t≤m)
    (hnull:∀t N,MeasurableSet[m] N → P N=0 → MeasurableSet[F t] N)
    (X A M C:ClosedTime T → Ω → ℝ) (hX:SemimartingaleDecomposition P F X A M)
    (hC:LocalCovarianceWitness P F M M C) (hp:∀t w,0<X t w)
    (c:ℕ → ℝ) (hc:∀n,0≤c n) (hcm:Monotone c) (hcT:∀n,(c n:EReal)<T)
    (hcc:∀t,t<⊤ → ∃n,t<realTimeClamp (T:=T) (c n)) :
    ∃I J L:ClosedTime T → Ω → ℝ,
      AdaptedLocalVariationWitness F I ∧ AdaptedLocalVariationWitness F J ∧
      LocalMProcessWitness P F L ∧
      (∀w t,t<⊤ → ContinuousAt (fun s => I s w) t) ∧
      (∀w t,t<⊤ → ContinuousAt (fun s => J s w) t) ∧
      VariationIntegralFormula P c hc A (fun z => (X (realTimeClamp z.2) z.1)⁻¹) I ∧
      VariationIntegralFormula P c hc C (fun z => -(X (realTimeClamp z.2) z.1)⁻¹^2) J ∧
      ItoCovarianceFormula P F M (fun z => (X (realTimeClamp z.2) z.1)⁻¹) L ∧
      (∀ᵐw∂P,∀t,t<⊤ → Real.log (X t w)=Real.log (X ⊥ w)+I t w+L t w+J t w/2) := by
  have hXa t (ht:t<⊤):Measurable[F t] (X t) := by
    have he:X t=fun w => A t w+M t w := funext (hX.decomposition t ht)
    rw [he]
    exact (hX.variation.adapted t ht).add (hX.martingale.adapted P F t ht)
  let H:=fun t w => (X t w)⁻¹
  let K:=fun t w => -(X t w)⁻¹^2
  have hHa t ht:Measurable[F t] (H t) := (hXa t ht).inv
  have hHc w t ht:ContinuousAt (fun s => H s w) t := (hX.continuous w t ht).inv₀ (hp t w).ne'
  have hKa t ht:Measurable[F t] (K t) := ((hXa t ht).inv.pow_const 2).neg
  have hKc w t ht:ContinuousAt (fun s => K s w) t := ((hHc w t ht).pow 2).neg
  obtain ⟨I,L,hIL,hI,hLI⟩:=continuous_semimartingale_integral_exists P hT F hF hle hnull X A M H hX hHa hHc c hc hcm hcT hcc
  have hCv:=covariance_adapted_variation P F hF hle hX.martingale hX.martingale hC
  have hCc:=local_covariance_path_continuous P F M M C hX.martingale hX.martingale hC
  obtain ⟨J,hJv,hJc,hJ⟩:=continuous_adapted_variation_exists P F hF hnull c hc hcm hcT hcc C hCv hCc
    (fun z => K (realTimeClamp z.2) z.1)
    (open_process_real_regularity F K hKa hKc).1 (open_process_real_regularity F K hKa hKc).2
  let e:=fun n:ℕ => 1/((n:ℝ)+1)
  have ep n:0<e n := by dsimp [e];positivity
  let f:=fun n => logExtension (e n) 1
  have hf n:ContDiff ℝ 3 (f n) := logExtension_contDiff _ _ (ep n) 3
  have hd n x:HasDerivAt (f n) (deriv (f n) x) x := ((hf n).differentiable (by norm_num) x).hasDerivAt
  have hdd n x:HasDerivAt (deriv (f n)) (iteratedDeriv 2 (f n) x) x := by
    simpa only [iteratedDeriv_succ,iteratedDeriv_one,iteratedDeriv_zero] using ((show ContDiff ℝ 2 (f n) from (hf n).of_le (by norm_num)).differentiable_deriv_two x).hasDerivAt
  choose Z Q hZ hQ he using fun n => constructed_scalar_ito P hT F hF hle hnull X A M C hX hC
    (f n) (deriv (f n)) (iteratedDeriv 2 (f n)) ((hf n).of_le (by norm_num)) (hd n) (hdd n) c hc hcm hcT hcc
  have hDa n t ht:Measurable[F t] (fun w => deriv (f n) (X t w)) := ((hf n).continuous_deriv (by norm_num)).measurable.comp (hXa t ht)
  have hDc n w t ht:ContinuousAt (fun s => deriv (f n) (X s w)) t := ((hf n).continuous_deriv (by norm_num)).continuousAt.comp (hX.continuous w t ht)
  have hDDa n t ht:Measurable[F t] (fun w => iteratedDeriv 2 (f n) (X t w)) := ((hf n).continuous_iteratedDeriv 2 (by norm_num)).measurable.comp (hXa t ht)
  have hDDc n w t ht:ContinuousAt (fun s => iteratedDeriv 2 (f n) (X s w)) t := ((hf n).continuous_iteratedDeriv 2 (by norm_num)).continuousAt.comp (hX.continuous w t ht)
  have hloc n:=semimartingale_integral_prefix_locality P hT F hF hle hnull
    (fun _ => X) (fun _ => A) (fun _ => M)
    (fun i => if i then H else fun t w => deriv (f n) (X t w))
    (fun i => if i then (fun t w => I t w+L t w) else Z n) (fun _ => hX)
    (fun i => by cases i;exact hDa n;exact hHa)
    (fun i => by cases i;exact hDc n;exact hHc) c hc hcT hcc
    (fun i => by cases i;exact hZ n;exact ⟨I,L,hIL,hI,hLI⟩)
  have hqloc n:=covariation_integral_prefix_locality P hT F hF hle hnull
    (fun _ => X) (fun _ => X) (fun _ => A) (fun _ => A) (fun _ => M) (fun _ => M) (fun _ => C)
    (fun i => if i then K else fun t w => iteratedDeriv 2 (f n) (X t w))
    (fun i => if i then J else Q n) (fun _ => hX) (fun _ => hX) (fun _ => hC)
    (fun i => by cases i;exact hDDa n;exact hKa)
    (fun i => by cases i;exact hDDc n;exact hKc) c hc hcT hcc
    (fun i => by cases i;exact hQ n;exact hJ)
  refine ⟨I,J,L,hIL.variation,hJv,hIL.martingale,hIL.variation_continuous P F,hJc,hI,hJ,hLI,?_⟩
  filter_upwards [ae_all_iff.mpr he,ae_all_iff.mpr hloc,ae_all_iff.mpr hqloc] with w he hl hq
  intro t ht
  have hcont:ContinuousOn (fun s => X s w) (Iic t) := fun s hs => (hX.continuous w s (hs.trans_lt ht)).continuousWithinAt
  obtain ⟨s,hs,hmin⟩:=(isClosed_Iic : IsClosed (Iic t)).isCompact.exists_isMinOn (show (Iic t).Nonempty from ⟨t,by simp⟩) hcont
  obtain ⟨n,hn⟩:=exists_nat_one_div_lt (hp s w)
  have hlow u (hu:u≤t):e n≤X u w := hn.le.trans (hmin hu)
  have hed u hu:=logExtension_derivatives (e n) 1 (X u w) (ep n) (hlow u hu)
  have hz:=hl n t ht (fun u hu => by simpa [f,H] using (hed u hu).2.1) (fun _ _ => rfl)
  have hj:=hq n t ht (fun u hu => by simpa [f,K,inv_pow] using (hed u hu).2.2) (fun _ _ => rfl) (fun _ _ => rfl)
  have hh:=he n t ht
  change f n (X t w)=f n (X ⊥ w)+Z n t w+Q n t w/2 at hh
  simp only [Bool.false_eq_true,ite_false,ite_true] at hz hj
  rw [hz,hj] at hh
  simpa only [f,(hed t le_rfl).1,(hed ⊥ bot_le).1,div_one,add_assoc] using hh
end Asakura.Chapter13
#print axioms Asakura.Chapter13.positive_log_ito_constructed
