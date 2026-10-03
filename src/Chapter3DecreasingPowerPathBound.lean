import Chapter3C1WeightedProduct
import Chapter3PositiveIntegralComparison
import Chapter3ShiftedPowerExtension
import Chapter3RegularizedStieltjesEnergy
import Chapter2AdaptedVariationAlgebra

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter3Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 3200000
set_option backward.isDefEq.respectTransparency false

/-- Construct the decreasing running-maximum weight and prove the exact
endpoint estimate used in the small-p reverse BDG argument. -/
theorem decreasing_power_ito_path_bound
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (X K : ClosedTime T → Ω → ℝ) (hX : LocalMProcessWitness P F X)
    (hKa : ∀ t, t < ⊤ → Measurable[F t] (K t))
    (hKc : ∀ ω t, t < ⊤ → ContinuousAt (fun s => K s ω) t)
    (hKm : ∀ ω, MonotoneOn (fun t => K t ω) (Iio ⊤))
    (hKp : ∀ ω t, t < ⊤ → 0 ≤ K t ω)
    (hK0 : ∀ᵐ ω ∂P, K ⊥ ω = 0)
    (hXK : ∀ ω t, t < ⊤ → |X t ω| ≤ K t ω)
    (α p : ℝ) (hα : 0 < α) (hp : 0 < p) (hp2 : p < 2)
    (b : ClosedTime T) (hb : b < ⊤) :
    ∃ Y : ClosedTime T → Ω → ℝ,
      LocalMProcessWitness P F Y ∧
      ItoCovarianceFormula P F X (fun z => (α+K (realTimeClamp z.2) z.1)^(p/2-1)) Y ∧
      (∀ᵐ ω ∂P, |Y b ω| ≤ (2/p)*(α+K b ω)^(p/2)-(2/p-1)*α^(p/2)) := by
  obtain ⟨v,hv,hvv,hvd⟩ := shifted_power_extension α (p/2-1) hα
  have hKvar := continuous_increasing_adapted_variation hT F hF K hKa hKm hKc
  have hvc ω t (ht : t < ⊤) : ContinuousAt (fun s => v (K s ω)) t :=
    hv.continuous.continuousAt.comp (hKc ω t ht)
  have hva t (ht : t < ⊤) : Measurable[F t] (fun ω => v (K t ω)) := hv.continuous.measurable.comp (hKa t ht)
  have hnvm ω : MonotoneOn (fun t => -v (K t ω)) (Iio ⊤) := by
    intro s hs t ht hst
    change -v (K s ω) ≤ -v (K t ω)
    rw [hvv _ (hKp ω s hs),hvv _ (hKp ω t ht)]
    apply neg_le_neg
    exact Real.rpow_le_rpow_of_nonpos (by linarith [hKp ω s hs])
      (by linarith [hKm ω hs ht hst]) (by linarith)
  have hnv := continuous_increasing_adapted_variation hT F hF (fun t ω => -v (K t ω))
    (fun t ht => (hva t ht).neg) hnvm (fun ω t ht => (hvc ω t ht).neg)
  have hV : AdaptedLocalVariationWitness F (fun t ω => v (K t ω)) := by
    simpa only [neg_mul,one_mul,neg_neg] using hnv.smul (-1)
  obtain ⟨c,hc,hcm,hcT,_,_,hcc⟩ := positive_real_time_exhaustion hT
  obtain ⟨Y,I,hY,hy,hIv,hIc,hI,hprod⟩ := C1_weighted_product_constructed P hT F hF hle hnull X K hX hKvar hKc
    v (hv.of_le (by norm_num)) hV c (fun n => (hc n).le) hcm.monotone hcT hcc
  have hy' : ItoCovarianceFormula P F X (fun z => (α+K (realTimeClamp z.2) z.1)^(p/2-1)) Y := by
    apply hy.congr_on_time_domain P F X Y _ _
    intro ω r hr hrT
    apply hvv
    apply hKp
    change (realTimeClamp r : EReal) < T
    rw [real_time_clamp_eq r hr hrT.le]
    exact hrT
  have hW := shifted_power_process_regularity F K hKa hKc hKp α (p/2-1) hα
  have hWr := open_process_real_regularity F (fun t ω => (α+K t ω)^(p/2-1)) hW.1 hW.2.1
  obtain ⟨J,hJv,hJc,hJ⟩ := continuous_adapted_variation_exists P F hF hnull c (fun n => (hc n).le)
    hcm.monotone hcT hcc K hKvar hKc (fun z => (α+K (realTimeClamp z.2) z.1)^(p/2-1)) hWr.1 hWr.2
  have hJe := regularized_stieltjes_energy_identity P hT F hF hle K J hKvar hKc hKp hK0 α p hα hp
    c (fun n => (hc n).le) hcT hcc hJ
  have hJscaled := variation_integral_scalar_multiple P K J _ c (fun n => (hc n).le) hJ (1-p/2)
  have hHr := open_process_real_regularity F (fun t ω => X t ω*deriv v (K t ω))
    (fun t ht => (hX.adapted P F t ht).mul ((hv.continuous_deriv (by norm_num)).measurable.comp (hKa t ht)))
    (fun ω t ht => (hX.path P F ω t ht).mul ((hv.continuous_deriv (by norm_num)).continuousAt.comp (hKc ω t ht)))
  have hcI := positive_variation_integral_abs_comparison P K I (fun t ω => (1-p/2)*J t ω)
    (fun z => X (realTimeClamp z.2) z.1*deriv v (K (realTimeClamp z.2) z.1))
    (fun z => (1-p/2)*(α+K (realTimeClamp z.2) z.1)^(p/2-1)) hKm hKc hHr.2
    (fun d hd hdT ω => continuousOn_const.mul (hWr.2 d hd hdT ω))
    c (fun n => (hc n).le) hcT hcc hI hJscaled b hb (by
      intro ω r hr hrT hrb
      have ht : realTimeClamp (T := T) r < ⊤ := hrb.trans_lt hb
      have hbase : 0 < α+K (realTimeClamp r) ω := by linarith [hKp ω _ ht]
      change |X (realTimeClamp r) ω*deriv v (K (realTimeClamp r) ω)| ≤
        (1-p/2)*(α+K (realTimeClamp r) ω)^(p/2-1)
      rw [hvd _ (hKp ω _ ht),abs_mul,abs_mul,abs_of_nonpos (by linarith : p/2-1 ≤ 0),
        abs_of_nonneg (Real.rpow_nonneg hbase.le _)]
      have hx : |X (realTimeClamp r) ω| ≤ α+K (realTimeClamp r) ω := by linarith [hXK ω _ ht]
      have hpow : (α+K (realTimeClamp r) ω)*(α+K (realTimeClamp r) ω)^(p/2-1-1) =
          (α+K (realTimeClamp r) ω)^(p/2-1) := by
        nth_rw 1 [← Real.rpow_one (α+K (realTimeClamp r) ω)]
        rw [← Real.rpow_add hbase]
        congr 1
        ring
      have hh := mul_le_mul_of_nonneg_right hx
        (mul_nonneg (by linarith : 0 ≤ -(p/2-1)) (Real.rpow_nonneg hbase.le (p/2-1-1)))
      nlinarith [hh,hpow])
  refine ⟨Y,hY,hy',?_⟩
  filter_upwards [hprod,hJe,hcI] with ω hpω hjω hiω
  have hbase : 0 < α+K b ω := by linarith [hKp ω b hb]
  have hpow : (α+K b ω)*(α+K b ω)^(p/2-1) = (α+K b ω)^(p/2) := by
    nth_rw 1 [← Real.rpow_one (α+K b ω)]
    rw [← Real.rpow_add hbase]
    congr 1
    ring
  have hterm : |X b ω*v (K b ω)| ≤ (α+K b ω)^(p/2) := by
    rw [hvv _ (hKp ω b hb),abs_mul,abs_of_nonneg (Real.rpow_nonneg hbase.le _)]
    have hh := mul_le_mul_of_nonneg_right
      (show |X b ω| ≤ α+K b ω by linarith [hXK ω b hb]) (Real.rpow_nonneg hbase.le (p/2-1))
    exact hh.trans_eq hpow
  have he : Y b ω = X b ω*v (K b ω)-I b ω := by linarith [hpω b hb]
  have hab : |Y b ω| ≤ |X b ω*v (K b ω)|+|I b ω| := by
    rw [he]
    exact abs_sub _ _
  rw [hjω b hb] at hiω
  have hend := Asakura.Chapter3Written.bdg_endpoint_identity (p := p) (A := α^(p/2)) (B := (α+K b ω)^(p/2)) hp
  nlinarith [hab,hterm,hiω,hend]

end Asakura.Chapter3Complete
#print axioms Asakura.Chapter3Complete.decreasing_power_ito_path_bound
