import Chapter11BarrierTerminal
import Chapter11ReplicationRepresentation
import Chapter2HalfLineLocalization

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter11
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter4 Asakura.Chapter5
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

/-- The preterminal stopped Ito representations and bounded terminal
convergence imply the conditional price identity. The identity at maturity
is derived here rather than assumed as a martingale representation input. -/
theorem bounded_preterminal_price_conditional {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (F : HalfClosedTime → MeasurableSpace Ω)
    (hle : ∀ t,F t≤m) (V : ℝ → Ω → ℝ) (U : Ω → ℝ)
    (T a K : ℝ) (hT : 0<T)
    (hpre : ∀ R,0≤R → R<T → ∃ N : HalfClosedTime → Ω → ℝ,
      ContinuousM2Witness P F N ∧ ∀ s∈Icc 0 R,V s=ᵐ[P] fun w => a+N (realTimeClamp s) w)
    (hVm : ∀ s∈Ico 0 T,StronglyMeasurable[F (realTimeClamp s)] (V s))
    (hUm : AEStronglyMeasurable U P)
    (hbound : ∀ s∈Ico 0 T,∀ᵐ w ∂P,|V s w|≤K)
    (hlimit : ∀ᵐ w ∂P,Tendsto (fun s => V s w) (𝓝[<] T) (𝓝 (U w))) :
    ∀ t∈Ico 0 T,P[U|F (realTimeClamp t)]=ᵐ[P] V t := by
  intro t ht
  obtain ⟨q,hqm,hq,hqlim⟩ := exists_seq_strictMono_tendsto' ht.2
  have hq0 n : 0≤q n := ht.1.trans (hq n).1.le
  have hqmT n : q n∈Ico 0 T := ⟨hq0 n,(hq n).2⟩
  have hVi : Integrable (V t) P := Integrable.of_bound
    ((hVm t ht).mono (hle _)).aestronglyMeasurable K
    ((hbound t ht).mono fun w hw => by simpa only [Real.norm_eq_abs] using hw)
  apply conditional_limit_from_stopped_tests P (F (realTimeClamp t)) (hle _) (fun n => V (q n)) U (V t) (fun _ => K)
    (fun n => ((hVm _ (hqmT n)).mono (hle _)).aestronglyMeasurable) hUm (hVm t ht) hVi (integrable_const _)
  · intro n
    exact (hbound _ (hqmT n)).mono fun w hw => by simpa only [Real.norm_eq_abs] using hw
  · filter_upwards [hlimit] with w hw
    exact hw.comp (tendsto_nhdsWithin_iff.mpr ⟨hqlim,Eventually.of_forall (fun n => (hq n).2)⟩)
  · intro n A hA
    obtain ⟨N,hN,he⟩ := hpre (q n) (hq0 n) (hq n).2
    have hiN := (hN.moment (realTimeClamp (q n))).integrable (by norm_num : (1:ENNReal)≤2)
    have hiNt := (hN.moment (realTimeClamp t)).integrable (by norm_num : (1:ENNReal)≤2)
    have hce : P[(fun w => a+N (realTimeClamp (q n)) w)|F (realTimeClamp t)]=ᵐ[P]
        fun w => a+N (realTimeClamp t) w := by
      have hh := condExp_add (integrable_const a) hiN (F (realTimeClamp t))
      rw [condExp_of_stronglyMeasurable (hle _) stronglyMeasurable_const (integrable_const a)] at hh
      filter_upwards [hh,hN.martingale (realTimeClamp t) (realTimeClamp (q n)) (real_time_clamp_mono (hq n).1.le)] with w hw hmart
      change P[(fun w => a+N (realTimeClamp (q n)) w)|F (realTimeClamp t)] w=a+P[N (realTimeClamp (q n))|F (realTimeClamp t)] w at hw
      simpa only [hmart] using hw
    calc
      (∫ w in A,V (q n) w ∂P)=(∫ w in A,a+N (realTimeClamp (q n)) w ∂P) := integral_congr_ae (ae_restrict_of_ae (he _ ⟨hq0 n,le_rfl⟩))
      _ = ∫ w in A,P[(fun w => a+N (realTimeClamp (q n)) w)|F (realTimeClamp t)] w ∂P :=
        (setIntegral_condExp (hle _) ((integrable_const a).add hiN) hA).symm
      _ = ∫ w in A,a+N (realTimeClamp t) w ∂P := integral_congr_ae (ae_restrict_of_ae hce)
      _ = ∫ w in A,V t w ∂P := integral_congr_ae (ae_restrict_of_ae (he t ⟨ht.1,(hq n).1.le⟩).symm)

end Asakura.Chapter11
