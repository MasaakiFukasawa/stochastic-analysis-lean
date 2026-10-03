import Chapter13ShiftLogCovariance
import Chapter13ForwardDrift
import Chapter4CovarianceSumsDensity
import Chapter2LocalCovarianceAE

open MeasureTheory Set Filter
open scoped Topology BigOperators
namespace Asakura.Chapter13
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter5
set_option maxHeartbeats 3800000
set_option backward.isDefEq.respectTransparency false

/-- A logarithmic numeraire which is a finite negative sum of logarithmic
rates turns the numeraire bracket correction into the cumulative correction.
All brackets here are the actual continuous local-martingale covariations. -/
theorem cumulative_log_drift {Ω:Type*} {m:MeasurableSpace Ω}
    (P:Measure Ω) [IsProbabilityMeasure P] {T:EReal} [Fact (0≤T)] (hT:0<T)
    (F:ClosedTime T → MeasurableSpace Ω) (hF:Monotone F) (hle:∀t,F t≤m)
    {n:ℕ} (U V L:Fin n → ClosedTime T → Ω → ℝ)
    (hU:∀i,SemimartingaleDecomposition P F (U i) (V i) (L i))
    (Z A N Y X D:ClosedTime T → Ω → ℝ)
    (hZ:SemimartingaleDecomposition P F Z A N)
    (hY:LocalMProcessWitness P F Y)
    (K:ClosedTime T → Ω → ℝ) (hK:AdaptedLocalVariationWitness F K)
    (hKc:∀w t,t<⊤ → ContinuousAt (fun s => K s w) t)
    (he:∀t,t<⊤ → ∀w,Z t w=K t w-∑i,U i t w)
    (C:Fin n → ClosedTime T → Ω → ℝ)
    (hC:∀i,LocalCovarianceWitness P F Y (L i) (C i))
    (hD:LocalCovarianceWitness P F Y N D)
    (hXD:LocalMProcessWitness P F (fun t w => X t w+D t w))
    (hXa:∀t,t<⊤ → Measurable[F t] (X t))
    (hXc:∀w t,t<⊤ → ContinuousAt (fun s => X s w) t) :
    LocalMProcessWitness P F (fun t w => X t w-∑i,C i t w) := by
  let S:=fun t w => ∑i,(-1:ℝ)*L i t w
  have hS:LocalMProcessWitness P F S := local_martingale_finset_sum P hT F hF hle Finset.univ
    (fun i t w => (-1:ℝ)*L i t w) (fun i _ => by simpa using (hU i).martingale.smul P F (-1))
  have hV:=adapted_variation_finset_sum hT F hF Finset.univ V (fun i _ => (hU i).variation)
  have hother:SemimartingaleDecomposition P F Z (fun t w => K t w+(-1:ℝ)*(∑i,V i t w)) S := by
    refine ⟨hK.add (hV.smul (-1)) hF,hS,hZ.continuous,?_⟩
    intro t ht w
    rw [he t ht w]
    have hh:∑i,U i t w=(∑i,V i t w)+(∑i,L i t w) := by
      simp_rw [(hU _).decomposition t ht w]
      exact Finset.sum_add_distrib
    simp only [S,Finset.sum_neg_distrib,neg_mul,one_mul,hh]
    ring
  have hNS:∀ᵐw∂P,∀t,t<⊤ → N t w=S t w :=
    (hZ.unique P F hF hle hother).mono (fun w hw t ht => (hw t ht).2)
  have hsum:LocalCovarianceWitness P F Y S (fun t w => ∑i,(-1:ℝ)*C i t w) :=
    (weighted_covariance_finset_left P hT F hF hle Finset.univ L C Y (fun _ => -1)
      (fun i _ => (hC i).symm P F)).symm P F
  have hD':=hD.congr_ae_processes P F hF hle hY hZ.martingale hY hS
    (Filter.Eventually.of_forall (fun _ _ _ => rfl)) hNS
  have hDS:=hD'.unique P F hF hle hsum
  apply Asakura.Chapter3Complete.LocalMProcessWitness.congr_ae_open P F hF hXD
  · intro t ht
    exact (hXa t ht).sub (Finset.measurable_sum _ (fun i _ =>
      (covariance_adapted_variation P F hF hle hY (hU i).martingale (hC i)).adapted t ht))
  · intro w t ht
    have hc : ∀s:Finset (Fin n),ContinuousAt (fun u => ∑i∈s,C i u w) t := by
      intro s
      induction s using Finset.induction_on with
      | empty => simpa using (continuousAt_const : ContinuousAt (fun _ : ClosedTime T => (0:ℝ)) t)
      | @insert i s hi ih =>
        have hh := (local_covariance_path_continuous P F Y (L i) (C i) hY (hU i).martingale (hC i) w t ht).add ih
        convert hh using 1
        ext u
        simp only [Finset.sum_insert hi,Pi.add_apply]
    exact (hXc w t ht).sub (hc Finset.univ)
  · filter_upwards [hDS] with w hw
    intro t ht
    rw [hw t ht]
    simp [sub_eq_add_neg]
end Asakura.Chapter13
#print axioms Asakura.Chapter13.cumulative_log_drift
