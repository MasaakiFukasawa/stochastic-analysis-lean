import Chapter6BrownianGridSamplesGaussian
import Chapter6PathFactorLimit
import Chapter6ContinuousItoGridLimit
import Chapter6SquareMeanToL1

open MeasureTheory Set Filter Finset
open scoped Topology BigOperators
namespace Asakura.Chapter6
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter7
set_option maxHeartbeats 3200000
set_option backward.isDefEq.respectTransparency false

/-- Deterministic left sums provide the measurable path representation of
an actual Ito integral, rather than assuming it as part of the likelihood. -/
theorem bounded_ito_path_factor {Ω E : Type*} {m : MeasurableSpace Ω} [MeasurableSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (B : BrownianSystem P d) (j : Fin d)
    (H N : HalfClosedTime → Ω → ℝ)
    (hHa : ∀ t,Measurable[B.F t] (H t)) (hHc : ∀ w,Continuous (fun t => H t w))
    (hN : LocalMProcessWitness P B.F N)
    (hNI : ItoCovarianceFormula P B.F (B.W j) (fun z => H (realTimeClamp z.2) z.1) N)
    (R : ℝ) (hR : 0<R) (K : ℝ) (hK : 0≤K)
    (hHb : ∀ w r,r∈Icc 0 R → |H (realTimeClamp r) w|≤K)
    (X : Ω → E) (hX : Measurable X)
    (hHX : ∀ r,r∈Icc 0 R → Measurable[MeasurableSpace.comap X inferInstance] (H (realTimeClamp r)))
    (hWX : ∀ r,r∈Icc 0 R → Measurable[MeasurableSpace.comap X inferInstance] (B.W j (realTimeClamp r))) :
    ∃ a : E → ℝ,Measurable a ∧ N (realTimeClamp R)=ᵐ[P] a ∘ X := by
  let S := fun n w => ∑ k∈range (n+1),H (realTimeClamp ((k:ℝ)*(R/(n+1)))) w*
      (B.W j (realTimeClamp (((k:ℝ)+1)*(R/(n+1)))) w-B.W j (realTimeClamp ((k:ℝ)*(R/(n+1)))) w)
  obtain ⟨hD2,hlim⟩ := continuous_ito_grid_square_limit P B j H N hHa hHc hN hNI R hR K hK hHb
  have hL := square_mean_zero_implies_L1_zero P _ hD2 hlim
  have htime (n k : ℕ) (hk : k≤n+1) : (k:ℝ)*(R/((n:ℝ)+1))∈Icc 0 R := by
    refine ⟨mul_nonneg (Nat.cast_nonneg _) (by positivity),?_⟩
    have hn : 0<(n:ℝ)+1 := by positivity
    have hk' : (k:ℝ)≤(n:ℝ)+1 := by exact_mod_cast hk
    have he : ((n:ℝ)+1)*(R/((n:ℝ)+1))=R := by field_simp
    exact (mul_le_mul_of_nonneg_right hk' (show 0≤R/((n:ℝ)+1) by positivity)).trans_eq he
  have hSm n : Measurable[MeasurableSpace.comap X inferInstance] (S n) := by
    letI : MeasurableSpace Ω := MeasurableSpace.comap X inferInstance
    apply Finset.measurable_sum
    intro k hk
    have hk' := mem_range.mp hk
    have hlast := htime n (k+1) (by omega)
    simp only [Nat.cast_add,Nat.cast_one] at hlast
    exact (hHX _ (htime n k (by omega))).mul ((hWX _ hlast).sub (hWX _ (htime n k (by omega))))
  have hSi n : Integrable (S n) P := by
    apply integrable_finset_sum
    intro k hk
    have hk' := mem_range.mp hk
    have hbm : AEStronglyMeasurable (H (realTimeClamp ((k:ℝ)*(R/(n+1))))) P := ((hHa _).mono (B.le _) le_rfl).aestronglyMeasurable
    have hbb : ∀ᵐ w ∂P,‖H (realTimeClamp ((k:ℝ)*(R/(n+1)))) w‖≤K := ae_of_all _ (fun w => hHb w _ (htime n k (by omega)))
    obtain ⟨hg,_,_⟩ := brownian_grid_samples_gaussian (n := n+1) P B (R/(n+1)) (by positivity)
      (fun q : Bool => if q then k+1 else k) (fun q => by split_ifs <;> omega) (fun _ => j)
    have hi := ((hg.eval true).integrable.sub (hg.eval false).integrable).bdd_mul hbm hbb
    simpa [Nat.cast_add,Nat.cast_one] using hi
  have hZi : Integrable (N (realTimeClamp R)) P := by
    have hi := ((hD2 0).integrable (by norm_num)).add (hSi 0)
    simpa only [S,Pi.add_def,sub_add_cancel] using hi
  exact path_factor_of_L1_limit P X hX S _ hSm hSi hZi (by simpa only [Real.norm_eq_abs] using hL)

end Asakura.Chapter6
