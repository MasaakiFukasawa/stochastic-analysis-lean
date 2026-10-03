import Chapter2StoppedCovariance
import Chapter2AdaptedGluing
import Chapter2LocalProcess

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
set_option maxHeartbeats 600000

/-- Construction of local covariation from the chapter's bounded localizers.
The stopped product-minus-covariation is proved to be an actual continuous
L2 martingale. No covariation or gluing operator is supplied as a premise. -/
theorem local_covariation_exists_along_localizers
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (X Y : ClosedTime T → Ω → ℝ)
    (τ : ℕ → Ω → ClosedTime T)
    (hτ : ∀ n t, MeasurableSet[F t] {ω | τ n ω ≤ t})
    (hmono : ∀ ω, Monotone (fun n => τ n ω))
    (htop : ∀ n ω, τ n ω < ⊤)
    (hcofinal : ∀ ω t, t < ⊤ → ∃ n, t < τ n ω)
    (hX : ∀ n, (fun t ω => X (min (τ n ω) t) ω) ∈ boundedMProcess P F)
    (hY : ∀ n, (fun t ω => Y (min (τ n ω) t) ω) ∈ boundedMProcess P F) :
    ∃ C : ClosedTime T → Ω → ℝ,
      (∀ t, t < ⊤ → Measurable[F t] (C t)) ∧
      (∀ ω t, t < ⊤ → ContinuousAt (fun s => C s ω) t) ∧
      (∀ n ω, ∃ U V : ClosedTime T → ℝ, Monotone U ∧ Monotone V ∧
        ∀ t, C (min (τ n ω) t) ω = U t - V t) ∧
      (∀ n, ContinuousM2Witness P F (fun t ω =>
        X (min (τ n ω) t) ω * Y (min (τ n ω) t) ω - C (min (τ n ω) t) ω)) ∧
      (∀ᵐ ω ∂P, ∀ n t, C (min (τ n ω) t) ω =
        boundedCov P F hF hle hnull ⟨_, hX n⟩ ⟨_, hY n⟩ t ω) := by
  let Bx (n) : boundedMProcess P F := ⟨_, hX n⟩
  let By (n) : boundedMProcess P F := ⟨_, hY n⟩
  let A (n) := boundedCov P F hF hle hnull (Bx n) (By n)
  have hAm (n t) : Measurable[F t] (A n t) := by
    exact (((boundedQV_properties P F hF hle hnull (Bx n+By n)).1 t).sub
      ((boundedQV_properties P F hF hle hnull (Bx n-By n)).1 t)).div_const 4
  have hAc (n ω) : Continuous (fun t => A n t ω) := by
    exact (((boundedQV_properties P F hF hle hnull (Bx n+By n)).2.1 ω).sub
      ((boundedQV_properties P F hF hle hnull (Bx n-By n)).2.1 ω)).div_const 4
  have hAv (n ω) := bounded_cov_in_A P F hF hle hnull (Bx n) (By n) ω
  have hcompat := covariances_along_localizers_compatible P F hF hle hnull X Y τ hτ hmono hX hY
  obtain ⟨C,hm,hc,he,hlim,hsm,hsc,hsv⟩ := adapted_continuous_stopped_gluing P F hnull
    τ hmono htop hcofinal A hAm hAc hAv hcompat
  refine ⟨C,hm,hc,hsv,?_,he⟩
  intro n
  have hM := bounded_cov_product_witness P F hF hle hnull (Bx n) (By n)
  have heq (t) : (fun ω => X (min (τ n ω) t) ω * Y (min (τ n ω) t) ω -
      C (min (τ n ω) t) ω) =ᵐ[P] (fun ω => (Bx n).val t ω * (By n).val t ω - A n t ω) := by
    filter_upwards [he] with ω hω
    rw [hω n t]
  refine ⟨fun t => (((hX n).1.adapted t).mul ((hY n).1.adapted t)).sub (hsm n t),
    fun t => MemLp.ae_eq (heq t).symm (hM.moment t),
    fun ω => (((hX n).1.path ω).mul ((hY n).1.path ω)).sub (hsc n ω),
    ?_, (heq ⊥).trans hM.initial⟩
  intro s t hst
  exact (condExp_congr_ae (heq t)).trans ((hM.martingale s t hst).trans (heq s).symm)

/-- Uniqueness on [0,T) from local finite variation and the product
martingale property, not from an assumed uniqueness of covariation. -/
theorem local_covariation_unique_along_localizers
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (X Y A B : ClosedTime T → Ω → ℝ)
    (τ : ℕ → Ω → ClosedTime T)
    (hcofinal : ∀ ω t, t < ⊤ → ∃ n, t ≤ τ n ω)
    (hA : ∀ n ω, ∃ U V : ClosedTime T → ℝ, Monotone U ∧ Monotone V ∧
      ∀ t, A (min (τ n ω) t) ω = U t - V t)
    (hB : ∀ n ω, ∃ U V : ClosedTime T → ℝ, Monotone U ∧ Monotone V ∧
      ∀ t, B (min (τ n ω) t) ω = U t - V t)
    (hMA : ∀ n, ContinuousM2Witness P F (fun t ω =>
      X (min (τ n ω) t) ω * Y (min (τ n ω) t) ω - A (min (τ n ω) t) ω))
    (hMB : ∀ n, ContinuousM2Witness P F (fun t ω =>
      X (min (τ n ω) t) ω * Y (min (τ n ω) t) ω - B (min (τ n ω) t) ω)) :
    ∀ᵐ ω ∂P, ∀ t, t < ⊤ → A t ω = B t ω := by
  have hM (n) : ContinuousM2Witness P F
      (fun t ω => A (min (τ n ω) t) ω - B (min (τ n ω) t) ω) := by
    have h := (hMB n).add P F ((hMA n).smul P F (-1))
    convert h using 1 <;> ext t ω <;> simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] <;> ring
  have hBV (n ω) : ∃ U V : ClosedTime T → ℝ, Monotone U ∧ Monotone V ∧
      ∀ t, A (min (τ n ω) t) ω - B (min (τ n ω) t) ω = U t - V t := by
    obtain ⟨Ap,An,hAp,hAn,heA⟩ := hA n ω
    obtain ⟨Bp,Bn,hBp,hBn,heB⟩ := hB n ω
    refine ⟨Ap+Bn, An+Bp, hAp.add hBn, hAn.add hBp, ?_⟩
    intro t
    rw [heA t, heB t]
    simp only [Pi.add_apply]
    ring
  have hz := local_bv_martingale_zero P F hF hle (fun t ω => A t ω - B t ω)
    τ hcofinal hM hBV
  exact hz.mono fun ω hω t ht => sub_eq_zero.mp (hω t ht)

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.local_covariation_exists_along_localizers

#print axioms Asakura.Chapter2Complete.local_covariation_unique_along_localizers
