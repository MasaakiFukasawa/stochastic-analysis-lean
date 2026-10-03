import Chapter2ElementaryCovariance
import Chapter2LocalCovarianceIdentification

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false

/-- The elementary-integral covariance formula for actual local
martingales. The bounded formula is applied to common stopped processes and
then their constructed covariations are identified with the local ones. -/
theorem elementary_local_integral_covariance
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (X Y C : ClosedTime T → Ω → ℝ)
    (hX : LocalMProcessWitness P F X) (hY : LocalMProcessWitness P F Y)
    (hC : LocalCovarianceWitness P F X Y C)
    (a b : ClosedTime T) (hab : a ≤ b)
    (G : Ω → ℝ) (hGm : Measurable[F a] G) (hG : MemLp G ∞ P)
    (D : ClosedTime T → Ω → ℝ)
    (hD : LocalCovarianceWitness P F
      (fun t ω => G ω * (X (min b t) ω-X (min a t) ω)) Y D) :
    ∀ᵐ ω ∂P, ∀ t, t < ⊤ → D t ω = G ω * (C (min b t) ω-C (min a t) ω) := by
  obtain ⟨τx,htx,hmx,httx,hcx,hbx⟩ := hX.localizers
  obtain ⟨τy,hty,hmy,htty,hcy,hby⟩ := hY.localizers
  let τ := fun n ω => min (τx n ω) (τy n ω)
  have ht (n) : ∀ t, MeasurableSet[F t] {ω | τ n ω ≤ t} :=
    (written_stopping_min_max F (τx n) (τy n) (htx n) (hty n)).1
  have hmono (ω) : Monotone (fun n => τ n ω) := (hmx ω).min (hmy ω)
  have htt (n ω) : τ n ω < ⊤ := (min_le_left _ _).trans_lt (httx n ω)
  have hc (ω t) (htop : t < ⊤) : ∃ n, t < τ n ω :=
    (common_localizers_cofinal (fun n => τx n ω) (fun n => τy n ω)
      (hmx ω) (hmy ω) (hcx ω) (hcy ω)).2 t htop
  have hx (n) : (fun t ω => X (min (τ n ω) t) ω) ∈ boundedMProcess P F :=
    bounded_at_minimum P F hF hle X (τx n) (τy n) (hty n) (hbx n)
  have hy (n) : (fun t ω => Y (min (τ n ω) t) ω) ∈ boundedMProcess P F := by
    simpa only [τ,min_comm (τx n _) (τy n _)] using
      bounded_at_minimum P F hF hle Y (τy n) (τx n) (htx n) (hby n)
  let Z := fun t ω => G ω * (X (min b t) ω-X (min a t) ω)
  have hz (n) : (fun t ω => Z (min (τ n ω) t) ω) ∈ boundedMProcess P F := by
    have h := elementary_integral_bounded_martingale P F hF hle ⟨_,hx n⟩ a b hab G hGm hG
    convert h using 1
    funext t ω
    change G ω * (X (min b (min (τ n ω) t)) ω-X (min a (min (τ n ω) t)) ω) = _
    rw [min_left_comm b,min_left_comm a]
  have hCe := local_covariance_matches_bounded_localizers P F hF hle hnull X Y C hC τ ht hmono htt hc hx hy
  have hDe := local_covariance_matches_bounded_localizers P F hF hle hnull Z Y D hD τ ht hmono htt hc hz hy
  have helem (n) : ∀ᵐ ω ∂P, ∀ t,
      boundedCov P F hF hle hnull ⟨_,hz n⟩ ⟨_,hy n⟩ t ω =
      G ω * (boundedCov P F hF hle hnull ⟨_,hx n⟩ ⟨_,hy n⟩ (min b t) ω-
        boundedCov P F hF hle hnull ⟨_,hx n⟩ ⟨_,hy n⟩ (min a t) ω) := by
    have h := elementary_integral_covariance P F hF hle hnull ⟨_,hx n⟩ ⟨_,hy n⟩ a b hab G hGm hG
    have he : (⟨_,hz n⟩ : boundedMProcess P F) =
        ⟨_,elementary_integral_bounded_martingale P F hF hle ⟨_,hx n⟩ a b hab G hGm hG⟩ := by
      apply Subtype.ext
      funext t ω
      change G ω * (X (min b (min (τ n ω) t)) ω-X (min a (min (τ n ω) t)) ω) = _
      rw [min_left_comm b,min_left_comm a]
    rw [he]
    exact h
  filter_upwards [hCe,hDe,ae_all_iff.2 helem] with ω hCω hDω hEω
  intro t htop
  obtain ⟨n,hn⟩ := hc ω t htop
  have htmin : min (τ n ω) t = t := min_eq_right hn.le
  have hbmin : min (τ n ω) (min b t) = min b t := min_eq_right ((min_le_right _ _).trans hn.le)
  have hamin : min (τ n ω) (min a t) = min a t := min_eq_right ((min_le_right _ _).trans hn.le)
  have he := hEω n t
  rw [← hDω n t,← hCω n (min b t),← hCω n (min a t),htmin,hbmin,hamin] at he
  exact he

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.elementary_local_integral_covariance
