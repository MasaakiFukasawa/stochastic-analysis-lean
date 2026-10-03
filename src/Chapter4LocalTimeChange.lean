import Chapter4TimeChangedM2

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter4
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false

lemma shifted_stopping_increment_identity
    {T S : EReal} [Fact (0≤T)] [Fact (0≤S)]
    (φ : ClosedTime S → ClosedTime T) (ψ : ClosedTime T → ClosedTime S)
    (hφ : Monotone φ) (hadj : ∀ a t,ψ a≤t ↔ a≤φ t)
    (hsection : ∀ a,φ (ψ a)=max (φ ⊥) a)
    (X : ClosedTime T → ℝ) (a : ClosedTime T) (t : ClosedTime S) :
    X (φ (min (ψ a) t))-X (φ ⊥)=X (min a (φ t))-X (min a (φ ⊥)) := by
  by_cases ha : a≤φ ⊥
  · have hz : ψ a=⊥ := le_antisymm ((hadj a ⊥).mpr ha) bot_le
    simp only [hz,min_eq_left bot_le,min_eq_left ha,min_eq_left (ha.trans (hφ bot_le)),sub_self]
  · have ha' : φ ⊥≤a := le_of_not_ge ha
    rw [hφ.map_min,hsection,max_eq_right ha',min_eq_right ha']

/-- Localizing times are shifted together with the process. The bounded
stopped martingales themselves are time-changed, so no shifted martingale
property is supplied as an assumption. -/
theorem local_martingale_time_change_increment
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T S : EReal} [Fact (0≤T)] [Fact (0≤S)]
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (φ : ClosedTime S → ClosedTime T) (ψ : ClosedTime T → ClosedTime S)
    (hφ : Monotone φ) (hcφ : Continuous φ) (hψ : Monotone ψ)
    (hadj : ∀ a t,ψ a≤t ↔ a≤φ t)
    (hsection : ∀ a,φ (ψ a)=max (φ ⊥) a)
    (hφtop : ∀ t,t<⊤ → φ t<⊤) (hψtop : ∀ a,a<⊤ → ψ a<⊤)
    (X : ClosedTime T → Ω → ℝ) (hX : LocalMProcessWitness P F X) :
    LocalMProcessWitness P (fun t => F (φ t)) (fun t w => X (φ t) w-X (φ ⊥) w) := by
  obtain ⟨τ,hτ,hm,ht,hc,hb⟩ := hX.localizers
  refine ⟨fun n w => ψ (τ n w),?_,fun w => hψ.comp (hm w),fun n w => hψtop _ (ht n w),?_,?_⟩
  · intro n t
    have he : {w | ψ (τ n w)≤t}={w | τ n w≤φ t} := Set.ext (fun w => hadj _ _)
    rw [he]
    exact hτ n (φ t)
  · intro w t htop
    obtain ⟨n,hn⟩ := hc w (φ t) (hφtop t htop)
    refine ⟨n,lt_of_not_ge ?_⟩
    intro hnt
    exact (not_le_of_gt hn) ((hadj _ _).mp hnt)
  · intro n
    have hh := bounded_martingale_time_change_increment P F hF hle φ hφ hcφ
      (fun t w => X (min (τ n w) t) w) (hb n)
    convert hh using 1
    funext t w
    exact shifted_stopping_increment_identity φ ψ hφ hadj hsection (fun a => X a w) (τ n w) t

/-- The same shifted stopping times preserve local bounded variation. -/
theorem local_variation_time_change_increment
    {Ω : Type*} {T S : EReal} [Fact (0≤T)] [Fact (0≤S)]
    (F : ClosedTime T → MeasurableSpace Ω)
    (φ : ClosedTime S → ClosedTime T) (ψ : ClosedTime T → ClosedTime S)
    (hφ : Monotone φ) (hψ : Monotone ψ)
    (hadj : ∀ a t,ψ a≤t ↔ a≤φ t)
    (hsection : ∀ a,φ (ψ a)=max (φ ⊥) a)
    (hφtop : ∀ t,t<⊤ → φ t<⊤) (hψtop : ∀ a,a<⊤ → ψ a<⊤)
    (A : ClosedTime T → Ω → ℝ) (hA : LocalVariationWitness F A) :
    LocalVariationWitness (fun t => F (φ t)) (fun t w => A (φ t) w-A (φ ⊥) w) := by
  obtain ⟨τ,hτ,hm,ht,hc,hb⟩ := hA.localizers
  refine ⟨fun n w => ψ (τ n w),?_,fun w => hψ.comp (hm w),fun n w => hψtop _ (ht n w),?_,?_⟩
  · intro n t
    have he : {w | ψ (τ n w)≤t}={w | τ n w≤φ t} := Set.ext (fun w => hadj _ _)
    rw [he]
    exact hτ n (φ t)
  · intro w t htop
    obtain ⟨n,hn⟩ := hc w (φ t) (hφtop t htop)
    exact ⟨n,lt_of_not_ge (fun hn' => (not_le_of_gt hn) ((hadj _ _).mp hn'))⟩
  · intro n w
    obtain ⟨U,V,hU,hV,he⟩ := hb n w
    refine ⟨fun t => U (φ t)-U (φ ⊥),fun t => V (φ t)-V (φ ⊥),
      (fun _ _ h => sub_le_sub_right (hU (hφ h)) _),(fun _ _ h => sub_le_sub_right (hV (hφ h)) _),?_⟩
    intro t
    rw [shifted_stopping_increment_identity φ ψ hφ hadj hsection (fun a => A a w) (τ n w) t,he,he]
    ring

end Asakura.Chapter4
