import Chapter3MultivariateIto
import Chapter3ContinuousIntegralConstruction

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter3Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 2800000
set_option backward.isDefEq.respectTransparency false

theorem finite_sum_continuousAt {ι S : Type*} [TopologicalSpace S] (a : S)
    (s : Finset ι) (f : ι → S → ℝ) (hf : ∀ i ∈ s, ContinuousAt (f i) a) :
    ContinuousAt (fun x => ∑ i ∈ s, f i x) a := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (continuousAt_const : ContinuousAt (fun _ : S => (0:ℝ)) a)
  | @insert i s hi ih =>
    have hh := (hf i (Finset.mem_insert_self _ _)).add
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))
    convert hh using 1
    funext x
    simp [Finset.sum_insert hi]

/-- The C² Ito formula supplies semimartingale membership, including the
initial random constant and every finite-variation correction. -/
theorem ito_composition_decomposition
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T) {d : ℕ}
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (X A M I N : Fin d → ClosedTime T → Ω → ℝ)
    (C J : Fin d → Fin d → ClosedTime T → Ω → ℝ)
    (hX : ∀ i, SemimartingaleDecomposition P F (X i) (A i) (M i))
    (hC : ∀ i j, LocalCovarianceWitness P F (M i) (M j) (C i j))
    (f : (Fin d → ℝ) → ℝ) (hf : ContDiff ℝ 2 f)
    (c : ℕ → ℝ) (hc : ∀ k, 0 ≤ c k) (hcT : ∀ k, (c k:EReal) < T)
    (hcc : ∀ t, t < ⊤ → ∃ k, t < realTimeClamp (T := T) (c k))
    (hIN : ∀ i, SemimartingaleDecomposition P F (fun t ω => I i t ω+N i t ω) (I i) (N i))
    (hI : ∀ i, VariationIntegralFormula P c hc (A i)
      (fun z => fderiv ℝ f (fun k => X k (realTimeClamp z.2) z.1) (Pi.single i 1)) (I i))
    (hN : ∀ i, ItoCovarianceFormula P F (M i)
      (fun z => fderiv ℝ f (fun k => X k (realTimeClamp z.2) z.1) (Pi.single i 1)) (N i))
    (hJv : ∀ i j, AdaptedLocalVariationWitness F (J i j))
    (hJc : ∀ i j ω t, t < ⊤ → ContinuousAt (fun s => J i j s ω) t)
    (hJ : ∀ i j, VariationIntegralFormula P c hc (C i j)
      (fun z => fderiv ℝ (fderiv ℝ f) (fun k => X k (realTimeClamp z.2) z.1)
        (Pi.single i 1) (Pi.single j 1)) (J i j)) :
    ∃ B L, SemimartingaleDecomposition P F (fun t ω => f (fun i => X i t ω)) B L ∧
      ∀ᵐ ω ∂P, ∀ t, t < ⊤ → L t ω = ∑ i, N i t ω := by
  classical
  let Y := fun t ω => f (fun i => X i t ω)
  have hXa i t (ht : t < ⊤) : Measurable[F t] (X i t) := by
    have he : X i t = fun ω => A i t ω+M i t ω := funext ((hX i).decomposition t ht)
    rw [he]
    exact ((hX i).variation.adapted t ht).add ((hX i).martingale.adapted P F t ht)
  have hYa t (ht : t < ⊤) : Measurable[F t] (Y t) := by
    letI : MeasurableSpace Ω := F t
    exact hf.continuous.measurable.comp (Measurable.of_eval (fun i => hXa i t ht))
  have hYc ω t (ht : t < ⊤) : ContinuousAt (fun s => Y s ω) t :=
    hf.continuous.continuousAt.comp (continuousAt_pi.mpr (fun i => (hX i).continuous ω t ht))
  let B := fun t ω => Y ⊥ ω+(∑ i, I i t ω)+(1/2:ℝ)*(∑ i, ∑ j, J i j t ω)
  let L := fun t ω => Y t ω-B t ω
  have hBv : AdaptedLocalVariationWitness F B := by
    have h0 := continuous_increasing_adapted_variation hT F hF (fun _ ω => Y ⊥ ω)
      (fun t _ => (hYa ⊥ hT).mono (hF bot_le) le_rfl)
      (fun _ => monotoneOn_const) (fun _ _ _ => continuousAt_const)
    have h1 := adapted_variation_finset_sum hT F hF Finset.univ I (fun i _ => (hIN i).variation)
    have h2 := adapted_variation_finset_sum hT F hF Finset.univ (fun i t ω => ∑ j, J i j t ω)
      (fun i _ => adapted_variation_finset_sum hT F hF Finset.univ (J i) (fun j _ => hJv i j))
    exact (h0.add h1 hF).add (h2.smul (1/2)) hF
  have hBc ω t (ht : t < ⊤) : ContinuousAt (fun s => B s ω) t :=
    (continuousAt_const.add (finite_sum_continuousAt t Finset.univ (fun i s => I i s ω) (fun i _ => (hIN i).variation_continuous P F ω t ht))).add
      ((finite_sum_continuousAt t Finset.univ (fun i s => ∑ j, J i j s ω) (fun i _ => finite_sum_continuousAt t Finset.univ (fun j s => J i j s ω) (fun j _ => hJc i j ω t ht))).const_mul _)
  have hsum := local_process_finset_sum P F hF hle Finset.univ N (fun i _ => (hIN i).martingale)
    (zero_local_process P hT F)
  have hIto := multivariate_ito_formula P hT F hF hle hnull X A M (fun i t ω => I i t ω+N i t ω)
    C J hX hC f hf c hc hcT hcc (fun i => ⟨I i,N i,hIN i,hI i,hN i⟩) hJ
  have he : ∀ᵐ ω ∂P, ∀ t, t < ⊤ → Y t ω = B t ω+(∑ i, N i t ω) := by
    filter_upwards [hIto] with ω hω
    intro t ht
    have hh := hω t ht
    rw [Finset.sum_add_distrib] at hh
    dsimp only [Y,B]
    linarith
  obtain ⟨hD,hLe⟩ := semimartingale_of_ae_decomposition P F hF Y B _ hYa hYc hBv hBc hsum he
  exact ⟨B,L,hD,hLe.mono (fun ω hω t ht => (hω t ht).symm)⟩

end Asakura.Chapter3Complete
#print axioms Asakura.Chapter3Complete.ito_composition_decomposition

#print axioms Asakura.Chapter3Complete.finite_sum_continuousAt
