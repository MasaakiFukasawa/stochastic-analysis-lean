import Chapter1IntervalSignedVariation
import Chapter1VanishingMesh
import Chapter2SignedRestriction
import Mathlib.Topology.UniformSpace.Dini

open MeasureTheory Set Filter
open scoped ENNReal Topology BigOperators
namespace Asakura.Chapter1Complete
set_option maxHeartbeats 3000000

lemma interval_cut_at (l r t : ℝ) (hlr : l≤r) :
    Ioc l r∩Iic t=Ioc (min l t) (min r t) := by
  ext x
  simp only [mem_inter_iff,mem_Ioc,mem_Iic]
  by_cases hl : l≤t
  · rw [min_eq_left hl]
    simp only [le_min_iff]
    tauto
  · have hr : t≤r := (le_of_not_ge hl).trans hlr
    rw [min_eq_right (le_of_not_ge hl),min_eq_right hr]
    constructor <;> intro h <;> linarith [h.1,h.2]

/-- A finite interval partition encoded by its nonempty cells, so that
refinement is the ordinary finite-partition order. -/
structure IntervalCells (a b : ℝ) where
  partition : Finpartition (univ : Set (Ioc a b))
  left : Set (Ioc a b) → ℝ
  right : Set (Ioc a b) → ℝ
  bounds : ∀ E∈partition.parts,a≤left E ∧ left E≤right E ∧ right E≤b
  cell : ∀ E∈partition.parts,E=Subtype.val ⁻¹' Ioc (left E) (right E)

lemma IntervalCells.measurable {a b : ℝ} (π : IntervalCells a b)
    (E : Set (Ioc a b)) (hE : E∈π.partition.parts) : MeasurableSet E := by
  rw [π.cell E hE]
  exact measurableSet_Ioc.preimage measurable_subtype_coe

noncomputable def intervalDiscreteVariation {a b : ℝ} (C : ℝ → ℝ)
    (π : IntervalCells a b) (t : ℝ) : ℝ :=
  ∑ E∈π.partition.parts,|C (min (π.right E) t)-C (min (π.left E) t)|

/-- This is the pointwise part of the manuscript's Stieltjes corollary.
The proof constructs dC, restricts it to time t, proves Borel generation
from the mesh bound, and applies the preceding conditional-expectation theorem. -/
theorem stieltjes_partition_convergence (a b : ℝ) (hab : a≤b) (C : ℝ → ℝ)
    (hC : BoundedVariationOn C (Icc a b))
    (hr : ∀ x∈Icc a b,ContinuousWithinAt C (Icc a b∩Ici x) x)
    (π : ℕ → IntervalCells a b) (href : Antitone (fun n => (π n).partition))
    (δ : ℕ → ℝ) (hδ : Tendsto δ atTop (𝓝 0))
    (hmesh : ∀ n,∀ E∈(π n).partition.parts,(π n).right E-(π n).left E≤δ n)
    {t : ℝ} (ht : t∈Icc a b) :
    Monotone (fun n => intervalDiscreteVariation C (π n) t) ∧
    Tendsto (fun n => intervalDiscreteVariation C (π n) t) atTop
      (𝓝 (eVariationOn C (Icc a t)).toReal) := by
  let ν := signedSubtype (intervalSigned a b hab C hC hr) (Ioc a b) measurableSet_Ioc
  let B : Set (Ioc a b) := Subtype.val ⁻¹' Iic t
  have hB : MeasurableSet B := measurableSet_Iic.preimage measurable_subtype_coe
  let κ : SignedMeasure (Ioc a b) := ν.restrict B
  have hcell n E (hE : E∈(π n).partition.parts) :
      κ E=C (min ((π n).right E) t)-C (min ((π n).left E) t) := by
    have hb := (π n).bounds E hE
    rw [show κ E=ν (E∩B) from VectorMeasure.restrict_apply ν hB ((π n).measurable E hE)]
    conv_lhs => rw [(π n).cell E hE]
    change ν (Subtype.val ⁻¹' Ioc ((π n).left E) ((π n).right E)∩Subtype.val ⁻¹' Iic t)=_
    rw [← preimage_inter,interval_cut_at _ _ _ hb.2.1]
    exact subtype_interval_signed_increment a b hab C hC hr le_rfl
      (le_min hb.1 ht.1) (min_le_min_right t hb.2.1) ((min_le_left _ _).trans hb.2.2)
  have hmass : κ.totalVariation.real univ=(eVariationOn C (Icc a t)).toReal := by
    rw [show κ.totalVariation=ν.totalVariation.restrict B from
      Asakura.Chapter2Complete.signed_totalVariation_restrict ν hB]
    rw [measureReal_def,Measure.restrict_apply MeasurableSet.univ,univ_inter,
      signed_subtype_variation,comap_subtype_coe_apply measurableSet_Ioc]
    have he : Subtype.val '' B=Ioc a t := by
      rw [show B=Subtype.val ⁻¹' Iic t from rfl,Subtype.image_preimage_coe]
      ext x
      simp only [mem_inter_iff,mem_Iic,mem_Ioc]
      constructor
      · rintro ⟨⟨hxa,hxb⟩,hxt⟩; exact ⟨hxa,hxt⟩
      · rintro ⟨hxa,hxt⟩; exact ⟨⟨hxa,hxt.trans ht.2⟩,hxt⟩
    rw [he]
    exact interval_signed_variation a b hab C hC hr ht
  have hd n E (hE : E∈(π n).partition.parts) (x : Ioc a b) (hx : x∈E)
      (y : Ioc a b) (hy : y∈E) : dist x y≤δ n := by
    rw [(π n).cell E hE] at hx hy
    change |(x:ℝ)-(y:ℝ)|≤δ n
    exact abs_le.mpr ⟨by linarith [hx.1,hx.2,hy.1,hy.2,hmesh n E hE],
      by linarith [hx.1,hx.2,hy.1,hy.2,hmesh n E hE]⟩
  have h := shrinking_partition_variation κ (fun n => (π n).partition)
    (fun n => (π n).measurable) href δ hδ hd
  have he n : (∑ E∈(π n).partition.parts,|κ E|)=intervalDiscreteVariation C (π n) t :=
    Finset.sum_congr rfl (fun E hE => congrArg abs (hcell n E hE))
  simpa only [he,hmass] using h

end Asakura.Chapter1Complete
