module

public import Carleson.ToMathlib.ENorm
public import Carleson.ToMathlib.MeasureTheory.Measure.AEMeasurable
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

--Upstreaming status: ready

public section

noncomputable section

open scoped NNReal ENNReal

variable {α ε : Type*} {m : MeasurableSpace α} [ENorm ε] {f : α → ε}

namespace MeasureTheory

lemma eLpNormEssSup_congr_measure {μ ν : Measure α} (h : ae ν = ae μ) :
    eLpNormEssSup f ν = eLpNormEssSup f μ := by
  unfold eLpNormEssSup essSup
  congr 1

lemma eLpNormEssSup_withDensity {μ : Measure α} {d : α → ℝ≥0∞} (hd : AEMeasurable d μ)
  (hd' : ∀ᵐ (x : α) ∂μ, d x ≠ 0) :
    eLpNormEssSup f (μ.withDensity d) = eLpNormEssSup f μ := by
  apply eLpNormEssSup_congr_measure
  apply le_antisymm
  · rw [Measure.ae_le_iff_absolutelyContinuous]
    apply withDensity_absolutelyContinuous
  · rw [Measure.ae_le_iff_absolutelyContinuous]
    apply withDensity_absolutelyContinuous' hd  hd'

lemma eLpNormEssSup_nnreal_scale_constant' {f : ℝ≥0 → ℝ≥0∞} {a : ℝ≥0} (h : a ≠ 0) :
    eLpNormEssSup (fun x ↦ f (a * x)) volume = eLpNormEssSup f volume := by
  let g := (Homeomorph.smulOfNeZero a h : ℝ≥0 ≃ₜ ℝ≥0).toMeasurableEquiv
  have : eLpNormEssSup (fun x ↦ f (a * x)) volume = eLpNormEssSup (f ∘ g) volume := rfl
  rw [this, ← MeasurableEmbedding.eLpNormEssSup_map_measure g.measurableEmbedding]
  apply eLpNormEssSup_congr_measure
  simp only [Homeomorph.toMeasurableEquiv_coe, Homeomorph.smulOfNeZero_apply, smul_eq_mul, g,
    NNReal.map_volume_mul_left h]
  apply Measure.ae_ennreal_smul_measure_eq (by simpa)

lemma eLpNorm_withDensity_scale_constant' {f : ℝ≥0 → ℝ≥0∞} {p : ℝ≥0∞} {a : ℝ≥0} (h : a ≠ 0) :
    eLpNorm (fun t ↦ f (a * t)) p (volume.withDensity (fun (t : ℝ≥0) ↦ t⁻¹))
      = eLpNorm f p (volume.withDensity (fun (t : ℝ≥0) ↦ t⁻¹)) := by
  let g := (Homeomorph.smulOfNeZero a h : ℝ≥0 ≃ₜ ℝ≥0).toMeasurableEquiv
  have : (fun t ↦ f (a * t)) = f ∘ g := rfl
  simp_rw [this]
  rw [← MeasurableEmbedding.eLpNorm_map_measure g.measurableEmbedding]
  congr 1
  ext s hs
  simp only [g.measurable, hs, Measure.map_apply, MeasurableEquiv.measurableSet_preimage,
    withDensity_apply]
  rw [← lintegral_indicator (g.measurable hs)]
  have A x : (g ⁻¹' s).indicator (fun (t : ℝ≥0) ↦ ((↑t)⁻¹ : ℝ≥0∞)) x =
      a * (s.indicator (fun (t : ℝ≥0) ↦ ((↑t)⁻¹ : ℝ≥0∞))) (a * x) := by
    simp only [Set.indicator, Set.mem_preimage]
    by_cases hx : a * x ∈ s
    · have : x ∈ ⇑g ⁻¹' s := hx
      simp only [this, ↓reduceIte, hx, ENNReal.coe_mul]
      rw [ENNReal.mul_inv (by simp [h]) (by simp), ← mul_assoc,
        ENNReal.mul_inv_cancel (by simp [h]) (by simp), one_mul]
    · have : ¬ (x ∈ ⇑g ⁻¹' s) := hx
      simp [hx, this]
  simp only [A]
  rw [lintegral_const_mul _ (by fun_prop), lintegral_nnreal_scale_constant' h,
    lintegral_indicator hs]

end MeasureTheory
