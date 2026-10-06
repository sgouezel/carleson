module

public import Carleson.ToMathlib.MeasureTheory.Function.LpSeminorm.Basic

/- This file upgrades Hölder's inequality to use enorm. -/

--Upstreaming status: ready

public section

open Filter ENNReal
open scoped Topology

namespace MeasureTheory

section Bilinear

variable {α E F G : Type*} {m : MeasurableSpace α}
  [TopologicalSpace E] [ENormedAddCommMonoid E] [TopologicalSpace F] [ENormedAddCommMonoid F]
  [TopologicalSpace G] [ENormedAddCommMonoid G] {μ : Measure α}
  {f : α → E} {g : α → F}

open NNReal

#check eLpNorm_le_eLpNorm_mul_eLpNorm_of_enorm

/-- Hölder's inequality, as an inequality on the `ℒp` seminorm for functions to `ℝ≥0∞`. -/
theorem eLpNorm_le_eLpNorm_mul_eLpNorm_of_enorm' {p q r : ℝ≥0∞} {f g : α → ℝ≥0∞}
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ)
    (hpqr : HolderTriple p q r) :
    eLpNorm (fun x => f x * g x) r μ ≤ eLpNorm f p μ * eLpNorm g q μ := by
  have W := eLpNorm_smul_le_mul_eLpNorm hf hg (hpqr := hpqr) (φ := f) (f := g)

#exit

/-- Hölder's inequality, as an inequality on the `ℒp` seminorm of an elementwise operation
`fun x => b (f x) (g x)`. -/
theorem eLpNorm_le_eLpNorm_mul_eLpNorm'_of_enorm {p q r : ℝ≥0∞} (hf : AEStronglyMeasurable f μ)
    (hg : AEStronglyMeasurable g μ) (b : E → F → G) (c : ℝ≥0)
    (h : ∀ᵐ x ∂μ, ‖b (f x) (g x)‖ₑ ≤ c * ‖f x‖ₑ * ‖g x‖ₑ) [hpqr : HolderTriple p q r] :
    eLpNorm (fun x => b (f x) (g x)) r μ ≤ c * eLpNorm f p μ * eLpNorm g q μ :=
  eLpNorm_le_eLpNorm_mul_eLpNorm_of_enorm hf hg b c h

open NNReal in
theorem MemLp.of_bilin' {p q r : ℝ≥0∞} {f : α → E} {g : α → F} (b : E → F → G) (c : ℝ≥0)
    (hf : MemLp f p μ) (hg : MemLp g q μ)
    (h : AEStronglyMeasurable (fun x ↦ b (f x) (g x)) μ)
    (hb : ∀ᵐ (x : α) ∂μ, ‖b (f x) (g x)‖ₑ ≤ c * ‖f x‖ₑ * ‖g x‖ₑ)
    [hpqr : HolderTriple p q r] :
    MemLp (fun x ↦ b (f x) (g x)) r μ := by
  refine ⟨h, ?_⟩
  apply (eLpNorm_le_eLpNorm_mul_eLpNorm_of_enorm hf.1 hg.1 b c hb (hpqr := hpqr)).trans_lt
  have := hf.2
  have := hg.2
  finiteness

end Bilinear

end MeasureTheory
