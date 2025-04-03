import Carleson.TileStructure
import Mathlib.Topology.MetricSpace.ProperSpace.Lemmas

/-! This should roughly contain the contents of chapter 8. -/

open scoped ShortVariables
variable {X : Type*} {a : ℕ} {q : ℝ} {K : X → X → ℂ} {σ₁ σ₂ : X → ℤ} {F G : Set X}
  [MetricSpace X] [ProofData a q K σ₁ σ₂ F G]

noncomputable section

open Set MeasureTheory Metric Function Complex Bornology TileStructure
open scoped NNReal ENNReal ComplexConjugate

/-- `cutoff R t x y` is `L(x, y)` in the proof of Lemma 8.0.1. -/
def cutoff (R t : ℝ) (x y : X) : ℝ :=
  max 0 (1 - dist x y / (t * R))

variable {R t : ℝ} {x y : X}

lemma cutoff_nonneg : 0 ≤ cutoff R t x y := by simp [cutoff]

lemma cutoff_comm : cutoff R t x y = cutoff R t y x := by
  unfold cutoff
  simp_rw [dist_comm x y]

lemma cutoff_Lipschitz (hR : 0 < R) (ht : 0 < t) :
    LipschitzWith ⟨(1 / (t * R)), by positivity⟩ (fun y ↦ cutoff R t x y) := by
  apply LipschitzWith.const_max
  apply LipschitzWith.of_le_add_mul
  intro a b
  simp only [one_div, NNReal.coe_mk, tsub_le_iff_right, div_eq_inv_mul, mul_one]
  have : (t * R) ⁻¹ * dist x b ≤ (t * R)⁻¹ * (dist x a + dist a b) := by
    gcongr
    exact dist_triangle _ _ _
  linarith

@[fun_prop]
lemma cutoff_continuous (hR : 0 < R) (ht : 0 < t) : Continuous (fun y ↦ cutoff R t x y) :=
  (cutoff_Lipschitz hR ht (X := X)).continuous

/-- `cutoff R t x` is measurable in `y`. -/
@[fun_prop]
lemma cutoff_measurable (hR : 0 < R) (ht : 0 < t) : Measurable (fun y ↦ cutoff R t x y) :=
  (cutoff_continuous hR ht).measurable

lemma cutoff_eq_zero (hR : 0 < R) (ht : 0 < t) {x y : X} (hy : y ∉ ball x (t * R)) :
    cutoff R t x y = 0 := by
  simp only [mem_ball, dist_comm, not_lt] at hy
  simp only [cutoff, sup_eq_left, tsub_le_iff_right, zero_add]
  rwa [one_le_div (by positivity)]

lemma hasCompactSupport_cutoff [ProperSpace X] (hR : 0 < R) (ht : 0 < t) {x : X} :
    HasCompactSupport (fun y ↦ cutoff R t x y) := by
  apply HasCompactSupport.intro (isCompact_closedBall x (t * R))
  intro y hy
  apply cutoff_eq_zero hR ht
  contrapose! hy
  exact ball_subset_closedBall hy

lemma integrable_cutoff (hR : 0 < R) (ht : 0 < t) {x : X} :
    Integrable (fun y ↦ cutoff R t x y) :=
  (cutoff_continuous hR ht).integrable_of_hasCompactSupport
    (hasCompactSupport_cutoff hR ht)

lemma integrable_cutoff_mul {z : X} (hR : 0 < R) (ht : 0 < t) {x : X} {ϕ : X → ℂ}
    (hc : Continuous ϕ) (hϕ : ϕ.support ⊆ ball z R) :
    Integrable (fun y ↦ cutoff R t x y * ϕ y) := by
  apply Continuous.integrable_of_hasCompactSupport
  · apply Continuous.mul
    · have := cutoff_continuous hR ht (x := x)
      fun_prop
    · exact hc
  · apply HasCompactSupport.mul_left
    apply HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall z R)
    apply hϕ.trans ball_subset_closedBall

-- Is this useful for mathlib? neither exact? nor aesop can prove this. Same for the next lemma.
lemma leq_of_max_neq_left {a b : ℝ} (h : max a b ≠ a) : a < b := by
  by_contra! h'
  exact h (max_eq_left h')

lemma leq_of_max_neq_right {a b : ℝ} (h : max a b ≠ b) : b < a := by
  by_contra! h'
  exact h (max_eq_right h')

/-- Equation 8.0.4 from the blueprint -/
lemma aux_8_0_4 (hR : 0 < R) (ht : 0 < t) (h : cutoff R t x y ≠ 0) : y ∈ ball x (t * R) := by
  contrapose! h
  exact cutoff_eq_zero hR ht h

lemma aux_8_0_5 (hR : 0 < R) (ht : 0 < t) (h : y ∈ ball x (2⁻¹ * t * R)) :
    2⁻¹ ≤ cutoff R t x y := by
  rw [mem_ball', mul_assoc] at h
  have : dist x y / (t * R) < 2⁻¹ := (div_lt_iff₀ (by positivity)).mpr h
  calc 2 ⁻¹
    _ ≤ 1 - dist x y / (t * R) := by
      norm_num at *; linarith only [h, this]
    _ ≤ cutoff R t x y := le_max_right _ _

lemma aux_8_0_6 (hR : 0 < R) (ht : 0 < t) :
    2⁻¹ * volume.real (ball x (2⁻¹ * t * R)) ≤ ∫ y, cutoff R t x y := by
  calc 2 ⁻¹ * volume.real (ball x (2⁻¹ * t * R))
    _ = ∫ y in ball x (2⁻¹ * t * R), 2⁻¹ := by
      rw [setIntegral_const, mul_comm]
      rfl
    _ ≤ ∫ y in (ball x (2⁻¹ * t * R)), cutoff R t x y := by
      apply setIntegral_mono_on
      · apply integrableOn_const.2
        right
        exact measure_ball_lt_top
      · apply (integrable_cutoff hR ht).integrableOn
      · exact measurableSet_ball
      · intro y' hy'
        exact aux_8_0_5 hy' (hR := hR) (ht := ht)
    _ ≤ ∫ y, cutoff R t x y := by
      apply setIntegral_le_integral (integrable_cutoff hR ht)
      filter_upwards with x using (by simp [cutoff])

lemma integral_cutoff_pos {R t : ℝ} (hR : 0 < R) (ht : 0 < t) : 0 < ∫ y, cutoff R t x y := by
  apply lt_of_lt_of_le _ (aux_8_0_6 hR ht)
  apply mul_pos (by positivity)
  apply measure_real_ball_pos
  positivity

/-- The constant occurring in Lemma 8.0.1. -/
def C8_0_1 (a : ℝ) (t : ℝ≥0) : ℝ≥0 := ⟨2 ^ (4 * a) * t ^ (- (a + 1)), by positivity⟩

/-- `ϕ ↦ \tilde{ϕ}` in the proof of Lemma 8.0.1. -/
def holderApprox (R t : ℝ) (ϕ : X → ℂ) (x : X) : ℂ :=
  (∫ y, cutoff R t x y * ϕ y) / (∫ y, cutoff R t x y)

lemma integral_mul_holderApprox {R t : ℝ} (hR : 0 < R) (ht : 0 < t) (ϕ : X → ℂ) :
    (∫ y, cutoff R t x y) * holderApprox R t ϕ x = ∫ y, cutoff R t x y * ϕ y := by
  rw [holderApprox, mul_div_cancel₀]
  simp only [ne_eq, ofReal_eq_zero]
  apply ne_of_gt
  exact integral_cutoff_pos hR ht

-- This surely exists in mathlib; how is it named?
lemma foo {φ : X → ℂ} (hf : ∫ x, φ x ≠ 0) : ∃ z, φ z ≠ 0 := by
  by_contra! h
  exact hf (by simp [h])

theorem exists_pos_forall_lt_dist {X : Type*} [PseudoMetricSpace X] {s t : Set X}
      (hs : IsCompact s) (ht : IsClosed t) (hst : Disjoint s t) :
    ∃ r : ℝ, 0 < r ∧ ∀ x ∈ s, ∀ y ∈ t, r < dist x y := by
  rcases EMetric.exists_pos_forall_lt_edist hs ht hst with ⟨r, r_pos, hr⟩
  refine ⟨r, r_pos, fun x hx y hy ↦ ?_⟩
  specialize hr x hx y hy
  rw [← ENNReal.ofReal_lt_ofReal_iff_of_nonneg NNReal.zero_le_coe]
  convert hr
  · simp
  · simp [edist_dist]

lemma support_holderApprox_subset_aux {z : X} {R R' t : ℝ} (hR : 0 < R)
    {ϕ : X → ℂ} (hϕ : ϕ.support ⊆ ball z R') (ht : t ∈ Ioc (0 : ℝ) 1) :
    support (holderApprox R t ϕ) ⊆ ball z (R + R') := by
  intro x hx
  choose y hy using foo (left_ne_zero_of_mul hx)
  have : x ∈ ball y (t * R) := by
    apply aux_8_0_4 hR ht.1
    rw [cutoff_comm]
    simpa using left_ne_zero_of_mul hy
  have h : x ∈ ball y R := by
    refine Set.mem_of_mem_of_subset this ?_
    nth_rw 2 [← one_mul R]
    gcongr
    exact ht.2
  calc dist x z
    _ ≤ dist x y + dist y z := dist_triangle x y z
    _ < R + R' := add_lt_add h (hϕ (right_ne_zero_of_mul hy))

/-- Part of Lemma 8.0.1. -/
lemma support_holderApprox_subset {z : X} {R t : ℝ} (hR : 0 < R)
    (ϕ : X → ℂ) (hϕ : ϕ.support ⊆ ball z R) (ht : t ∈ Ioc (0 : ℝ) 1) :
    support (holderApprox R t ϕ) ⊆ ball z (2 * R) := by
  convert support_holderApprox_subset_aux hR hϕ ht using 2
  ring

/-- Part of Lemma 8.0.1. -/
lemma tsupport_holderApprox_subset {z : X} {R t : ℝ} (hR : 0 < R)
    {ϕ : X → ℂ} (hϕ : tsupport ϕ ⊆ ball z R) (ht : t ∈ Ioc (0 : ℝ) 1) :
    tsupport (holderApprox R t ϕ) ⊆ ball z (2 * R) := by
  rcases exists_pos_lt_subset_ball hR (isClosed_tsupport ϕ) hϕ with ⟨R', R'_pos, hR'⟩
  have A : support (holderApprox R t ϕ) ⊆ ball z (R + R') :=
    support_holderApprox_subset_aux hR ((subset_tsupport _).trans hR') ht
  have : tsupport (holderApprox R t ϕ) ⊆ closedBall z (R + R') :=
    (closure_mono A).trans closure_ball_subset_closedBall
  apply this.trans (closedBall_subset_ball ?_)
  linarith [R'_pos.2]

open Filter

/-- Part of Lemma 8.0.1: Equation (8.0.1).
Note that the norm `||ϕ||_C^τ` is normalized by definition, i.e., it is `R ^ τ` times the best
Hölder constant of `ϕ`, so the Lean statement corresponds to the blueprint statement.
We assume that `ϕ` is globally Hölder for simplicity, but this is equivalent to being
Hölder on `ball z R` as `ϕ` is supported there.
-/
lemma dist_holderApprox_le {z : X} {R t : ℝ} (hR : 0 < R) {C : ℝ≥0} (ht : 0 < t)
    (ϕ : X → ℂ) (hϕ : tsupport ϕ ⊆ ball z R) (h2ϕ : HolderOnWith C nnτ ϕ (ball z R)) (x : X) :
    dist (ϕ x) (holderApprox R t ϕ x) ≤ t ^ τ * (R ^ τ * C) := by
  have : (∫ y, cutoff R t x y * ϕ x) / (∫ y, (cutoff R t x y : ℂ)) = ϕ x := by
    rw [integral_mul_right, mul_div_cancel_left₀]
    simpa only [ne_eq, ofReal_eq_zero, integral_complex_ofReal] using (integral_cutoff_pos hR ht).ne'
  rw [dist_eq_norm, ← this, holderApprox, integral_complex_ofReal, ← sub_div,
    ← integral_sub]; rotate_left
  · apply (integrable_cutoff hR ht).ofReal.mul_const
  · apply integrable_cutoff_mul hR ht (h2ϕ.continuous (nnτ_pos X)) hϕ
  rw [norm_div, norm_real, div_le_iff₀]; swap
  · exact ((integral_cutoff_pos hR ht)).trans_le (le_abs_self _)
  calc
    ‖∫ y, cutoff R t x y * ϕ x - cutoff R t x y * ϕ y‖
  _ = ‖∫ y, cutoff R t x y * (ϕ x - ϕ y)‖ := by simp only [mul_sub]
  _ ≤ ∫ y, ‖cutoff R t x y * (ϕ x - ϕ y)‖ := norm_integral_le_integral_norm _
  _ ≤ ∫ y, cutoff R t x y * (C * (t * R) ^ τ) := by
    apply integral_mono_of_nonneg
    · filter_upwards with y using (by positivity)
    · apply (integrable_cutoff hR ht).mul_const
    filter_upwards with y
    rcases le_total (dist x y) (t * R) with hy | hy
    -- Case 1: |x - y| ≤ t * R, then cutoff is non-negative.
    · simp only [norm_mul, norm_real, Real.norm_eq_abs, defaultτ, norm_real,
        _root_.abs_of_nonneg cutoff_nonneg]
      gcongr
      · exact cutoff_nonneg
      rw [← dist_eq_norm]
      exact h2ϕ.dist_le_of_le hy
    -- Case 2: |x - y| > t * R, and cutoff is zero.
    · have : cutoff R t x y = 0 := by
        simp only [cutoff, sup_eq_left, tsub_le_iff_right, zero_add]
        rwa [one_le_div₀ (by positivity)]
      simp [this]
  _ = (t * R) ^τ * C * ∫ y, cutoff R t x y := by
    rw [integral_mul_right]
    ring
  _ ≤ (t * R) ^ τ * C * ‖∫ (x_1 : X), cutoff R t x x_1‖ := by
    gcongr
    exact Real.le_norm_self _
  _ = t ^ τ * (R ^ τ * C) * ‖∫ (x_1 : X), cutoff R t x x_1‖ := by
    rw [Real.mul_rpow ht.le hR.le]
    ring

/-- Part of Lemma 8.0.1: sup norm control in Equation (8.0.2). Note that it only uses the sup
norm of `ϕ`, no need for a Hölder control. -/
lemma holderApprox_le {R t : ℝ} (hR : 0 < R) {C : ℝ≥0} (ht : 0 < t)
    {ϕ : X → ℂ} (hC : ∀ x, ‖ϕ x‖ ≤ C) (x : X) :
    ‖holderApprox R t ϕ x‖ ≤ C := by
  rw [holderApprox, norm_div, norm_real, Real.norm_eq_abs]
  apply div_le_of_le_mul₀ (by positivity) (by positivity)
  apply (norm_integral_le_integral_norm _).trans
  rw [abs_of_pos (integral_cutoff_pos hR ht), ← integral_mul_left]
  apply integral_mono_of_nonneg
  · apply Eventually.of_forall (fun x ↦ by positivity)
  · apply (integrable_cutoff hR ht).const_mul
  apply Eventually.of_forall (fun y ↦ ?_)
  simp only [Complex.norm_mul, norm_real, Real.norm_eq_abs, cutoff_nonneg, abs_of_nonneg,
    mul_comm (C : ℝ)]
  gcongr
  · apply cutoff_nonneg
  · exact hC y

/-- Auxiliary lemma: part of the Lipschitz control in Equation (8.0.2), when the distance between
the points is at most `R`. -/
lemma norm_holderApprox_sub_le_aux {z : X} {R t : ℝ} (hR : 0 < R) (ht : 0 < t) (h't : t ≤ 1)
    {C : ℝ≥0} {ϕ : X → ℂ} (hc : Continuous ϕ) (hϕ : ϕ.support ⊆ ball z R)
    (hC : ∀ x, ‖ϕ x‖ ≤ C) {x x' : X} (h : dist x x' < R) :
    ‖holderApprox R t ϕ x' - holderApprox R t ϕ x‖ ≤
      2⁻¹ * 2 ^ (4 * a) * t ^ (-1 - a : ℝ) * C * dist x x' / (2 * R) := by
  have M : (2⁻¹ * volume.real (ball x (2⁻¹ * t * R))) *
      ‖holderApprox R t ϕ x' - holderApprox R t ϕ x‖ ≤
        2 * C * ∫ y, |cutoff R t x y - cutoff R t x' y| :=
    calc
      (2⁻¹ * volume.real (ball x (2⁻¹ * t * R))) * ‖holderApprox R t ϕ x' - holderApprox R t ϕ x‖
    _ ≤ (∫ y, cutoff R t x y) * ‖holderApprox R t ϕ x' - holderApprox R t ϕ x‖ := by
      gcongr
      apply aux_8_0_6 hR ht
    _ = ‖(∫ y, cutoff R t x y) * (holderApprox R t ϕ x' - holderApprox R t ϕ x)‖ := by
      rw [norm_mul, norm_real, Real.norm_eq_abs,
        abs_of_pos (integral_cutoff_pos hR ht)]
    _ = ‖((∫ y, cutoff R t x y)  - (∫ y, cutoff R t x' y)) * holderApprox R t ϕ x'
          + ((∫ y, cutoff R t x' y) * holderApprox R t ϕ x'
          - (∫ y, cutoff R t x y) * holderApprox R t ϕ x)‖ := by congr 1; ring
    _ ≤ ‖(∫ y, cutoff R t x y - cutoff R t x' y) * holderApprox R t ϕ x'‖
        + ‖(∫ y, cutoff R t x' y) * holderApprox R t ϕ x'
          - (∫ y, cutoff R t x y) * holderApprox R t ϕ x‖ := by
      rw [integral_sub (integrable_cutoff hR ht) (integrable_cutoff hR ht), ofReal_sub]
      exact norm_add_le _ _
    _ = ‖∫ y, cutoff R t x y - cutoff R t x' y‖ * ‖holderApprox R t ϕ x'‖ +
          ‖(∫ y, cutoff R t x' y * ϕ y) - (∫ y, cutoff R t x y * ϕ y)‖ := by
      simp [norm_mul, integral_mul_holderApprox hR ht]
    _ ≤ (∫ y, ‖cutoff R t x y - cutoff R t x' y‖) * C +
          ‖(∫ y, (cutoff R t x' y - cutoff R t x y) * ϕ y)‖ := by
      gcongr
      · apply norm_integral_le_integral_norm
      · apply holderApprox_le hR ht hC
      · apply le_of_eq
        rw [← integral_sub]
        · simp [sub_mul]
        · apply integrable_cutoff_mul hR ht hc hϕ
        · apply integrable_cutoff_mul hR ht hc hϕ
    _ ≤ (∫ y, ‖cutoff R t x y - cutoff R t x' y‖) * C +
          ∫ y, ‖cutoff R t x' y - cutoff R t x y‖ * C := by
      gcongr
      apply (norm_integral_le_integral_norm _).trans
      apply integral_mono_of_nonneg
      · apply Eventually.of_forall (fun x ↦ by positivity)
      · apply ((integrable_cutoff hR ht).sub (integrable_cutoff hR ht)).norm.mul_const
      · apply Eventually.of_forall (fun y ↦ ?_)
        simp only [← ofReal_sub, norm_mul, norm_real, Real.norm_eq_abs]
        gcongr
        apply hC
    _ = 2 * C * ∫ y, |cutoff R t x y - cutoff R t x' y| := by
      simp only [Real.norm_eq_abs, integral_mul_right, abs_sub_comm (cutoff R t x' _)]
      ring
  have N : ∫ y, |cutoff R t x y - cutoff R t x' y| ≤
      volume.real (ball x (2 * R)) * dist x x' / (t * R) := calc
    ∫ y, |cutoff R t x y - cutoff R t x' y|
    _ = ∫ y in ball x (t * R) ∪ ball x' (t * R), |cutoff R t x y - cutoff R t x' y| := by
      apply (setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy ↦ ?_)).symm
      simp only [mem_union, not_or] at hy
      simp [cutoff_eq_zero hR ht hy.1, cutoff_eq_zero hR ht hy.2]
    _ ≤ ∫ y in ball x (t * R) ∪ ball x' (t * R), dist x x' / (t * R) := by
      apply integral_mono_of_nonneg (Eventually.of_forall (fun y ↦ by positivity))
      · apply integrableOn_const.2
        simp [measure_union_lt_top_iff, measure_ball_lt_top]
      apply Eventually.of_forall (fun y ↦ ?_)
      simp only [cutoff_comm (y := y)]
      simpa [div_eq_inv_mul, dist_eq_norm] using (cutoff_Lipschitz hR ht (x := y)).dist_le_mul x x'
    _ = volume.real (ball x (t * R) ∪ ball x' (t * R)) * dist x x' / (t * R) := by
      simp [Measure.real, mul_div_assoc]
    _ ≤ volume.real (ball x (2 * R)) * dist x x' / (t * R) := by
      gcongr
      · apply measure_ball_lt_top.ne
      apply union_subset
      · apply ball_subset_ball
        gcongr
        linarith
      · apply ball_subset_ball'
        rw [dist_comm]
        nlinarith
  calc
    ‖holderApprox R t ϕ x' - holderApprox R t ϕ x‖
  _ ≤ (2 * C * ∫ y, |cutoff R t x y - cutoff R t x' y|)
        / (2⁻¹ * volume.real (ball x (2⁻¹ * t * R))) := by
    rwa [← le_div_iff₀'] at M
    apply mul_pos (by positivity)
    apply measure_real_ball_pos
    positivity
  _ ≤ (2 * C * (volume.real (ball x (2 * R)) * dist x x' / (t * R))) /
      (2⁻¹ * volume.real (ball x (2⁻¹ * t * R))) := by gcongr
  _ ≤ (2 * C * (((defaultA a) * (4 ⁻¹ * t) ^ (- Real.logb 2 (defaultA a)) *
        volume.real (ball x ((4⁻¹ * t) * (2 * R)))) * dist x x' / (t * R))) /
      (2⁻¹ * volume.real (ball x (2⁻¹ * t * R))) := by
    gcongr
    exact measure_ball_le_same'' (μ := (volume : Measure X)) (t := 4⁻¹ * t) (r := 2 * R) x
      (by positivity) (by linarith)
  _ = 2⁻¹ * 16 * C * (defaultA a) * t⁻¹ * (4 ⁻¹ * t) ^ (- Real.logb 2 (defaultA a)) * (dist x x' / (2 * R)) *
        (volume.real (ball x ((4⁻¹ * t) * (2 * R))) / volume.real (ball x (2⁻¹ * t * R))) := by
    ring
  _ = 2⁻¹ * 16 * C * 2 ^ a * t⁻¹ * (4 ⁻¹ * t) ^ (- a : ℝ) * (dist x x' / (2 * R)) := by
    have : volume.real (ball x ((4⁻¹ * t) * (2 * R))) / volume.real (ball x (2⁻¹ * t * R)) = 1 := by
      rw [show (4⁻¹ * t) * (2 * R) = 2⁻¹ * t * R by ring, div_self]
      apply ne_of_gt
      apply measure_real_ball_pos
      positivity
    simp [defaultA, ← Real.rpow_natCast, this]
  _ ≤ 2⁻¹ * 2 ^ a * C * 2 ^ a * t⁻¹ * (4 ⁻¹ * t) ^ (- a : ℝ) * (dist x x' / (2 * R)) := by
    gcongr
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num]
    apply pow_le_pow_right₀ (by norm_num)
    apply le_trans (by norm_num) (four_le_a X)
  _ = 2⁻¹ * 2 ^ (a + a + 2 * a) * t ^ (- (1+a) : ℝ) * C * (dist x x' / (2 * R)) := by
    simp only [pow_add, neg_add_rev]
    rw [Real.mul_rpow (by norm_num) ht.le,
      Real.rpow_neg (by norm_num), Real.inv_rpow (by norm_num), inv_inv, Real.rpow_add ht,
      Real.rpow_neg_one, Real.rpow_natCast, pow_mul, show (2 : ℝ) ^ 2 = 4 by norm_num]
    ring
  _ = 2⁻¹ * 2 ^ (4 * a) * t ^ (-1 - a : ℝ) * C * (dist x x' / (2 * R)) := by
    congr <;> ring
  _ = _ := by ring

/-- Part of Lemma 8.0.1: Lipschitz norm control in Equation (8.0.2). Note that it only uses the sup
norm of `ϕ`, no need for a Hölder control. -/
lemma norm_holderApprox_sub_le {z : X} {R t : ℝ} (hR : 0 < R) (ht : 0 < t) (h't : t ≤ 1)
    {C : ℝ≥0} {ϕ : X → ℂ} (hc : Continuous ϕ) (hϕ : ϕ.support ⊆ ball z R)
    (hC : ∀ x, ‖ϕ x‖ ≤ C) {x x' : X} :
    ‖holderApprox R t ϕ x - holderApprox R t ϕ x'‖ ≤
      2⁻¹ * 2 ^ (4 * a) * t ^ (-1 - a : ℝ) * C * dist x x' / (2 * R) := by
  rcases lt_or_le (dist x x') R with hx | hx
  · rw [norm_sub_rev]
    exact norm_holderApprox_sub_le_aux hR ht h't hc hϕ hC hx
  calc
    ‖holderApprox R t ϕ x - holderApprox R t ϕ x'‖
  _ ≤ ‖holderApprox R t ϕ x‖ + ‖holderApprox R t ϕ x'‖ := norm_sub_le _ _
  _ ≤ C + C := by
    gcongr
    · exact holderApprox_le hR ht hC x
    · exact holderApprox_le hR ht hC x'
  _ = 2⁻¹ * 2 ^ 3 * 1 * C * 2⁻¹ := by ring
  _ ≤ 2⁻¹ * 2 ^ (4 * a) * t ^ (-1 - a : ℝ) * C * (dist x x' / (2 * R)) := by
    gcongr
    · exact one_le_two
    · have : 4 ≤ a := four_le_a X
      linarith
    · apply Real.one_le_rpow_of_pos_of_le_one_of_nonpos ht h't
      have : (4 : ℝ) ≤ a := mod_cast (four_le_a X)
      linarith
    · simp only [inv_eq_one_div]
      apply (div_le_div_iff₀ (by norm_num) (by positivity)).2
      linarith
  _ = _ := by ring

lemma iLipENorm_holderApprox' {z : X} {R t : ℝ} (ht : 0 < t) (h't : t ≤ 1)
    {C : ℝ≥0} {ϕ : X → ℂ} (hc : Continuous ϕ) (hϕ : ϕ.support ⊆ ball z R)
    (hC : ∀ x, ‖ϕ x‖ ≤ C) :
    iLipENorm (holderApprox R t ϕ) z (2 * R) ≤
      2 ^ (4 * a) * (ENNReal.ofReal t) ^ (-1 - a : ℝ) * C := by
  let C' : ℝ≥0 := 2 ^ (4 * a) * (t.toNNReal) ^ (-1 - a : ℝ) * C
  have : 2 ^ (4 * a) * (ENNReal.ofReal t) ^ (-1 - a : ℝ) * C = C' := by
    simp only [ENNReal.coe_mul, ENNReal.coe_pow, ENNReal.coe_ofNat, C', ENNReal.ofReal]
    congr
    rw [ENNReal.coe_rpow_of_ne_zero]
    simpa using ht
  rw [this]
  apply iLipENorm_le
  · intro x hx
    have h'R : 0 < 2 * R := pos_of_mem_ball hx
    have hR : 0 < R := by linarith
    apply (holderApprox_le hR ht hC x).trans
    simp only [NNReal.coe_mul, NNReal.coe_pow, NNReal.coe_ofNat, NNReal.coe_rpow, C', ← mul_assoc]
    have : (C : ℝ) = 1 * 1 * C := by simp
    conv_lhs => rw [this]
    gcongr
    · calc
        (1 : ℝ)
      _ = 2⁻¹ * (2 ^ 1) := by norm_num
      _ ≤ 2⁻¹ * (2 ^ (4 * a)) := by
        gcongr
        · norm_num
        · have := four_le_a X
          linarith
    · apply Real.one_le_rpow_of_pos_of_le_one_of_nonpos (by simp [ht]) (by simp [h't])
      linarith
  · intro x hx x' hx' hne
    have h'R : 0 < 2 * R := pos_of_mem_ball hx
    have hR : 0 < R := by linarith
    simp only [NNReal.coe_mul, NNReal.coe_pow, NNReal.coe_ofNat, NNReal.coe_rpow,
      Real.coe_toNNReal', ht.le, sup_of_le_left, ← mul_assoc, C']
    exact norm_holderApprox_sub_le hR ht h't hc hϕ hC

lemma iLipENorm_holderApprox {z : X} {R t : ℝ} (ht : 0 < t) (h't : t ≤ 1)
    {ϕ : X → ℂ} (hϕ : tsupport ϕ ⊆ ball z R) :
    iLipENorm (holderApprox R t ϕ) z (2 * R) ≤
      2 ^ (4 * a) * (ENNReal.ofReal t) ^ (-1 - a : ℝ) * iHolENorm ϕ z R := by
  rcases eq_or_ne (iHolENorm ϕ z R) ∞ with h'ϕ | h'ϕ
  · apply le_top.trans_eq
    rw [eq_comm]
    simp [h'ϕ, ENNReal.mul_eq_top, ht]
  rw [← ENNReal.coe_toNNReal h'ϕ]
  apply iLipENorm_holderApprox' ht h't
  · apply continuous_of_iHolENorm_ne_top hϕ h'ϕ
  · apply (subset_tsupport ϕ).trans hϕ
  · exact fun x ↦ norm_le_iHolNNNorm_of_subset h'ϕ ((subset_tsupport ϕ).trans hϕ)

/-- The constant occurring in Proposition 2.0.5. -/
def C2_0_5 (a : ℝ) : ℝ≥0 := 2 ^ (8 * a)

section DivisionMonoid

variable {α β : Type*} [TopologicalSpace α] [DivisionMonoid β]
variable {f f' : α → β}

/- PR after HasCompactMulSupport.inv' -/

@[to_additive]
theorem HasCompactMulSupport.div (hf : HasCompactMulSupport f) (hf' : HasCompactMulSupport f') :
    HasCompactMulSupport (f / f') := hf.comp₂_left hf' (div_one 1)

end DivisionMonoid


/-- Proposition 2.0.5. -/
theorem holder_van_der_corput {z : X} {R : ℝ} (hR : 0 < R) {ϕ : X → ℂ}
    (hϕ : tsupport ϕ ⊆ ball z R) (h2ϕ : iHolENorm ϕ z R ≠ ∞) {f g : Θ X} :
    ‖∫ x, exp (I * (f x - g x)) * ϕ x‖ₑ ≤
    (C2_0_5 a : ℝ≥0∞) * volume (ball z R) * iHolENorm ϕ z R *
    (1 + nndist_{z, R} f g) ^ (2 * a^2 + a^3 : ℝ)⁻¹ := by
  let t : ℝ := (1 + nndist_{z, R} f g) ^ (- (τ / (2 + a)))
  have t_pos : 0 < t := Real.rpow_pos_of_pos (by positivity) _
  have t_one : t ≤ 1 := by
    apply Real.rpow_le_one_of_one_le_of_nonpos
    · simp only [le_add_iff_nonneg_right,  NNReal.zero_le_coe]
    · simp only [defaultτ, Left.neg_nonpos_iff]
      positivity
  have ϕ_cont : Continuous ϕ :=
    ContinuousOn.continuous_of_tsupport_subset
      ((HolderOnWith.of_iHolENorm_ne_top h2ϕ).continuousOn (nnτ_pos X)) isOpen_ball hϕ
  have ϕ_comp : HasCompactSupport ϕ := by
    apply HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall z R)
    exact (subset_tsupport ϕ).trans (hϕ.trans ball_subset_closedBall)
  let ϕ' := holderApprox R t ϕ
  have ϕ'_norm : iLipENorm (holderApprox R t ϕ) z (2 * R) < ∞ := by
    apply (iLipENorm_holderApprox t_pos t_one hϕ).trans_lt (Ne.lt_top ?_)
    simp [ENNReal.mul_eq_top, h2ϕ, t_pos]
  have ϕ'_supp : tsupport ϕ' ⊆ ball z (2 * R) := tsupport_holderApprox_subset hR hϕ ⟨t_pos, t_one⟩
  have ϕ'_cont : Continuous ϕ' :=
    ContinuousOn.continuous_of_tsupport_subset
      (LipschitzOnWith.of_iLipENorm_ne_top ϕ'_norm.ne).continuousOn isOpen_ball ϕ'_supp
  have ϕ'_comp : HasCompactSupport ϕ' := by
    apply HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall z (2 * R))
    exact (subset_tsupport ϕ').trans (ϕ'_supp.trans ball_subset_closedBall)
  have : ‖∫ x, exp (I * (f x - g x)) * ϕ x‖ₑ
      ≤ ‖∫ x, exp (I * (f x - g x)) * (ϕ x - ϕ' x)‖ₑ + ‖∫ x, exp (I * (f x - g x)) * ϕ' x‖ₑ := calc
    ‖∫ x, exp (I * (f x - g x)) * ϕ x‖ₑ
    _ = ‖∫ x, exp (I * (f x - g x)) * (ϕ x - ϕ' x) + exp (I * (f x - g x)) * ϕ' x‖ₑ := by
      congr with x
      ring
    _ = ‖(∫ x, exp (I * (f x - g x)) * (ϕ x - ϕ' x)) + ∫ x, exp (I * (f x - g x)) * ϕ' x‖ₑ := by
      rw [integral_add]
      · apply Continuous.integrable_of_hasCompactSupport (by fun_prop)
        exact (ϕ_comp.sub ϕ'_comp).mul_left
      · apply Continuous.integrable_of_hasCompactSupport (by fun_prop)
        exact ϕ'_comp.mul_left
    _ ≤ ‖∫ x, exp (I * (f x - g x)) * (ϕ x - ϕ' x)‖ₑ + ‖∫ x, exp (I * (f x - g x)) * ϕ' x‖ₑ :=
      enorm_add_le _ _
  sorry
