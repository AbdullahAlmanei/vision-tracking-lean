import VisionTracking.Model

/-!
# Pointing reduces to one scalar

With yaw free, whether a hinged camera can see the unit direction `u` depends only
on the *rotor-plane elevation* `e = arcsin ⟪b₃, u⟫` of `u`:

* for every yaw `ψ` and hinge angle `η ∈ [-π/2, π/2]`,
  `|η - e| ≤ angle (camAxis b₃ ψ η) u`  (`abs_sub_elevation_le_angle`);
* some yaw attains equality  (`exists_yaw_angle_eq`);
* hence the target direction can be put inside a cone of half-angle `α` with
  `η ∈ [lo, hi]` iff `lo - α ≤ e ≤ hi + α`  (`exists_visible_iff`).

The first half of the file is coordinate-free: it works for any orthonormal pair
`b₁ ⟂ b₃`. The second half shows that `bodyForward b₃ ψ` is such a `b₁`, and that
it reaches every unit vector of the rotor plane as `ψ` varies.
-/

open InnerProductGeometry Real
open scoped RealInnerProductSpace

namespace VisionTracking

/-- Rotor-plane elevation of the line of sight `u` for thrust axis `b₃`. -/
noncomputable def elevation (b₃ u : E3) : ℝ := Real.arcsin ⟪b₃, u⟫

/-! ## Coordinate-free geometry of an orthonormal pair -/

section Orthonormal

variable {b₁ b₃ u : E3}

/-- Bessel's inequality for an orthonormal pair. -/
theorem inner_sq_add_inner_sq_le (h₁ : ‖b₁‖ = 1) (h₃ : ‖b₃‖ = 1) (h₁₃ : ⟪b₁, b₃⟫ = 0)
    (u : E3) : ⟪b₁, u⟫ ^ 2 + ⟪b₃, u⟫ ^ 2 ≤ ‖u‖ ^ 2 := by
  have h := real_inner_self_nonneg (x := u - ⟪b₁, u⟫ • b₁ - ⟪b₃, u⟫ • b₃)
  have e1 : ⟪b₁, b₁⟫ = 1 := by rw [real_inner_self_eq_norm_sq, h₁]; norm_num
  have e3 : ⟪b₃, b₃⟫ = 1 := by rw [real_inner_self_eq_norm_sq, h₃]; norm_num
  have e31 : ⟪b₃, b₁⟫ = 0 := by rw [real_inner_comm]; exact h₁₃
  simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
    e1, e3, h₁₃, e31] at h
  rw [real_inner_self_eq_norm_sq, real_inner_comm b₁ u, real_inner_comm b₃ u] at h
  nlinarith [h]

/-- The camera axis built from an orthonormal pair is a unit vector. -/
theorem norm_cos_smul_add_sin_smul (h₁ : ‖b₁‖ = 1) (h₃ : ‖b₃‖ = 1) (h₁₃ : ⟪b₁, b₃⟫ = 0)
    (η : ℝ) : ‖Real.cos η • b₁ + Real.sin η • b₃‖ = 1 := by
  have e1 : ⟪b₁, b₁⟫ = 1 := by rw [real_inner_self_eq_norm_sq, h₁]; norm_num
  have e3 : ⟪b₃, b₃⟫ = 1 := by rw [real_inner_self_eq_norm_sq, h₃]; norm_num
  have e31 : ⟪b₃, b₁⟫ = 0 := by rw [real_inner_comm]; exact h₁₃
  have hsq : ‖Real.cos η • b₁ + Real.sin η • b₃‖ ^ 2 = 1 := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
      e1, e3, h₁₃, e31]
    nlinarith [Real.sin_sq_add_cos_sq η]
  have h0 := norm_nonneg (Real.cos η • b₁ + Real.sin η • b₃)
  nlinarith [hsq, h0]

/-- The key inequality: `⟪c, u⟫ ≤ cos (η - e)`. -/
theorem inner_camera_le_cos (h₁ : ‖b₁‖ = 1) (h₃ : ‖b₃‖ = 1) (h₁₃ : ⟪b₁, b₃⟫ = 0)
    (hu : ‖u‖ = 1) {η : ℝ} (hη : η ∈ Set.Icc (-(π / 2)) (π / 2)) :
    ⟪Real.cos η • b₁ + Real.sin η • b₃, u⟫ ≤ Real.cos (η - Real.arcsin ⟪b₃, u⟫) := by
  have hb := inner_sq_add_inner_sq_le h₁ h₃ h₁₃ u
  rw [hu, one_pow] at hb
  have hs : |⟪b₃, u⟫| ≤ 1 := by
    have := abs_real_inner_le_norm b₃ u
    rwa [h₃, hu, one_mul] at this
  have hb1 : ⟪b₁, u⟫ ≤ √(1 - ⟪b₃, u⟫ ^ 2) :=
    (le_abs_self _).trans (Real.abs_le_sqrt (by linarith))
  rw [Real.cos_sub, Real.cos_arcsin, Real.sin_arcsin (abs_le.1 hs).1 (abs_le.1 hs).2,
    inner_add_left, real_inner_smul_left, real_inner_smul_left]
  have hc := Real.cos_nonneg_of_mem_Icc hη
  nlinarith [mul_le_mul_of_nonneg_left hb1 hc]

/-- Equality in `inner_camera_le_cos` when `b₁` is aligned with the rotor-plane part
of `u`. -/
theorem inner_camera_eq_cos (h₃ : ‖b₃‖ = 1) (hu : ‖u‖ = 1)
    (hal : ⟪b₁, u⟫ = √(1 - ⟪b₃, u⟫ ^ 2)) (η : ℝ) :
    ⟪Real.cos η • b₁ + Real.sin η • b₃, u⟫ = Real.cos (η - Real.arcsin ⟪b₃, u⟫) := by
  have hs : |⟪b₃, u⟫| ≤ 1 := by
    have := abs_real_inner_le_norm b₃ u
    rwa [h₃, hu, one_mul] at this
  rw [Real.cos_sub, Real.cos_arcsin, Real.sin_arcsin (abs_le.1 hs).1 (abs_le.1 hs).2,
    inner_add_left, real_inner_smul_left, real_inner_smul_left, hal]

/-- `arccos (cos x) = |x|` for `|x| ≤ π`. -/
theorem arccos_cos_eq_abs {x : ℝ} (hx : |x| ≤ π) : Real.arccos (Real.cos x) = |x| := by
  rw [← Real.cos_abs, Real.arccos_cos (abs_nonneg x) hx]

theorem abs_sub_arcsin_le_pi {η s : ℝ} (hη : η ∈ Set.Icc (-(π / 2)) (π / 2)) :
    |η - Real.arcsin s| ≤ π := by
  have h1 := Real.neg_pi_div_two_le_arcsin s
  have h2 := Real.arcsin_le_pi_div_two s
  rw [abs_le]; constructor <;> linarith [hη.1, hη.2]

/-- **Lower bound, coordinate-free.** -/
theorem abs_sub_le_angle_of_orthonormal (h₁ : ‖b₁‖ = 1) (h₃ : ‖b₃‖ = 1)
    (h₁₃ : ⟪b₁, b₃⟫ = 0) (hu : ‖u‖ = 1) {η : ℝ}
    (hη : η ∈ Set.Icc (-(π / 2)) (π / 2)) :
    |η - Real.arcsin ⟪b₃, u⟫| ≤ angle (Real.cos η • b₁ + Real.sin η • b₃) u := by
  unfold angle
  rw [norm_cos_smul_add_sin_smul h₁ h₃ h₁₃, hu, one_mul, div_one,
    ← arccos_cos_eq_abs (abs_sub_arcsin_le_pi hη)]
  exact Real.arccos_le_arccos (inner_camera_le_cos h₁ h₃ h₁₃ hu hη)

/-- **Equality, coordinate-free.** -/
theorem angle_eq_abs_sub_of_aligned (h₁ : ‖b₁‖ = 1) (h₃ : ‖b₃‖ = 1)
    (h₁₃ : ⟪b₁, b₃⟫ = 0) (hu : ‖u‖ = 1) (hal : ⟪b₁, u⟫ = √(1 - ⟪b₃, u⟫ ^ 2)) {η : ℝ}
    (hη : η ∈ Set.Icc (-(π / 2)) (π / 2)) :
    angle (Real.cos η • b₁ + Real.sin η • b₃) u = |η - Real.arcsin ⟪b₃, u⟫| := by
  unfold angle
  rw [norm_cos_smul_add_sin_smul h₁ h₃ h₁₃, hu, one_mul, div_one,
    inner_camera_eq_cos h₃ hu hal, arccos_cos_eq_abs (abs_sub_arcsin_le_pi hη)]

end Orthonormal

/-! ## Coordinates: the body forward axis -/

/-- The inner product in coordinates. -/
theorem inner_eq_coords (a b : E3) :
    ⟪a, b⟫ = a.ofLp 0 * b.ofLp 0 + a.ofLp 1 * b.ofLp 1 + a.ofLp 2 * b.ofLp 2 := by
  rw [PiLp.inner_apply, Fin.sum_univ_three]
  simp only [inner, starRingEnd_apply, star_trivial, RCLike.re_to_real]
  ring

theorem inner_up (v : E3) : ⟪v, up⟫ = v.ofLp 2 := by simp [inner_eq_coords, up]

theorem inner_heading_up (ψ : ℝ) : ⟪heading ψ, up⟫ = 0 := by
  simp [inner_eq_coords, up, heading]

theorem norm_heading (ψ : ℝ) : ‖heading ψ‖ = 1 := by
  rw [EuclideanSpace.norm_eq]; simp [heading, Fin.sum_univ_three]

section Body

variable {b₃ : E3}

/-- The projection of a horizontal unit vector onto the rotor plane is nonzero when
the thrust axis is not horizontal. -/
theorem heading_proj_ne_zero (hz : ⟪b₃, up⟫ ≠ 0) (ψ : ℝ) :
    heading ψ - ⟪heading ψ, b₃⟫ • b₃ ≠ 0 := by
  intro h0
  have hup : ⟪heading ψ - ⟪heading ψ, b₃⟫ • b₃, up⟫ = 0 := by rw [h0, inner_zero_left]
  rw [inner_sub_left, real_inner_smul_left, inner_heading_up, zero_sub, neg_eq_zero] at hup
  have ht : ⟪heading ψ, b₃⟫ = 0 := (mul_eq_zero.1 hup).resolve_right hz
  rw [ht, zero_smul, sub_zero] at h0
  have := norm_heading ψ
  rw [h0, norm_zero] at this
  exact zero_ne_one this

theorem norm_bodyForward (hz : ⟪b₃, up⟫ ≠ 0) (ψ : ℝ) : ‖bodyForward b₃ ψ‖ = 1 := by
  unfold bodyForward
  exact norm_smul_inv_norm (heading_proj_ne_zero hz ψ)

theorem inner_bodyForward_self (h₃ : ‖b₃‖ = 1) (ψ : ℝ) : ⟪bodyForward b₃ ψ, b₃⟫ = 0 := by
  unfold bodyForward
  simp only
  rw [real_inner_smul_left, inner_sub_left, real_inner_smul_left,
    real_inner_self_eq_norm_sq, h₃]
  ring

/-- **Yaw covers the rotor plane.** Every unit vector `w` of the rotor plane is the
body forward axis for some yaw. -/
theorem exists_yaw_bodyForward_eq (h₃ : ‖b₃‖ = 1) (hz : ⟪b₃, up⟫ ≠ 0) {w : E3}
    (hw : ‖w‖ = 1) (hwb : ⟪w, b₃⟫ = 0) : ∃ ψ : ℝ, bodyForward b₃ ψ = w := by
  -- Slide `w` along `b₃` until it is horizontal.
  set t := ⟪w, up⟫ / ⟪b₃, up⟫ with ht
  set h := w - t • b₃ with hh
  have hh2 : h.ofLp 2 = 0 := by
    rw [← inner_up, hh, inner_sub_left, real_inner_smul_left, ht, div_mul_cancel₀ _ hz,
      sub_self]
  have hb₃b₃ : ⟪b₃, b₃⟫ = 1 := by rw [real_inner_self_eq_norm_sq, h₃]; norm_num
  have hhb : ⟪h, b₃⟫ = -t := by
    rw [hh, inner_sub_left, real_inner_smul_left, hwb, hb₃b₃]; ring
  have hne : h ≠ 0 := by
    intro h0
    have : ⟪h, b₃⟫ = 0 := by rw [h0, inner_zero_left]
    rw [hhb, neg_eq_zero] at this
    rw [hh, this, zero_smul, sub_zero] at h0
    rw [h0, norm_zero] at hw
    exact zero_ne_one hw
  have hnorm : ‖h‖ = √(h.ofLp 0 ^ 2 + h.ofLp 1 ^ 2) := by
    rw [EuclideanSpace.norm_eq]; simp [Fin.sum_univ_three, hh2]
  set z : ℂ := ⟨h.ofLp 0, h.ofLp 1⟩ with hzdef
  have hznorm : ‖z‖ = ‖h‖ := by
    rw [hnorm, Complex.norm_def, Complex.normSq_mk]; ring_nf
  have hz0 : z ≠ 0 := by
    intro h0
    have : ‖z‖ = 0 := by rw [h0, norm_zero]
    rw [hznorm, norm_eq_zero] at this
    exact hne this
  have hpos : 0 < ‖h‖ := norm_pos_iff.2 hne
  -- The heading at `arg z` is `h / ‖h‖`.
  have hhead : heading z.arg = ‖h‖⁻¹ • h := by
    ext i
    fin_cases i
    · have hc := Complex.cos_arg hz0
      have hre : z.re = h.ofLp 0 := rfl
      rw [hznorm, hre] at hc
      simp [heading, hc, div_eq_inv_mul]
    · have hc := Complex.sin_arg z
      have him : z.im = h.ofLp 1 := rfl
      rw [hznorm, him] at hc
      simp [heading, hc, div_eq_inv_mul]
    · simp [heading, hh2]
  refine ⟨z.arg, ?_⟩
  unfold bodyForward
  simp only
  have hproj : heading z.arg - ⟪heading z.arg, b₃⟫ • b₃ = ‖h‖⁻¹ • w := by
    rw [hhead, real_inner_smul_left, hhb, hh]
    module
  rw [hproj, norm_smul, hw, mul_one, Real.norm_of_nonneg (inv_nonneg.2 hpos.le), smul_smul,
    inv_inv, mul_inv_cancel₀ hpos.ne', one_smul]

end Body

/-! ## The pointing reduction -/

section Reduction

variable {b₃ u : E3}

/-- **Lower bound.** Whatever the yaw, the camera misses `u` by at least the
distance between the hinge angle and the rotor-plane elevation of `u`. -/
theorem abs_sub_elevation_le_angle (h₃ : ‖b₃‖ = 1) (hz : ⟪b₃, up⟫ ≠ 0) (hu : ‖u‖ = 1)
    (ψ : ℝ) {η : ℝ} (hη : η ∈ Set.Icc (-(π / 2)) (π / 2)) :
    |η - elevation b₃ u| ≤ angle (camAxis b₃ ψ η) u :=
  abs_sub_le_angle_of_orthonormal (norm_bodyForward hz ψ) h₃ (inner_bodyForward_self h₃ ψ)
    hu hη

/-- **Attainment.** Some yaw achieves the lower bound exactly. -/
theorem exists_yaw_angle_eq (h₃ : ‖b₃‖ = 1) (hz : ⟪b₃, up⟫ ≠ 0) (hu : ‖u‖ = 1)
    {η : ℝ} (hη : η ∈ Set.Icc (-(π / 2)) (π / 2)) :
    ∃ ψ : ℝ, angle (camAxis b₃ ψ η) u = |η - elevation b₃ u| := by
  set s := ⟪b₃, u⟫ with hs
  have hb₃b₃ : ⟪b₃, b₃⟫ = 1 := by rw [real_inner_self_eq_norm_sq, h₃]; norm_num
  have huu : ⟪u, u⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hu]; norm_num
  -- The rotor-plane part of `u`.
  set r := u - s • b₃ with hr
  have hrb : ⟪r, b₃⟫ = 0 := by
    rw [hr, inner_sub_left, real_inner_smul_left, hb₃b₃, hs, real_inner_comm]; ring
  have hrr : ‖r‖ ^ 2 = 1 - s ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, hr]
    simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
      hb₃b₃, huu]
    rw [real_inner_comm b₃ u, ← hs]; ring
  by_cases hr0 : r = 0
  · -- `u = ± b₃`: every yaw is optimal.
    refine ⟨0, ?_⟩
    have hs1 : 1 - s ^ 2 = 0 := by rw [← hrr, hr0, norm_zero]; norm_num
    have hal : ⟪bodyForward b₃ 0, u⟫ = √(1 - ⟪b₃, u⟫ ^ 2) := by
      have hu' : u = s • b₃ := by rw [← sub_eq_zero, ← hr, hr0]
      rw [← hs, hs1, Real.sqrt_zero, hu', real_inner_smul_right,
        inner_bodyForward_self h₃, mul_zero]
    exact angle_eq_abs_sub_of_aligned (norm_bodyForward hz 0) h₃ (inner_bodyForward_self h₃ 0)
      hu hal hη
  · -- Align `b₁` with `r / ‖r‖`.
    have hrpos : 0 < ‖r‖ := norm_pos_iff.2 hr0
    obtain ⟨ψ, hψ⟩ := exists_yaw_bodyForward_eq h₃ hz (w := ‖r‖⁻¹ • r)
      (norm_smul_inv_norm hr0) (by rw [real_inner_smul_left, hrb, mul_zero])
    refine ⟨ψ, ?_⟩
    have hal : ⟪bodyForward b₃ ψ, u⟫ = √(1 - ⟪b₃, u⟫ ^ 2) := by
      have hur : ⟪r, u⟫ = ‖r‖ ^ 2 := by
        rw [← real_inner_self_eq_norm_sq]
        conv_rhs => rw [hr]
        rw [inner_sub_right, real_inner_smul_right, hrb, mul_zero, sub_zero]
      rw [hψ, real_inner_smul_left, hur, ← hs, ← hrr, Real.sqrt_sq hrpos.le]
      field_simp
    exact angle_eq_abs_sub_of_aligned (norm_bodyForward hz ψ) h₃ (inner_bodyForward_self h₃ ψ)
      hu hal hη

/-- **Pointing reduction.** With yaw free, a hinge range `[lo, hi] ⊆ [-π/2, π/2]` and
cone half-angle `α ≥ 0`, the camera can put `u` inside its cone iff the rotor-plane
elevation of `u` lies in `[lo - α, hi + α]`. -/
theorem exists_visible_iff (h₃ : ‖b₃‖ = 1) (hz : ⟪b₃, up⟫ ≠ 0) (hu : ‖u‖ = 1)
    {lo hi α : ℝ} (hlo : -(π / 2) ≤ lo) (hlohi : lo ≤ hi) (hhi : hi ≤ π / 2) (hα : 0 ≤ α) :
    (∃ ψ η, η ∈ Set.Icc lo hi ∧ angle (camAxis b₃ ψ η) u ≤ α) ↔
      (lo - α ≤ elevation b₃ u ∧ elevation b₃ u ≤ hi + α) := by
  constructor
  · rintro ⟨ψ, η, ⟨h1, h2⟩, hang⟩
    have hb := (abs_sub_elevation_le_angle h₃ hz hu ψ ⟨by linarith, by linarith⟩).trans hang
    rw [abs_le] at hb
    constructor <;> linarith [hb.1, hb.2]
  · rintro ⟨h1, h2⟩
    set e := elevation b₃ u
    set η := max lo (min hi e) with hηdef
    have hηI : η ∈ Set.Icc lo hi := ⟨le_max_left _ _, max_le hlohi (min_le_left _ _)⟩
    obtain ⟨ψ, hψ⟩ := exists_yaw_angle_eq h₃ hz hu (η := η)
      ⟨by linarith [hηI.1], by linarith [hηI.2]⟩
    refine ⟨ψ, η, hηI, ?_⟩
    rw [hψ, abs_le]
    constructor
    · -- η - e ≥ -α
      have : min hi e ≤ η := le_max_right _ _
      rcases min_choice hi e with h | h <;> rw [h] at this <;> linarith
    · -- η - e ≤ α
      rcases le_total lo (min hi e) with h | h
      · rw [hηdef, max_eq_right h]; linarith [min_le_right hi e]
      · rw [hηdef, max_eq_left h]; linarith

end Reduction

end VisionTracking
