import VisionTracking.Pointing

/-!
# Overhead geometry: hinge range and fixed mounts

When the drone sits directly above the target, the line of sight is `-e₃`, and its
rotor-plane elevation is simply `tilt - π/2`, where `tilt` is the angle between the
thrust axis and vertical (`elevation_neg_up`). Combined with the pointing reduction:

* `overhead_visible_iff`: at a single thrust axis, the camera can see straight down
  iff `tilt - π/2` lies within `α` of the hinge range;
* `overhead_band_iff`: it can do so for *every* thrust axis whose tilt lies in a band
  `[tlo, thi]` iff `lo - α ≤ tlo - π/2` and `thi - π/2 ≤ hi + α`;
* `fixed_overhead_iff`: a **fixed** camera (no hinge) works across the whole tilt
  band iff `thi - tlo ≤ 2α`; the mount angle `(tlo + thi)/2 - π/2` then suffices.

The tilt band is whatever the drone's thrust must span to copy the target (from
drag at the target's speed band plus its manoeuvres); that is the next layer of
the roadmap.
-/

open InnerProductGeometry Real
open scoped RealInnerProductSpace

namespace VisionTracking

theorem norm_up : ‖up‖ = 1 := by simp [up]

/-- The forward unit vector `e₁`. -/
noncomputable def east : E3 := EuclideanSpace.single 0 1

theorem norm_east : ‖east‖ = 1 := by simp [east]

theorem inner_east_up : ⟪east, up⟫ = 0 := by simp [inner_eq_coords, east, up]

/-- From directly above, the line of sight `-e₃` has rotor-plane elevation
`tilt - π/2`. -/
theorem elevation_neg_up {b : E3} (hb : ‖b‖ = 1) :
    elevation b (-up) = angle b up - π / 2 := by
  have hcos : ⟪b, up⟫ = Real.cos (angle b up) := by
    rw [cos_angle, hb, norm_up, mul_one, div_one]
  have h0 := angle_nonneg b up
  have hπ := angle_le_pi b up
  unfold elevation
  rw [inner_neg_right, hcos, Real.arcsin_neg, ← Real.sin_pi_div_two_sub,
    Real.arcsin_sin (by linarith) (by linarith)]
  ring

/-- A tilted unit vector: tilt `t` from vertical, leaning towards `e₁`. -/
noncomputable def tiltVec (t : ℝ) : E3 := Real.cos t • up + Real.sin t • east

theorem norm_tiltVec (t : ℝ) : ‖tiltVec t‖ = 1 := by
  unfold tiltVec
  have h := norm_cos_smul_add_sin_smul norm_up norm_east
    (by rw [real_inner_comm]; exact inner_east_up) t
  exact h

theorem angle_tiltVec_up {t : ℝ} (h0 : 0 ≤ t) (hπ : t ≤ π) : angle (tiltVec t) up = t := by
  unfold angle
  have hup : ⟪up, up⟫ = 1 := by rw [real_inner_self_eq_norm_sq, norm_up]; norm_num
  rw [norm_tiltVec, norm_up, mul_one, div_one, tiltVec, inner_add_left,
    real_inner_smul_left, real_inner_smul_left, hup, inner_east_up, mul_zero, add_zero,
    mul_one, Real.arccos_cos h0 hπ]

theorem inner_up_ne_zero_of_tilt_lt {b : E3} (hb : ‖b‖ = 1) (ht : angle b up < π / 2) :
    ⟪b, up⟫ ≠ 0 := by
  have hcos : ⟪b, up⟫ = Real.cos (angle b up) := by
    rw [cos_angle, hb, norm_up, mul_one, div_one]
  rw [hcos]
  exact (Real.cos_pos_of_mem_Ioo ⟨by linarith [angle_nonneg b up], ht⟩).ne'

variable {lo hi α : ℝ}

/-- **Overhead visibility at one thrust axis.** -/
theorem overhead_visible_iff {b : E3} (hb : ‖b‖ = 1) (ht : angle b up < π / 2)
    (hlo : -(π / 2) ≤ lo) (hlohi : lo ≤ hi) (hhi : hi ≤ π / 2) (hα : 0 ≤ α) :
    (∃ ψ η, η ∈ Set.Icc lo hi ∧ angle (camAxis b ψ η) (-up) ≤ α) ↔
      (lo - α ≤ angle b up - π / 2 ∧ angle b up - π / 2 ≤ hi + α) := by
  rw [exists_visible_iff hb (inner_up_ne_zero_of_tilt_lt hb ht)
    (by rw [norm_neg, norm_up]) hlo hlohi hhi hα, elevation_neg_up hb]

/-- Thrust axes whose tilt lies in `[tlo, thi]`. -/
def TiltBand (tlo thi : ℝ) : Set E3 :=
  {b | ‖b‖ = 1 ∧ angle b up ∈ Set.Icc tlo thi}

/-- **Overhead visibility across a tilt band.** The hinge must reach down to at
most `tlo - π/2 + α` and up to at least `thi - π/2 - α`, and that is enough. -/
theorem overhead_band_iff {tlo thi : ℝ} (htlo : 0 ≤ tlo) (htt : tlo ≤ thi)
    (hthi : thi < π / 2)
    (hlo : -(π / 2) ≤ lo) (hlohi : lo ≤ hi) (hhi : hi ≤ π / 2) (hα : 0 ≤ α) :
    (∀ b ∈ TiltBand tlo thi, ∃ ψ η, η ∈ Set.Icc lo hi ∧ angle (camAxis b ψ η) (-up) ≤ α) ↔
      (lo - α ≤ tlo - π / 2 ∧ thi - π / 2 ≤ hi + α) := by
  constructor
  · intro h
    have hπ : π / 2 < π := by linarith [Real.pi_pos]
    have ha := h (tiltVec tlo) ⟨norm_tiltVec tlo, by
      rw [angle_tiltVec_up htlo (by linarith)]; exact ⟨le_rfl, htt⟩⟩
    have hb := h (tiltVec thi) ⟨norm_tiltVec thi, by
      rw [angle_tiltVec_up (by linarith) (by linarith)]; exact ⟨htt, le_rfl⟩⟩
    rw [overhead_visible_iff (norm_tiltVec _)
      (by rw [angle_tiltVec_up htlo (by linarith)]; linarith) hlo hlohi hhi hα,
      angle_tiltVec_up htlo (by linarith)] at ha
    rw [overhead_visible_iff (norm_tiltVec _)
      (by rw [angle_tiltVec_up (by linarith) (by linarith)]; linarith) hlo hlohi hhi hα,
      angle_tiltVec_up (by linarith) (by linarith)] at hb
    exact ⟨ha.1, hb.2⟩
  · rintro ⟨h1, h2⟩ b ⟨hb, ht1, ht2⟩
    rw [overhead_visible_iff hb (by linarith) hlo hlohi hhi hα]
    constructor <;> linarith

/-- **Fixed camera from overhead.** Some fixed mount angle sees straight down at
every tilt in `[tlo, thi]` iff the band is at most `2α` wide. -/
theorem fixed_overhead_iff {tlo thi : ℝ} (htlo : 0 ≤ tlo) (htt : tlo ≤ thi)
    (hthi : thi < π / 2) (hα : 0 ≤ α) :
    (∃ η₀ ∈ Set.Icc (-(π / 2)) (π / 2),
        ∀ b ∈ TiltBand tlo thi, ∃ ψ, angle (camAxis b ψ η₀) (-up) ≤ α) ↔
      thi - tlo ≤ 2 * α := by
  have fixed : ∀ η₀ ∈ Set.Icc (-(π / 2)) (π / 2),
      (∀ b ∈ TiltBand tlo thi, ∃ ψ, angle (camAxis b ψ η₀) (-up) ≤ α) ↔
        (η₀ - α ≤ tlo - π / 2 ∧ thi - π / 2 ≤ η₀ + α) := by
    intro η₀ hη₀
    rw [← overhead_band_iff htlo htt hthi hη₀.1 le_rfl hη₀.2 hα]
    constructor
    · intro h b hb
      obtain ⟨ψ, hψ⟩ := h b hb
      exact ⟨ψ, η₀, ⟨le_rfl, le_rfl⟩, hψ⟩
    · intro h b hb
      obtain ⟨ψ, η, hη, hψ⟩ := h b hb
      have : η = η₀ := le_antisymm hη.2 hη.1
      exact ⟨ψ, this ▸ hψ⟩
  constructor
  · rintro ⟨η₀, hη₀, h⟩
    have := (fixed η₀ hη₀).1 h
    linarith [this.1, this.2]
  · intro hw
    refine ⟨(tlo + thi) / 2 - π / 2, ⟨by linarith, by linarith⟩, ?_⟩
    rw [fixed _ ⟨by linarith, by linarith⟩]
    constructor <;> linarith

end VisionTracking
