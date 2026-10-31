import VisionTracking.Pointing

/-!
# Body-frame facts

For an orthonormal pair `b₁, b₂`, the thrust axis `b₃ = b₁ × b₂` is a unit vector
orthogonal to both. Consequently the camera boresight `cos η · b₁ + sin η · b₃` of a
quadrotor is built from an orthonormal pair, and the pointing lower bound applies to
every state of the full rigid-body model.
-/

open InnerProductGeometry Real
open scoped RealInnerProductSpace

namespace VisionTracking

theorem cross_apply (a b : E3) :
    (cross a b).ofLp 0 = a.ofLp 1 * b.ofLp 2 - a.ofLp 2 * b.ofLp 1 ∧
    (cross a b).ofLp 1 = a.ofLp 2 * b.ofLp 0 - a.ofLp 0 * b.ofLp 2 ∧
    (cross a b).ofLp 2 = a.ofLp 0 * b.ofLp 1 - a.ofLp 1 * b.ofLp 0 := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [cross, crossProduct]

theorem inner_cross_left (a b : E3) : ⟪a, cross a b⟫ = 0 := by
  obtain ⟨h0, h1, h2⟩ := cross_apply a b
  rw [inner_eq_coords, h0, h1, h2]; ring

theorem inner_cross_right (a b : E3) : ⟪b, cross a b⟫ = 0 := by
  obtain ⟨h0, h1, h2⟩ := cross_apply a b
  rw [inner_eq_coords, h0, h1, h2]; ring

theorem cross_zero_left (a : E3) : cross 0 a = 0 := by
  ext i; fin_cases i <;> simp [cross, crossProduct]

theorem cross_smul_left (k : ℝ) (a b : E3) : cross (k • a) b = k • cross a b := by
  ext i; fin_cases i <;> simp [cross, crossProduct]

/-- Binet–Cauchy: `⟪a × b, c × d⟫ = ⟪a, c⟫⟪b, d⟫ - ⟪a, d⟫⟪b, c⟫`. -/
theorem inner_cross_cross (a b c d : E3) :
    ⟪cross a b, cross c d⟫ = ⟪a, c⟫ * ⟪b, d⟫ - ⟪a, d⟫ * ⟪b, c⟫ := by
  obtain ⟨h0, h1, h2⟩ := cross_apply a b
  obtain ⟨k0, k1, k2⟩ := cross_apply c d
  rw [inner_eq_coords, h0, h1, h2, k0, k1, k2, inner_eq_coords, inner_eq_coords,
    inner_eq_coords, inner_eq_coords]
  ring

theorem norm_cross_sq (a b : E3) : ‖cross a b‖ ^ 2 = ‖a‖ ^ 2 * ‖b‖ ^ 2 - ⟪a, b⟫ ^ 2 := by
  obtain ⟨h0, h1, h2⟩ := cross_apply a b
  rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq,
    inner_eq_coords, inner_eq_coords, inner_eq_coords, inner_eq_coords, h0, h1, h2]
  ring

theorem norm_cross_of_orthonormal {a b : E3} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hab : ⟪a, b⟫ = 0) : ‖cross a b‖ = 1 := by
  have h := norm_cross_sq a b
  rw [ha, hb, hab] at h
  have h0 := norm_nonneg (cross a b)
  nlinarith [h, h0]

variable {Q : QuadParams} {C : CameraParams} {δ : ℝ}

theorem QuadTraj.b₃_unit (d : QuadTraj Q C δ) (k : ℕ) : ‖d.b₃ k‖ = 1 := by
  rw [d.b₃_cross k]
  exact norm_cross_of_orthonormal (d.b₁_unit k) (d.b₂_unit k) (d.b₁₂_orth k)

theorem QuadTraj.b₁₃_orth (d : QuadTraj Q C δ) (k : ℕ) : ⟪d.b₁ k, d.b₃ k⟫ = 0 := by
  rw [d.b₃_cross k]; exact inner_cross_left _ _

theorem QuadTraj.thrust_nonneg (d : QuadTraj Q C δ) (k : ℕ) :
    0 ≤ totalThrust (d.f k) / Q.mass := by
  have := d.motor_nonneg k
  unfold totalThrust
  have := Q.mass_pos
  have h0 := d.motor_nonneg k 0
  have h1 := d.motor_nonneg k 1
  have h2 := d.motor_nonneg k 2
  have h3 := d.motor_nonneg k 3
  positivity

/-- **Pointing bound for every quadrotor state.** Whatever the attitude, the camera
misses a unit direction `u` by at least the distance between the hinge angle and the
rotor-plane elevation of `u`. -/
theorem QuadTraj.abs_sub_elevation_le_angle (d : QuadTraj Q C δ) (k : ℕ) {u : E3}
    (hu : ‖u‖ = 1) : |d.η k - elevation (d.b₃ k) u| ≤ angle (d.cam k) u :=
  abs_sub_le_angle_of_orthonormal (d.b₁_unit k) (d.b₃_unit k) (d.b₁₃_orth k) hu
    ⟨by linarith [C.hingeLo_ge, d.hinge_ge k], by linarith [C.hingeHi_le, d.hinge_le k]⟩

/-- **Necessary pointing condition for every quadrotor state.** If the camera sees the
unit direction `u` at step `k`, its rotor-plane elevation lies within `α` of the
hinge range. -/
theorem QuadTraj.elevation_mem_of_sees (d : QuadTraj Q C δ) (k : ℕ) {u : E3}
    (hu : ‖u‖ = 1) (hsee : angle (d.cam k) u ≤ C.halfFov) :
    C.hingeLo - C.halfFov ≤ elevation (d.b₃ k) u ∧
      elevation (d.b₃ k) u ≤ C.hingeHi + C.halfFov := by
  have h := (d.abs_sub_elevation_le_angle k hu).trans hsee
  rw [abs_le] at h
  constructor <;> linarith [h.1, h.2, d.hinge_ge k, d.hinge_le k]

end VisionTracking
