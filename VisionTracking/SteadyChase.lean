import VisionTracking.Overhead
import VisionTracking.Frame

/-!
# Speed costs tilt, and tilt costs view

A drone that holds a constant horizontal velocity `v` has zero acceleration, so its
thrust must exactly cancel gravity and drag: `f b₃ = g e₃ + c_D ‖v‖ v`. Its thrust
axis is therefore *forced* to lean forward by the **chase tilt**
`θ(v) = arctan (c_D ‖v‖² / g)`, whatever its top speed (`b₃_eq_steadyAxis`).

That tilt carries the camera with it. For a target seen ahead at elevation `λ`
above the drone's horizon, in the vertical plane of travel, the camera can see it
exactly when `lo - α ≤ θ(v) + λ ≤ hi + α` (`inplane_visible_iff`,
`steady_chase_window`). So the trackable speed depends on where the drone flies
relative to the target:

* same altitude, target dead ahead (`λ = 0`): `c_D v² ≤ g tan (hi + α)`;
* drone above the target (`λ < 0`): the bound loosens by `|λ|`;
* drone below the target (`λ > 0`): it tightens by `λ`
  (`chaseTilt_add_le_iff`).

The general (off-plane) version is `steady_visible_iff`: the relevant quantity is
`arcsin (cos θ ⟪e₃, u⟫ + sin θ ⟪v̂, u⟫)`.
-/

open InnerProductGeometry Real
open scoped RealInnerProductSpace

namespace VisionTracking

variable {Q : QuadParams} {C : CameraParams} {δ : ℝ}

/-- The tilt forced by steady level flight at speed `s`. -/
noncomputable def chaseTilt (Q : QuadParams) (s : ℝ) : ℝ :=
  Real.arctan (Q.drag * s ^ 2 / Q.g)

/-- The unit thrust axis leaning by `θ` from vertical towards the horizontal unit
vector `w`. -/
noncomputable def steadyAxis (θ : ℝ) (w : E3) : E3 :=
  Real.cos θ • up + Real.sin θ • w

theorem chaseTilt_nonneg (Q : QuadParams) (s : ℝ) : 0 ≤ chaseTilt Q s := by
  unfold chaseTilt
  rw [← Real.arctan_zero]
  exact Real.arctan_strictMono.monotone
    (div_nonneg (mul_nonneg Q.drag_pos.le (sq_nonneg s)) Q.g_pos.le)

theorem chaseTilt_lt (Q : QuadParams) (s : ℝ) : chaseTilt Q s < π / 2 :=
  Real.arctan_lt_pi_div_two _

theorem norm_steadyAxis {θ : ℝ} {w : E3} (hw : ‖w‖ = 1) (hwu : ⟪w, up⟫ = 0) :
    ‖steadyAxis θ w‖ = 1 :=
  norm_cos_smul_add_sin_smul norm_up hw (by rw [real_inner_comm]; exact hwu) θ

theorem inner_steadyAxis (θ : ℝ) (w u : E3) :
    ⟪steadyAxis θ w, u⟫ = Real.cos θ * ⟪up, u⟫ + Real.sin θ * ⟪w, u⟫ := by
  rw [steadyAxis, inner_add_left, real_inner_smul_left, real_inner_smul_left]

/-- Two nonnegative multiples of unit vectors that agree, with the second multiple
positive, have the same direction. -/
theorem eq_of_smul_eq_smul_of_unit {f M : ℝ} {b B : E3} (hf : 0 ≤ f) (hM : 0 < M)
    (hb : ‖b‖ = 1) (hB : ‖B‖ = 1) (h : f • b = M • B) : b = B := by
  have hn : f = M := by
    have := congrArg norm h
    rw [norm_smul, norm_smul, hb, hB, Real.norm_of_nonneg hf, Real.norm_of_nonneg hM.le]
      at this
    simpa using this
  rw [hn] at h
  exact smul_right_injective E3 hM.ne' h

/-- **Steady flight forces the tilt.** If the quadrotor's velocity is horizontal,
nonzero and unchanged over step `k`, then whatever its motors do, its thrust axis at
step `k` is the steady axis leaning by the chase tilt towards the direction of
travel, and its collective thrust per unit mass is `√(g² + (c_D ‖v‖²)²)`. -/
theorem b₃_eq_steadyAxis (d : QuadTraj Q C δ) (hδ : δ ≠ 0) (k : ℕ)
    (hsteady : d.v (k + 1) = d.v k) (hhor : ⟪d.v k, up⟫ = 0) (hv : d.v k ≠ 0) :
    d.b₃ k = steadyAxis (chaseTilt Q ‖d.v k‖) (‖d.v k‖⁻¹ • d.v k) := by
  set s := ‖d.v k‖ with hs
  have hspos : 0 < s := norm_pos_iff.2 hv
  set x := Q.drag * s ^ 2 / Q.g with hx
  have hthrust : (totalThrust (d.f k) / Q.mass) • d.b₃ k = Q.g • up + (Q.drag * s) • d.v k := by
    have h := d.translational k
    rw [hsteady] at h
    have h0 : δ • ((totalThrust (d.f k) / Q.mass) • d.b₃ k - Q.g • up
        - (Q.drag * ‖d.v k‖) • d.v k) = 0 := by
      have := congrArg (fun z => z - d.v k) h
      simpa using this.symm
    rcases smul_eq_zero.1 h0 with h1 | h1
    · exact absurd h1 hδ
    · rw [sub_sub, sub_eq_zero] at h1; exact h1
  have hsq : 0 < √(1 + x ^ 2) := Real.sqrt_pos.2 (by positivity)
  have hM : 0 < Q.g * √(1 + x ^ 2) := mul_pos Q.g_pos hsq
  have hw : ‖s⁻¹ • d.v k‖ = 1 := norm_smul_inv_norm hv
  have hwu : ⟪s⁻¹ • d.v k, up⟫ = 0 := by rw [real_inner_smul_left, hhor, mul_zero]
  apply eq_of_smul_eq_smul_of_unit (d.thrust_nonneg k) hM (d.b₃_unit k)
    (norm_steadyAxis hw hwu)
  rw [hthrust, steadyAxis, chaseTilt, ← hx, Real.cos_arctan, Real.sin_arctan, smul_add,
    smul_smul, smul_smul, smul_smul]
  have hsq' : √(1 + x ^ 2) ≠ 0 := hsq.ne'
  have e1 : Q.g * √(1 + x ^ 2) * (1 / √(1 + x ^ 2)) = Q.g := by field_simp
  have e2 : Q.g * √(1 + x ^ 2) * (x / √(1 + x ^ 2)) * s⁻¹ = Q.drag * s := by
    have hg := Q.g_pos.ne'
    have hs0 := hspos.ne'
    rw [hx]; field_simp
  rw [e1, e2]

/-- **Steady pointing, general direction.** At the steady axis leaning by
`θ ∈ [0, π/2)` towards the horizontal unit vector `w`, the camera can see the unit
direction `u` iff `arcsin (cos θ ⟪e₃, u⟫ + sin θ ⟪w, u⟫)` lies within `α` of the
hinge range. -/
theorem steady_visible_iff {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : θ < π / 2) {w u : E3}
    (hw : ‖w‖ = 1) (hwu : ⟪w, up⟫ = 0) (hu : ‖u‖ = 1) {lo hi α : ℝ}
    (hlo : -(π / 2) ≤ lo) (hlohi : lo ≤ hi) (hhi : hi ≤ π / 2) (hα : 0 ≤ α) :
    (∃ ψ η, η ∈ Set.Icc lo hi ∧ angle (camAxis (steadyAxis θ w) ψ η) u ≤ α) ↔
      (lo - α ≤ Real.arcsin (Real.cos θ * ⟪up, u⟫ + Real.sin θ * ⟪w, u⟫) ∧
        Real.arcsin (Real.cos θ * ⟪up, u⟫ + Real.sin θ * ⟪w, u⟫) ≤ hi + α) := by
  have hz : ⟪steadyAxis θ w, up⟫ ≠ 0 := by
    rw [inner_steadyAxis, real_inner_self_eq_norm_sq, norm_up, hwu]
    simp only [one_pow, mul_one, mul_zero, add_zero]
    exact (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hθ⟩).ne'
  rw [exists_visible_iff (norm_steadyAxis hw hwu) hz hu hlo hlohi hhi hα, elevation,
    inner_steadyAxis]

/-- **Steady pointing, in the plane of travel.** For a target ahead at elevation `λ`
(`u = cos λ · w + sin λ · e₃`) with `|θ + λ| ≤ π/2`, the camera can see it iff
`lo - α ≤ θ + λ ≤ hi + α`. -/
theorem inplane_visible_iff {θ el : ℝ} (hθ0 : 0 ≤ θ) (hθ : θ < π / 2)
    (hsum : |θ + el| ≤ π / 2) {w : E3} (hw : ‖w‖ = 1) (hwu : ⟪w, up⟫ = 0) {lo hi α : ℝ}
    (hlo : -(π / 2) ≤ lo) (hlohi : lo ≤ hi) (hhi : hi ≤ π / 2) (hα : 0 ≤ α) :
    (∃ ψ η, η ∈ Set.Icc lo hi ∧
        angle (camAxis (steadyAxis θ w) ψ η) (Real.cos el • w + Real.sin el • up) ≤ α) ↔
      (lo - α ≤ θ + el ∧ θ + el ≤ hi + α) := by
  have hu : ‖Real.cos el • w + Real.sin el • up‖ = 1 :=
    norm_cos_smul_add_sin_smul hw norm_up hwu el
  have hupup : ⟪up, up⟫ = 1 := by rw [real_inner_self_eq_norm_sq, norm_up]; norm_num
  have hww : ⟪w, w⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hw]; norm_num
  have huw : ⟪up, w⟫ = 0 := by rw [real_inner_comm]; exact hwu
  rw [steady_visible_iff hθ0 hθ hw hwu hu hlo hlohi hhi hα]
  have key : Real.cos θ * ⟪up, Real.cos el • w + Real.sin el • up⟫ +
      Real.sin θ * ⟪w, Real.cos el • w + Real.sin el • up⟫ = Real.sin (θ + el) := by
    rw [inner_add_right, inner_add_right, real_inner_smul_right, real_inner_smul_right,
      real_inner_smul_right, real_inner_smul_right, hupup, hww, huw, hwu, Real.sin_add]
    ring
  rw [key, Real.arcsin_sin (abs_le.1 hsum).1 (abs_le.1 hsum).2]

/-- **The steady-chase window.** Suppose that over step `k` the quadrotor holds a
constant, nonzero, horizontal velocity, and that at frame `k` its camera sees the
target ahead in its plane of travel at elevation `el` (that is, `p - x` is a positive
multiple of `cos el · v̂ + sin el · e₃`), with `|θ + el| ≤ π/2`. Then the chase tilt
`θ = chaseTilt ‖v‖` satisfies `lo - α ≤ θ + el ≤ hi + α`. This holds for every motor
command and every attitude consistent with the dynamics. -/
theorem steady_chase_window (d : QuadTraj Q C δ) (hδ : δ ≠ 0) (k : ℕ)
    (hsteady : d.v (k + 1) = d.v k) (hhor : ⟪d.v k, up⟫ = 0) (hv : d.v k ≠ 0)
    {s : ℝ} {p : E3} (hvis : Visible C s (d.x k) (d.cam k) p)
    {el r : ℝ} (hr : 0 < r)
    (hlos : p - d.x k = r • (Real.cos el • (‖d.v k‖⁻¹ • d.v k) + Real.sin el • up))
    (hsum : |chaseTilt Q ‖d.v k‖ + el| ≤ π / 2) :
    C.hingeLo - C.halfFov ≤ chaseTilt Q ‖d.v k‖ + el ∧
      chaseTilt Q ‖d.v k‖ + el ≤ C.hingeHi + C.halfFov := by
  have hw : ‖‖d.v k‖⁻¹ • d.v k‖ = 1 := norm_smul_inv_norm hv
  have hwu : ⟪‖d.v k‖⁻¹ • d.v k, up⟫ = 0 := by rw [real_inner_smul_left, hhor, mul_zero]
  have hb := b₃_eq_steadyAxis d hδ k hsteady hhor hv
  generalize hwdef : ‖d.v k‖⁻¹ • d.v k = w at hlos hw hwu hb
  have hu : ‖Real.cos el • w + Real.sin el • up‖ = 1 :=
    norm_cos_smul_add_sin_smul hw norm_up hwu el
  have hsee : angle (d.cam k) (Real.cos el • w + Real.sin el • up) ≤ C.halfFov := by
    have h := hvis.2
    rwa [hlos, angle_smul_right_of_pos _ _ hr] at h
  have hel : elevation (d.b₃ k) (Real.cos el • w + Real.sin el • up)
      = chaseTilt Q ‖d.v k‖ + el := by
    have hupup : ⟪up, up⟫ = 1 := by rw [real_inner_self_eq_norm_sq, norm_up]; norm_num
    have hww : ⟪w, w⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hw]; norm_num
    have huw : ⟪up, w⟫ = 0 := by rw [real_inner_comm]; exact hwu
    rw [elevation, hb, inner_steadyAxis,
      inner_add_right, inner_add_right, real_inner_smul_right, real_inner_smul_right,
      real_inner_smul_right, real_inner_smul_right, hupup, hww, huw, hwu]
    have : Real.cos (chaseTilt Q ‖d.v k‖) * (Real.cos el * 0 + Real.sin el * 1) +
        Real.sin (chaseTilt Q ‖d.v k‖) * (Real.cos el * 1 + Real.sin el * 0)
        = Real.sin (chaseTilt Q ‖d.v k‖ + el) := by rw [Real.sin_add]; ring
    rw [this, Real.arcsin_sin (abs_le.1 hsum).1 (abs_le.1 hsum).2]
  have := d.elevation_mem_of_sees k hu hsee
  rwa [hel] at this

/-- `arctan x ≤ β ↔ x ≤ tan β` for `β ∈ (-π/2, π/2)`. -/
theorem arctan_le_iff_le_tan {x β : ℝ} (h1 : -(π / 2) < β) (h2 : β < π / 2) :
    Real.arctan x ≤ β ↔ x ≤ Real.tan β := by
  conv_lhs => rw [← Real.arctan_tan h1 h2]
  exact Real.arctan_strictMono.le_iff_le

/-- **Speed form of the window's upper edge.** With the camera's reach
`β = hi + α - λ ∈ (-π/2, π/2)`, the chase tilt fits under it iff
`c_D s² ≤ g tan β`. So the top trackable steady speed at elevation `λ` is
`√(g tan (hi + α - λ) / c_D)`. -/
theorem chaseTilt_add_le_iff {s el hi α : ℝ} (h1 : -(π / 2) < hi + α - el)
    (h2 : hi + α - el < π / 2) :
    chaseTilt Q s + el ≤ hi + α ↔ Q.drag * s ^ 2 ≤ Q.g * Real.tan (hi + α - el) := by
  rw [show chaseTilt Q s + el ≤ hi + α ↔ chaseTilt Q s ≤ hi + α - el by
      constructor <;> intro h <;> linarith,
    chaseTilt, arctan_le_iff_le_tan h1 h2, div_le_iff₀ Q.g_pos, mul_comm (Real.tan _)]

/-- **Speed form of the window's lower edge.** The camera can still reach down far
enough iff `g tan (lo - α - λ) ≤ c_D s²` (for `lo - α - λ ∈ (-π/2, π/2)`). A camera
that cannot look low enough sets a *minimum* trackable speed. -/
theorem le_chaseTilt_add_iff {s el lo α : ℝ} (h1 : -(π / 2) < lo - α - el)
    (h2 : lo - α - el < π / 2) :
    lo - α ≤ chaseTilt Q s + el ↔ Q.g * Real.tan (lo - α - el) ≤ Q.drag * s ^ 2 := by
  rw [show lo - α ≤ chaseTilt Q s + el ↔ lo - α - el ≤ chaseTilt Q s by
      constructor <;> intro h <;> linarith, chaseTilt]
  conv_lhs => rw [← Real.arctan_tan h1 h2]
  rw [Real.arctan_strictMono.le_iff_le, le_div_iff₀ Q.g_pos, mul_comm]

end VisionTracking
