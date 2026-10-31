import VisionTracking.Model

/-!
# Motor allocation for the "+" quadrotor

The mixer maps four motor thrusts to a collective thrust `F` and a body torque
`τ = (L (f₁ - f₃), L (f₂ - f₀), k (f₀ - f₁ + f₂ - f₃))`. It is invertible, and the
inverse is explicit:

`f₀ = F/4 - τ₁/(2L) + τ₂/(4k)`, `f₂ = F/4 + τ₁/(2L) + τ₂/(4k)`,
`f₁ = F/4 + τ₀/(2L) - τ₂/(4k)`, `f₃ = F/4 - τ₀/(2L) - τ₂/(4k)`.

So a wrench `(F, τ)` is producible by motors in `[0, fMotor]` exactly when each of
these four numbers lies in that interval. `exists_motors_of_wrench` gives the
convenient sufficient form, with roll/pitch/yaw demands inside the thrust margins.
-/

namespace VisionTracking

variable {Q : QuadParams}

/-- The explicit inverse mixer. -/
noncomputable def QuadParams.mix (Q : QuadParams) (F : ℝ) (τ : E3) : Fin 4 → ℝ :=
  ![F / 4 - τ.ofLp 1 / (2 * Q.arm) + τ.ofLp 2 / (4 * Q.kYaw),
    F / 4 + τ.ofLp 0 / (2 * Q.arm) - τ.ofLp 2 / (4 * Q.kYaw),
    F / 4 + τ.ofLp 1 / (2 * Q.arm) + τ.ofLp 2 / (4 * Q.kYaw),
    F / 4 - τ.ofLp 0 / (2 * Q.arm) - τ.ofLp 2 / (4 * Q.kYaw)]

theorem totalThrust_mix (F : ℝ) (τ : E3) : totalThrust (Q.mix F τ) = F := by
  simp [totalThrust, QuadParams.mix]; ring

theorem torque_mix (F : ℝ) (τ : E3) : Q.torque (Q.mix F τ) = τ := by
  have hL := Q.arm_pos.ne'
  have hk := Q.kYaw_pos.ne'
  ext i
  fin_cases i <;> simp [QuadParams.torque, QuadParams.mix] <;> field_simp <;> ring

/-- `|a| / c` bounds `a / c` from both sides for `c > 0`. -/
theorem abs_div_bounds {a c : ℝ} (hc : 0 < c) : -(|a| / c) ≤ a / c ∧ a / c ≤ |a| / c := by
  constructor
  · rw [← neg_div]; exact div_le_div_of_nonneg_right (neg_abs_le a) hc.le
  · exact div_le_div_of_nonneg_right (le_abs_self a) hc.le

/-- **Motor allocation.** A collective thrust `F` and body torque `τ` are produced by
four motor thrusts in `[0, fMotor]` whenever the per-axis torque demands fit inside
`F / 4` and `fMotor - F / 4`. -/
theorem exists_motors_of_wrench (F : ℝ) (τ : E3)
    (h1 : |τ.ofLp 0| / (2 * Q.arm) + |τ.ofLp 2| / (4 * Q.kYaw) ≤ F / 4)
    (h2 : |τ.ofLp 1| / (2 * Q.arm) + |τ.ofLp 2| / (4 * Q.kYaw) ≤ F / 4)
    (h3 : F / 4 + |τ.ofLp 0| / (2 * Q.arm) + |τ.ofLp 2| / (4 * Q.kYaw) ≤ Q.fMotor)
    (h4 : F / 4 + |τ.ofLp 1| / (2 * Q.arm) + |τ.ofLp 2| / (4 * Q.kYaw) ≤ Q.fMotor) :
    ∃ f : Fin 4 → ℝ, (∀ i, 0 ≤ f i ∧ f i ≤ Q.fMotor) ∧ totalThrust f = F ∧
      Q.torque f = τ := by
  refine ⟨Q.mix F τ, ?_, totalThrust_mix F τ, torque_mix F τ⟩
  have hL : 0 < 2 * Q.arm := by linarith [Q.arm_pos]
  have hk : 0 < 4 * Q.kYaw := by linarith [Q.kYaw_pos]
  obtain ⟨a0, b0⟩ := abs_div_bounds (a := τ.ofLp 0) hL
  obtain ⟨a1, b1⟩ := abs_div_bounds (a := τ.ofLp 1) hL
  obtain ⟨a2, b2⟩ := abs_div_bounds (a := τ.ofLp 2) hk
  intro i
  fin_cases i <;> simp [QuadParams.mix] <;> constructor <;> linarith

end VisionTracking
