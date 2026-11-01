import VisionTracking.PlannerSharp

/-!
# Planner smoothness from the target's snap limit

If the target starts in steady flight (zero initial jerk), the extended acceleration has
second differences at most `δ² · snap` everywhere, and so does the planned acceleration
up to the factor `H₀ = Σ |hᵢ|`.
-/

open InnerProductGeometry Real
open scoped RealInnerProductSpace

namespace VisionTracking

variable {P : TargetParams} {δ : ℝ}

theorem TargetTraj.accExt_second_le (T : TargetTraj P δ) (a₀ : E3) (hδ : 0 < δ)
    (hS : T.v 1 = T.v 0 + δ • a₀) (hS2 : T.v 2 = T.v 1 + δ • a₀) (n : ℤ) :
    ‖T.accExt a₀ (n + 2) - 2 • T.accExt a₀ (n + 1) + T.accExt a₀ n‖ ≤ δ ^ 2 * P.snap := by
  have hJ : 0 ≤ δ ^ 2 * P.snap := mul_nonneg (sq_nonneg δ) P.snap_nonneg
  have hd : δ ≠ 0 := hδ.ne'
  have a0 : δ⁻¹ • (T.v 1 - T.v 0) = a₀ := by
    rw [hS, add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hd, one_smul]
  have a1 : δ⁻¹ • (T.v 2 - T.v 1) = a₀ := by
    rw [hS2, add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hd, one_smul]
  rcases le_or_gt 0 n with h | h
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le h
    have h1 : (0 : ℤ) ≤ (m : ℤ) + 1 := by omega
    have h2 : (0 : ℤ) ≤ (m : ℤ) + 2 := by omega
    simp only [TargetTraj.accExt, if_pos h, if_pos h1, if_pos h2]
    rw [show ((m : ℤ) + 2).toNat = m + 2 by omega, show ((m : ℤ) + 1).toNat = m + 1 by omega,
      show (m : ℤ).toNat = m by omega]
    have e : δ⁻¹ • (T.v (m + 2 + 1) - T.v (m + 2)) - 2 • δ⁻¹ • (T.v (m + 1 + 1) - T.v (m + 1))
        + δ⁻¹ • (T.v (m + 1) - T.v m)
        = δ⁻¹ • (T.v (m + 3) - 3 • T.v (m + 2) + 3 • T.v (m + 1) - T.v m) := by
      rw [show m + 2 + 1 = m + 3 by ring, show m + 1 + 1 = m + 2 by ring]; module
    rw [e, norm_smul, norm_inv, Real.norm_of_nonneg hδ.le, inv_mul_le_iff₀ hδ]
    calc _ ≤ δ ^ 3 * P.snap := T.snap_le m
      _ = δ * (δ ^ 2 * P.snap) := by ring
  · rcases (by omega : n = -1 ∨ n = -2 ∨ n ≤ -3) with h1 | h1 | h1
    · subst h1
      simp only [TargetTraj.accExt]
      norm_num
      rw [a1, a0]
      have : a₀ - 2 • a₀ + a₀ = 0 := by module
      rw [this, norm_zero]; exact hJ
    · subst h1
      simp only [TargetTraj.accExt]
      norm_num
      rw [a0]
      have : a₀ - 2 • a₀ + a₀ = 0 := by module
      rw [this, norm_zero]; exact hJ
    · have e1 : ¬ (0 ≤ n + 2) := by omega
      have e2 : ¬ (0 ≤ n + 1) := by omega
      have e3 : ¬ (0 ≤ n) := by omega
      simp only [TargetTraj.accExt, if_neg e1, if_neg e2, if_neg e3]
      have : a₀ - 2 • a₀ + a₀ = 0 := by module
      rw [this, norm_zero]; exact hJ

namespace FIR

variable (F : FIR) (T : TargetTraj P δ) (a₀ : E3)

/-- **Planned acceleration, second difference, from snap.** -/
theorem planAcc_second_snap (hδ : 0 < δ) (hS : T.StartsSteady (T.p 0) (T.v 0) a₀) (k : ℕ) :
    ‖F.planAcc T a₀ (k + 2) - 2 • F.planAcc T a₀ (k + 1) + F.planAcc T a₀ k‖
      ≤ F.H0 * δ ^ 2 * P.snap := by
  have key : F.planAcc T a₀ (k + 2) - 2 • F.planAcc T a₀ (k + 1) + F.planAcc T a₀ k
      = ∑ i ∈ Finset.range (F.M + 1), F.h i • (T.accExt a₀ (((k : ℤ) - i) + 2)
          - 2 • T.accExt a₀ (((k : ℤ) - i) + 1) + T.accExt a₀ ((k : ℤ) - i)) := by
    simp only [planAcc, Finset.smul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro i _
    rw [show ((k + 2 : ℕ) : ℤ) - i = ((k : ℤ) - i) + 2 by push_cast; ring,
      show ((k + 1 : ℕ) : ℤ) - i = ((k : ℤ) - i) + 1 by push_cast; ring]
    module
  rw [key]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ i ∈ Finset.range (F.M + 1), ‖F.h i • (T.accExt a₀ (((k : ℤ) - i) + 2)
          - 2 • T.accExt a₀ (((k : ℤ) - i) + 1) + T.accExt a₀ ((k : ℤ) - i))‖
      ≤ ∑ i ∈ Finset.range (F.M + 1), |F.h i| * (δ ^ 2 * P.snap) := by
        apply Finset.sum_le_sum; intro i _
        rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left
          (T.accExt_second_le a₀ hδ hS.1.2.2 (by rw [hS.2, hS.1.2.2]) _) (abs_nonneg _)
    _ = F.H0 * δ ^ 2 * P.snap := by
        rw [H0, Finset.sum_mul, Finset.sum_mul]
        apply Finset.sum_congr rfl; intro i _; ring

end FIR

end VisionTracking
