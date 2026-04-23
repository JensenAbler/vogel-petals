/-
# Formalizing "How Irrational Spirals Make Flowers"

This file formalizes the key mathematical claims from the theory of Vogel spirals
and petal formation. A Vogel spiral places particles at angular step 2π/α², and a
radial modulation sin⁸(θ·P/2) creates P peaks. The step size P/α² (in modulation
cycles) determines coherence.

## Main results

1. **Golden power decomposition**: φⁿ = Fib(n) · φ + Fib(n-1), which implies that
   for P = φⁿ, the step size P/φ² = φⁿ⁻² decomposes so the petal count is Fib(n-2).

2. **Pentagon bridge identity**: cos(2π/5) = 1/(2φ), connecting circular geometry (π)
   with golden geometry (φ) through the regular pentagon.

3. **Pell sequence recurrence**: The Pell numbers satisfy P(n) = 2·P(n-1) + P(n-2),
   generalizing Fibonacci's role when the continued fraction coefficient is 2 instead of 1.

4. **Offset invariance**: Adding α² to P doesn't change the fractional part of P/α²,
   so petal structure is preserved.
-/

import Mathlib

open Real
open scoped goldenRatio

noncomputable section

/-!
## Part 1: Golden Ratio Power Decomposition

The fundamental identity: φⁿ⁺¹ = Fib(n+1) · φ + Fib(n).
This is the engine of Fibonacci petal counts. When P = φⁿ, the step size
P/φ² = φⁿ⁻² decomposes into Fib(n-2)·φ + Fib(n-3). The integer part Fib(n-3)
is invisible under sin⁸, and the surviving Fib(n-2)·φ determines the petal count.
-/

/-- The golden ratio power decomposition: φⁿ⁺¹ = Fib(n+1) · φ + Fib(n).
This is a restatement of Mathlib's `goldenRatio_mul_fib_succ_add_fib` in
additive form, making the Fibonacci coefficients explicit. -/
theorem goldenRatio_pow_eq_fib_decomposition (n : ℕ) :
    φ ^ (n + 1) = ↑(Nat.fib (n + 1)) * φ + ↑(Nat.fib n) := by
  linarith [goldenRatio_mul_fib_succ_add_fib n]

/-- The step-size decomposition for the Vogel spiral petal mechanism.
When P = φⁿ⁺³, the step size P/φ² = φⁿ⁺¹ decomposes as Fib(n+1)·φ + Fib(n).
The integer part Fib(n) vanishes under sin⁸ (period-1 modulation), and the
surviving fractional structure Fib(n+1)·φ gives Fib(n+1) petals. -/
theorem step_size_decomposition (n : ℕ) :
    φ ^ (n + 3) / φ ^ 2 = ↑(Nat.fib (n + 1)) * φ + ↑(Nat.fib n) := by
  have hφ : φ ^ 2 ≠ 0 := by positivity
  rw [div_eq_iff hφ, ← goldenRatio_pow_eq_fib_decomposition]
  ring

/-- The ground state: when P = φ², the step size is 1 (= Fib(1)·φ + Fib(0) = 0·φ + 1).
Every particle sees the same modulation phase, so no petals emerge. -/
theorem ground_state : φ ^ 2 / φ ^ 2 = 1 := div_self (by positivity)

/-!
## Part 2: The Pentagon Bridge Identity

cos(2π/5) = 1/(2φ) connects circular geometry (π) with golden geometry (φ).
This is the geometric foundation for the bridge identity π ≈ 6φ²/5, which
unifies the φ-family and π-family of coherences.
-/

/-
PROBLEM
The pentagon bridge identity: cos(72°) = cos(2π/5) = 1/(2φ).
This connects π and φ through the regular pentagon, where the diagonal-to-side
ratio is φ and the interior angle is 108° = 3π/5.

PROVIDED SOLUTION
Suffices to show both sides equal (√5 - 1)/4. For the RHS: 1/(2φ) = 1/((1+√5)/2 * 2) = 1/(1+√5) = (√5-1)/((√5+1)(√5-1)) = (√5-1)/4. For the LHS: use cos_two_mul and cos_pi_div_five to compute cos(2π/5) = 2*((1+√5)/4)^2 - 1 = 2*(6+2√5)/16 - 1 = (6+2√5)/8 - 1 = (√5-1)/4 (using √5^2 = 5). Strategy: show both sides equal (√5 - 1) / 4 using have statements, then combine. Use nlinarith with sq_sqrt for the algebraic manipulations.
-/
theorem cos_two_pi_div_five_eq_inv_two_goldenRatio :
    Real.cos (2 * π / 5) = 1 / (2 * φ) := by
  -- Use the identity $cos(2π/5) = 2cos²(π/5) - 1$ to rewrite the goal.
  suffices h : 2 * (Real.cos (Real.pi / 5)) ^ 2 - 1 = 1 / (2 * φ) by
    rw [ ← h, ← Real.cos_two_mul, mul_div_assoc ];
  rw [ Real.cos_sq ] ; ring ; norm_num [ mul_div ] ; ring;
  rw [ show Real.pi * ( 2 / 5 ) = 2 * ( Real.pi / 5 ) by ring, Real.cos_two_mul ] ; norm_num [ Real.cos_pi_div_five ] ; ring ; norm_num;
  grind

/-!
## Part 3: Offset Invariance

Adding α² to P preserves the fractional part of P/α², hence preserves the
petal structure. This is because (P + α²)/α² = P/α² + 1, and the integer
offset 1 is invisible under sin⁸.
-/

/-- Offset invariance: for any real P and nonzero α², adding α² to P shifts
the step size P/α² by exactly 1. Since sin⁸ has period 1, the modulation
structure is unchanged — same petals, same orientation. -/
theorem offset_invariance (P α_sq : ℝ) (hα : α_sq ≠ 0) :
    (P + α_sq) / α_sq = P / α_sq + 1 := by
  rw [add_div, div_self hα]

/-!
## Part 4: The Pell Sequence

When the continued fraction of 1/α² has all partial quotients equal to 2
(instead of 1 for the golden ratio), the recurrence becomes G(n) = 2·G(n-1) + G(n-2),
generating Pell numbers: 0, 1, 2, 5, 12, 29, ...

This generalizes the Fibonacci mechanism: different continued fraction coefficients
produce different integer sequences, all serving as petal counts.
-/

/-- The Pell sequence: P(0) = 0, P(1) = 1, P(n+2) = 2·P(n+1) + P(n). -/
def pell : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 => 2 * pell (n + 1) + pell n

@[simp] theorem pell_zero : pell 0 = 0 := rfl
@[simp] theorem pell_one : pell 1 = 1 := rfl
@[simp] theorem pell_two : pell 2 = 2 := rfl

theorem pell_succ_succ (n : ℕ) : pell (n + 2) = 2 * pell (n + 1) + pell n := rfl

/-- First several Pell numbers, matching the essay's table. -/
theorem pell_values :
    (pell 0, pell 1, pell 2, pell 3, pell 4, pell 5) = (0, 1, 2, 5, 12, 29) := by
  native_decide

/-!
## Part 5: The Pell Generator Algebra

For the Pell case, α = √(1+√2), so α² = 1+√2. Powers of α² = 1+√2 satisfy
(1+√2)ⁿ = Pell(n)·√2 + (integer), analogous to φⁿ = Fib(n)·φ + (integer).

The "silver ratio" δ = 1 + √2 satisfies δ² = 2δ + 1, paralleling φ² = φ + 1.
-/

/-- The silver ratio δ = 1 + √2 satisfies δ² = 2δ + 1.
This is the Pell analogue of φ² = φ + 1. The coefficient 2 in the recurrence
matches the continued fraction partial quotient for √2: [1; 2, 2, 2, ...]. -/
theorem silver_ratio_sq : (1 + √2) ^ 2 = 2 * (1 + √2) + 1 := by
  nlinarith [Real.sq_sqrt (show (2 : ℝ) ≥ 0 by norm_num)]

/-!
## Part 6: Why φ is Special

The golden ratio is the unique irrational number that is simultaneously:
- Degree 2 algebraic (every power decomposes)
- Has all continued fraction partial quotients equal to 1 (simplest recurrence)
- Is the "most irrational" number (hardest to approximate by rationals)

We formalize the first property: φ is a root of x² - x - 1 = 0, which is
degree 2. This means every power of φ is a ℤ-linear combination of 1 and φ,
so the decomposition φⁿ = Fib(n)·φ + Fib(n-1) works for ALL n.
-/

/-- φ satisfies the quadratic equation x² = x + 1. This degree-2 property
means every power of φ reduces to an integer linear combination of 1 and φ,
which is why ALL powers of φ produce coherent petal counts (unlike higher-degree
algebraic numbers where only certain powers work). -/
theorem goldenRatio_quadratic : φ ^ 2 - φ - 1 = 0 := by linarith [goldenRatio_sq]

/-- The golden ratio is irrational — no two particles in a golden-angle
Vogel spiral ever land at the same angle. -/
theorem goldenRatio_is_irrational : Irrational φ := goldenRatio_irrational

/-!
## Part 7: Fibonacci Petal Count Table

We verify the essay's petal count table. For P = φⁿ⁺², the step size is
φⁿ = Fib(n)·φ + Fib(n-1), and the petal count is Fib(n).

| P   | Step = P/φ² | Fib coefficient | Petals |
|-----|-------------|-----------------|--------|
| φ²  | φ⁰ = 1     | Fib(0) = 0      | 0      |
| φ³  | φ¹         | Fib(1) = 1      | 1      |
| φ⁴  | φ²         | Fib(1) = 1      | 1      |
| φ⁵  | φ³         | Fib(2) = 2      | 2      |
| φ⁶  | φ⁴         | Fib(3) = 3      | 3      |
| φ⁷  | φ⁵         | Fib(4) = 5      | 5      |
| φ⁸  | φ⁶         | Fib(5) = 8      | 8      |
-/

/-
PROBLEM
The petal count for P = φⁿ⁺² is Fib(n). We extract the Fibonacci coefficient
from the golden ratio power decomposition: φⁿ = Fib(n)·φ + Fib(n-1), where
Fib(n-1) is an integer that vanishes under sin⁸ modulation.

PROVIDED SOLUTION
For n=0: φ^2/φ^2 = 1 = 0*φ + 1, so k=1. For n≥1 (say n = m+1): φ^(m+3)/φ^2 = φ^(m+1) by field_simp/ring. Then goldenRatio_pow_eq_fib_decomposition m gives φ^(m+1) = Fib(m+1)*φ + Fib(m). So k = Fib(m) = Fib(n-1). Use cases n, then for the succ case use the decomposition theorem directly.
-/
theorem petal_count_is_fib (n : ℕ) :
    ∃ (k : ℤ), φ ^ (n + 2) / φ ^ 2 = ↑(Nat.fib n) * φ + ↑k := by
  induction' n with n ih;
  · exact ⟨ 1, by rw [ div_self <| by positivity ] ; norm_num ⟩;
  · rw [ show φ ^ ( n + 3 ) / φ ^ 2 = φ ^ ( n + 1 ) by rw [ div_eq_iff ( by positivity ) ] ; ring ] ; rw [ goldenRatio_pow_eq_fib_decomposition ] ; aesop;

/-- Verification of specific Fibonacci petal counts from the essay's table. -/
theorem fib_petal_table :
    (Nat.fib 0, Nat.fib 1, Nat.fib 2, Nat.fib 3, Nat.fib 4, Nat.fib 5) =
    (0, 1, 1, 2, 3, 5) := rfl

end