module

public import Mathlib.Data.Nat.Prime.Factorial
public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.NormNum

/-!
# Erdős Problem 374
Distinct positive factorial arguments; exact minimal cardinality.
Source: Erdős--Graham, On products of factorials (1976), pp. 337--355;
https://www.erdosproblems.com/374 (accessed 7 October 2026).
The density question below is a proposition, not an asserted theorem.
The proven results are classical constructions, not a new solution.
-/
public section

namespace Erdos374
open scoped BigOperators

/-- A representation by exactly k distinct positive factorial arguments, largest m. -/
def HasRep (m k : ℕ) : Prop :=
  ∃ s : Finset ℕ, s.card = k ∧ m ∈ s ∧
    (∀ a ∈ s, 0 < a ∧ a ≤ m) ∧ IsSquare (∏ a ∈ s, Nat.factorial a)

/-- The minimum is taken only over cardinalities at least two. No default F value. -/
def InD (m k : ℕ) : Prop :=
  2 ≤ k ∧ HasRep m k ∧ ∀ j, 2 ≤ j → j < k → ¬ HasRep m j

def D (k : ℕ) : Set ℕ := {m | InD m k}

noncomputable def countD (k n : ℕ) : ℕ := by
  classical
  exact ((Finset.Icc 1 n).filter (fun m => InD m k)).card

/-- Exact meaning of the example question |D₆ ∩ {1,...,n}| ≫ n. -/
def PositiveLowerDensitySix : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → c * (n : ℝ) ≤ (countD 6 n : ℝ)

theorem rep_two {a b : ℕ} (ha : 0 < a) (hab : a < b)
    (hsq : IsSquare (Nat.factorial a * Nat.factorial b)) : HasRep b 2 := by
  sorry

theorem square_inD_two {r : ℕ} (hr : 1 < r) : InD (r ^ 2) 2 := by
  sorry

theorem adjacent_identity {n : ℕ} (hn : 0 < n) :
    Nat.factorial n * Nat.factorial (n - 1) =
      n * Nat.factorial (n - 1) ^ 2 := by
  sorry

theorem four_factor_identity {r u : ℕ} (hr : 0 < r) (hu : 0 < u) :
    Nat.factorial (r ^ 2 * u) * Nat.factorial (r ^ 2 * u - 1) *
      Nat.factorial u * Nat.factorial (u - 1) =
      (r * u * Nat.factorial (r ^ 2 * u - 1) * Nat.factorial (u - 1)) ^ 2 := by
  sorry

theorem six_factor_identity {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    Nat.factorial (a * b) * Nat.factorial (a * b - 1) *
      Nat.factorial a * Nat.factorial (a - 1) *
      Nat.factorial b * Nat.factorial (b - 1) =
      (a * b * Nat.factorial (a * b - 1) *
        Nat.factorial (a - 1) * Nat.factorial (b - 1)) ^ 2 := by
  sorry

theorem minimum_unique {m k l : ℕ} (hk : InD m k) (hl : InD m l) : k = l := by
  sorry

theorem prime_no_rep {p k : ℕ} (hp : Nat.Prime p) : ¬ HasRep p k := by
  sorry

theorem product_separated_rep_six {a b : ℕ} (ha : 2 ≤ a) (hab : a + 2 ≤ b) : HasRep (a*b) 6 := by
  sorry

theorem product_adjacent_rep_four {a : ℕ} (ha : 2 ≤ a) : HasRep (a*(a+1)) 4 := by
  sorry

theorem product_equal_rep_two {a : ℕ} (ha : 2 ≤ a) : HasRep (a*a) 2 := by
  sorry

theorem product_has_rep_le_six {a b : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b) :
    ∃ k, 2 ≤ k ∧ k ≤ 6 ∧ HasRep (a*b) k := by
  sorry

theorem exists_minimum_le {m k : ℕ} (hk : 2 ≤ k) (hrep : HasRep m k) :
    ∃ j, j ≤ k ∧ InD m j := by
  sorry

theorem product_minimum_le_six {a b : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b) :
    ∃ k, k ≤ 6 ∧ InD (a * b) k := by
  sorry

theorem rep_527_six : HasRep 527 6 := by
  sorry

theorem rep_card_le {m k : ℕ} (hrep : HasRep m k) : k ≤ m := by
  sorry

theorem composite_minimum_le_six {m : ℕ} (hm : 2 ≤ m) (hp : ¬ Nat.Prime m) :
    ∃ k, k ≤ 6 ∧ InD m k := by
  sorry

theorem D_empty_above_six {k : ℕ} (hk : 6 < k) : D k = ∅ := by
  sorry

theorem countD_le (k n : ℕ) : countD k n ≤ n := by
  sorry

end Erdos374
