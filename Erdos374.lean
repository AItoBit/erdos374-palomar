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
  refine ⟨{a, b}, ?_, by simp, ?_, ?_⟩
  · simp [ne_of_lt hab]
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> omega
  · simpa [Finset.prod_pair, ne_of_lt hab] using hsq

/-- Classical adjacent-factor construction for every square greater than one. -/
theorem square_inD_two {r : ℕ} (hr : 1 < r) : InD (r ^ 2) 2 := by
  have hn : 0 < r ^ 2 := by positivity
  have hpred : 0 < r ^ 2 - 1 := by
    have : 1 < r ^ 2 := by nlinarith
    omega
  refine ⟨le_rfl, rep_two hpred (by omega) ?_, ?_⟩
  · refine ⟨r * Nat.factorial (r ^ 2 - 1), ?_⟩
    rw [← Nat.mul_factorial_pred (Nat.ne_of_gt hn)]
    ring
  · intro j hj hlt
    omega

/-- Two consecutive factorials expose exactly one unsquared factor. -/
theorem adjacent_identity {n : ℕ} (hn : 0 < n) :
    Nat.factorial n * Nat.factorial (n - 1) =
      n * Nat.factorial (n - 1) ^ 2 := by
  rw [← Nat.mul_factorial_pred (Nat.ne_of_gt hn)]
  ring

/-- The classical four-factor identity; distinctness is a separate obligation. -/
theorem four_factor_identity {r u : ℕ} (hr : 0 < r) (hu : 0 < u) :
    Nat.factorial (r ^ 2 * u) * Nat.factorial (r ^ 2 * u - 1) *
      Nat.factorial u * Nat.factorial (u - 1) =
      (r * u * Nat.factorial (r ^ 2 * u - 1) * Nat.factorial (u - 1)) ^ 2 := by
  have hn : 0 < r ^ 2 * u := by positivity
  rw [← Nat.mul_factorial_pred (Nat.ne_of_gt hn),
    ← Nat.mul_factorial_pred (Nat.ne_of_gt hu)]
  ring

/-- Erdős--Graham six-factor identity; it does not exclude shorter representations. -/
theorem six_factor_identity {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    Nat.factorial (a * b) * Nat.factorial (a * b - 1) *
      Nat.factorial a * Nat.factorial (a - 1) *
      Nat.factorial b * Nat.factorial (b - 1) =
      (a * b * Nat.factorial (a * b - 1) *
        Nat.factorial (a - 1) * Nat.factorial (b - 1)) ^ 2 := by
  have hn : 0 < a * b := Nat.mul_pos ha hb
  rw [← Nat.mul_factorial_pred (Nat.ne_of_gt hn),
    ← Nat.mul_factorial_pred (Nat.ne_of_gt ha),
    ← Nat.mul_factorial_pred (Nat.ne_of_gt hb)]
  ring

/-- A fixed m cannot have two different minimum cardinalities. -/
theorem minimum_unique {m k l : ℕ} (hk : InD m k) (hl : InD m l) : k = l := by
  rcases lt_trichotomy k l with h | h | h
  · exact False.elim (hl.2.2 k hk.1 h hk.2.1)
  · exact h
  · exact False.elim (hk.2.2 l hl.1 h hl.2.1)

theorem prime_no_rep {p k : ℕ} (hp : Nat.Prime p) : ¬ HasRep p k := by
  classical
  rintro ⟨s, hk, hps, hbound, hsquare⟩
  have hfactor : p.factorial = p * (p - 1).factorial := by
    have hsucc : p - 1 + 1 = p := by have := hp.two_le; omega
    simpa only [hsucc] using Nat.factorial_succ (p - 1)
  have hrest : ¬ p ∣ ∏ a ∈ s.erase p, a.factorial := by
    have hgeneral : ∀ t : Finset ℕ, (∀ a ∈ t, a < p) → ¬ p ∣ ∏ a ∈ t, a.factorial := by
      intro t
      induction t using Finset.induction_on with
      | empty => simp [hp.ne_one]
      | @insert a t hat ih =>
        intro hb
        rw [Finset.prod_insert hat]
        apply hp.not_dvd_mul
        · intro hd
          have := hp.dvd_factorial.mp hd
          have := hb a (Finset.mem_insert_self a t)
          omega
        · apply ih
          intro b hbt
          exact hb b (Finset.mem_insert_of_mem hbt)
    apply hgeneral
    intro a ha
    have hmem := Finset.mem_erase.mp ha
    have := (hbound a hmem.2).2
    omega
  have hprevious : ¬ p ∣ (p - 1).factorial := by
    intro hd
    have := hp.dvd_factorial.mp hd
    have := hp.two_le
    omega
  let t := (p - 1).factorial * ∏ a ∈ s.erase p, a.factorial
  have ht : ¬ p ∣ t := hp.not_dvd_mul hprevious hrest
  have hprod : ∏ a ∈ s, a.factorial = p * t := by
    rw [← Finset.mul_prod_erase s Nat.factorial hps, hfactor]
    simp [t, mul_assoc]
  obtain ⟨x, hx⟩ := hsquare
  have heq : p * t = x * x := by simpa [hprod] using hx
  have hpx : p ∣ x := by
    have hdiv : p ∣ x * x := by rw [← heq]; exact Nat.dvd_mul_right p t
    exact (hp.dvd_mul.mp hdiv).elim id id
  obtain ⟨y, hy⟩ := hpx
  have heq2 : p * t = p * (p * (y * y)) := by
    rw [heq, hy]
    ring
  have htEq : t = p * (y * y) := Nat.mul_left_cancel hp.pos heq2
  exact ht (htEq ▸ Nat.dvd_mul_right p (y * y))

theorem product_separated_rep_six {a b : ℕ} (ha : 2 ≤ a) (hab : a + 2 ≤ b) : HasRep (a*b) 6 := by
  have hb : 2 ≤ b := by omega
  have han0 : a + 2 ≤ a*b := by nlinarith
  have hbn0 : b + 2 ≤ a*b := by nlinarith
  have han : a < a*b - 1 := by omega
  have hbn : b < a*b - 1 := by omega
  have hne : a*b - 1 < a*b := by omega
  have h1 : 0 < a-1 := by omega
  have h2 : a-1 < a := by omega
  have h3 : a < b-1 := by omega
  have h4 : b-1 < b := by omega
  refine ⟨{a-1,a,b-1,b,a*b-1,a*b}, ?_, by simp, ?_, ?_⟩
  · simp [show a-1 ≠ a by omega, show a-1 ≠ b-1 by omega,
      show a-1 ≠ b by omega, show a-1 ≠ a*b-1 by omega,
      show a-1 ≠ a*b by omega, show a ≠ b-1 by omega,
      show a ≠ b by omega, show a ≠ a*b-1 by omega,
      show a ≠ a*b by omega, show b-1 ≠ b by omega,
      show b-1 ≠ a*b-1 by omega, show b-1 ≠ a*b by omega,
      show b ≠ a*b-1 by omega, show b ≠ a*b by omega,
      show a*b-1 ≠ a*b by omega]
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl|rfl|rfl|rfl|rfl|rfl <;> omega
  · have hprod : (∏ x ∈ ({a-1,a,b-1,b,a*b-1,a*b} : Finset ℕ), x.factorial) =
        (a-1).factorial*a.factorial*(b-1).factorial*b.factorial*(a*b-1).factorial*(a*b).factorial := by
      simp [Finset.prod_insert, show a-1 ≠ a by omega, show a-1 ≠ b-1 by omega,
        show a-1 ≠ b by omega, show a-1 ≠ a*b-1 by omega,
        show a-1 ≠ a*b by omega, show a ≠ b-1 by omega,
        show a ≠ b by omega, show a ≠ a*b-1 by omega,
        show a ≠ a*b by omega, show b-1 ≠ b by omega,
        show b-1 ≠ a*b-1 by omega, show b-1 ≠ a*b by omega,
        show b ≠ a*b-1 by omega, show b ≠ a*b by omega,
        show a*b-1 ≠ a*b by omega, mul_assoc]
    rw [hprod]
    refine ⟨a*b*(a-1).factorial*(b-1).factorial*(a*b-1).factorial, ?_⟩
    rw [← Nat.mul_factorial_pred (show a ≠ 0 by omega),
      ← Nat.mul_factorial_pred (show b ≠ 0 by omega),
      ← Nat.mul_factorial_pred (show a*b ≠ 0 by nlinarith)]
    ring
theorem product_adjacent_rep_four {a : ℕ} (ha : 2 ≤ a) : HasRep (a*(a+1)) 4 := by
  have hn0 : a+3 ≤ a*(a+1) := by nlinarith
  have h1 : 0 < a-1 := by omega
  have h2 : a-1 < a+1 := by omega
  have h3 : a+1 < a*(a+1)-1 := by omega
  have h4 : a*(a+1)-1 < a*(a+1) := by omega
  refine ⟨{a-1,a+1,a*(a+1)-1,a*(a+1)}, ?_, by simp, ?_, ?_⟩
  · simp [show a-1 ≠ a+1 by omega, show a-1 ≠ a*(a+1)-1 by omega,
      show a-1 ≠ a*(a+1) by omega, show a+1 ≠ a*(a+1)-1 by omega,
      show a+1 ≠ a*(a+1) by omega, show a*(a+1)-1 ≠ a*(a+1) by omega]
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl|rfl|rfl|rfl <;> omega
  · have hprod : (∏ x ∈ ({a-1,a+1,a*(a+1)-1,a*(a+1)} : Finset ℕ), x.factorial) =
        (a-1).factorial*(a+1).factorial*(a*(a+1)-1).factorial*(a*(a+1)).factorial := by
      simp [Finset.prod_insert, show a-1 ≠ a+1 by omega, show a-1 ≠ a*(a+1)-1 by omega,
        show a-1 ≠ a*(a+1) by omega, show a+1 ≠ a*(a+1)-1 by omega,
        show a+1 ≠ a*(a+1) by omega, show a*(a+1)-1 ≠ a*(a+1) by omega, mul_assoc]
    rw [hprod]
    refine ⟨a*(a+1)*(a-1).factorial*(a*(a+1)-1).factorial, ?_⟩
    rw [Nat.factorial_succ, ← Nat.mul_factorial_pred (show a ≠ 0 by omega),
      ← Nat.mul_factorial_pred (show a*(a+1) ≠ 0 by nlinarith)]
    ring

theorem product_equal_rep_two {a : ℕ} (ha : 2 ≤ a) : HasRep (a*a) 2 := by
  simpa [pow_two] using (square_inD_two (by omega : 1 < a)).2.1

theorem product_has_rep_le_six {a b : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b) :
    ∃ k, 2 ≤ k ∧ k ≤ 6 ∧ HasRep (a*b) k := by
  have hordered : ∀ x y : ℕ, 2 ≤ x → x ≤ y → ∃ k, 2 ≤ k ∧ k ≤ 6 ∧ HasRep (x*y) k := by
    intro x y hx hxy
    by_cases heq : x = y
    · subst y
      exact ⟨2, by omega, by omega, product_equal_rep_two hx⟩
    by_cases hadj : y = x+1
    · subst y
      exact ⟨4, by omega, by omega, product_adjacent_rep_four hx⟩
    exact ⟨6, by omega, by omega, product_separated_rep_six hx (by omega)⟩
  by_cases hab : a ≤ b
  · exact hordered a b ha hab
  · simpa [Nat.mul_comm] using hordered b a hb (by omega)

/-- Existence of a representation implies existence of its actual minimum. -/
theorem exists_minimum_le {m k : ℕ} (hk : 2 ≤ k) (hrep : HasRep m k) :
    ∃ j, j ≤ k ∧ InD m j := by
  classical
  have hex : ∃ j, 2 ≤ j ∧ HasRep m j := ⟨k, hk, hrep⟩
  refine ⟨Nat.find hex, Nat.find_min' hex ⟨hk, hrep⟩,
    (Nat.find_spec hex).1, (Nat.find_spec hex).2, ?_⟩
  intro j hj hlt hrepj
  exact (Nat.find_min hex hlt) ⟨hj, hrepj⟩

/-- Every nontrivial product has an actual minimum between two and six. -/
theorem product_minimum_le_six {a b : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b) :
    ∃ k, k ≤ 6 ∧ InD (a * b) k := by
  obtain ⟨j, hj, hj6, hrep⟩ := product_has_rep_le_six ha hb
  obtain ⟨k, hkj, hk⟩ := exists_minimum_le hj hrep
  exact ⟨k, le_trans hkj hj6, hk⟩

/-- Source-listed concrete endpoint: existence alone, not F(527)=6. -/
theorem rep_527_six : HasRep 527 6 := by
  simpa using (product_separated_rep_six (a := 17) (b := 31) (by norm_num) (by norm_num))

/-- Distinct positive indices bounded by m give at most m factorials. -/
theorem rep_card_le {m k : ℕ} (hrep : HasRep m k) : k ≤ m := by
  obtain ⟨s, hk, _, hbound, _⟩ := hrep
  have hs : s ⊆ Finset.Icc 1 m := by
    intro a ha
    have := hbound a ha
    simp only [Finset.mem_Icc]
    omega
  have hc := Finset.card_le_card hs
  simpa [hk] using hc

/-- Every composite endpoint at least two has a minimum no larger than six. -/
theorem composite_minimum_le_six {m : ℕ} (hm : 2 ≤ m) (hp : ¬ Nat.Prime m) :
    ∃ k, k ≤ 6 ∧ InD m k := by
  obtain ⟨a, b, ham, hbm, hab⟩ := (Nat.not_prime_iff_exists_mul_eq hm).mp hp
  have ha : 2 ≤ a := by
    by_contra h
    have : a = 0 ∨ a = 1 := by omega
    rcases this with rfl | rfl <;> simp at hab <;> omega
  have hb : 2 ≤ b := by
    by_contra h
    have : b = 0 ∨ b = 1 := by omega
    rcases this with rfl | rfl <;> simp at hab <;> omega
  simpa [hab] using product_minimum_le_six ha hb

/-- Classical support cutoff: the minimum can never exceed six. -/
theorem D_empty_above_six {k : ℕ} (hk : 6 < k) : D k = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro m hm
  change InD m k at hm
  have hmk := rep_card_le hm.2.1
  have hm2 : 2 ≤ m := by omega
  have hnp : ¬ Nat.Prime m := by
    intro hp
    exact prime_no_rep hp hm.2.1
  obtain ⟨j, hj, hjD⟩ := composite_minimum_le_six hm2 hnp
  have := minimum_unique hm hjD
  omega

/-- Elementary upper bound valid for every cardinality class. -/
theorem countD_le (k n : ℕ) : countD k n ≤ n := by
  classical
  unfold countD
  have h := Finset.card_filter_le (s := Finset.Icc 1 n) (p := fun m => InD m k)
  simpa using h

end Erdos374
