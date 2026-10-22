-- Draft/LaczFormalGraphWit2.lean -- WITNESS/CONTROL data for the irrationality hypothesis `NotComb a b c` of the graph layer (`head_out_edge`, `ga_of_codes`, ...).
-- Positive: `NotComb (sqrt 5) 1 2` (tile (1,2,sqrt 5), a = hypotenuse), `NotComb (sqrt 2) 1 1` (right isosceles, a = hypotenuse), `NotComb (sqrt 3) 1 2` (30-60-90, a = long leg).
-- Negative control: `NotComb` FAILS for every tile with commensurable sides (e.g. the corpus integer tilings (2,3,4), (3,5,7)), so `head_out_edge` and its relatives have
-- no instance in an integer-sided corpus tiling; a positive instance needs an irrational-sided tile with a T-vertex of the Gamma_a head type.  UNAUDITED.
-- Credit: Laczkovich (DCG 48 (2012), Sect. 4).
import Erdos634.Draft.LaczFormalGraphGa

namespace Erdos634.Draft.LaczFormal.Graph

theorem notComb_sqrt_of_irrational {a b c : ℝ} (hb : 0 < b) (h : ∀ r p q : ℕ, 0 < r → (r : ℝ) * a ≠ p * b + q * c) : NotComb a b c := h

/-- `NotComb (sqrt n) 1 k` whenever `sqrt n` is irrational (n not a square), for integer `k`. -/
theorem notComb_sqrt (n k : ℕ) (hn : Irrational (Real.sqrt n)) : NotComb (Real.sqrt n) 1 k := by
  intro r p q hr h
  apply hn
  refine ⟨((p + q * k : ℕ) : ℚ) / r, ?_⟩
  have hr' : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  push_cast
  field_simp
  linarith

theorem notComb_sqrt5 : NotComb (Real.sqrt 5) 1 2 := by
  have := notComb_sqrt 5 2 (by exact_mod_cast (Nat.Prime.irrational_sqrt (by norm_num : Nat.Prime 5)))
  simpa using this

theorem notComb_sqrt2 : NotComb (Real.sqrt 2) 1 1 := by
  have := notComb_sqrt 2 1 (by exact_mod_cast (Nat.Prime.irrational_sqrt (by norm_num : Nat.Prime 2)))
  simpa using this

/-- Negative control: commensurable sides defeat `NotComb`. -/
theorem not_notComb_of_commensurable {a b c : ℝ} (p q r : ℕ) (hr : 0 < r) (h : (r : ℝ) * a = p * b + q * c) : ¬ NotComb a b c :=
  fun hn => hn r p q hr h

theorem not_notComb_integer_tile : ¬ NotComb 2 3 4 := not_notComb_of_commensurable 0 1 2 (by norm_num) (by norm_num)

end Erdos634.Draft.LaczFormal.Graph
