import Erdos634.Draft.BeesonT17Alg

/-!
# Witness for `thm17_alg_complete`: N = 77, M = 5, s = 1/2

NOTE, UNAUDITED.  Credit: Beeson (arXiv 1206.2229 v4, Thm 17; the 77-tiling is Beeson's Fig./Table 3 entry), Laczkovich, Beeson-Zhang.
Computation (Python, 2026-10-22): `77 (1/2)^2 (5/2)^2 = 77 * 25/16 = 25 * (7/4)(11/4)`.  Hypotheses are satisfied; no H1 used.
-/

namespace Erdos634.BeesonColoring

set_option maxRecDepth 100000 in
theorem thm17_wit77 : ((5 : ℕ), (1 : ℕ), (2 : ℕ)) ∈ thm17Sol 77 := by
  have := thm17_alg_complete (N := 77) (M := 5) (q := (1 : ℚ) / 2) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  have hn : ((1 : ℚ) / 2).num = 1 := by
    have := Rat.num_div_eq_of_coprime (a := (1 : ℤ)) (b := (2 : ℤ)) (by norm_num) (by norm_num)
    simpa using this
  have hd : ((1 : ℚ) / 2).den = 2 := by
    have := Rat.den_div_eq_of_coprime (a := (1 : ℤ)) (b := (2 : ℤ)) (by norm_num) (by norm_num)
    simpa using this
  rw [hn, hd] at this
  exact this

end Erdos634.BeesonColoring

#print axioms Erdos634.BeesonColoring.thm17_wit77
