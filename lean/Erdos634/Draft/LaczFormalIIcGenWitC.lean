-- Draft/LaczFormalIIcGenWitC.lean -- WITNESS of the GENERIC Case IIc block (alpha != beta), step C: kernel evaluation of the pairwise separation of the 204 tiles (row chunks, to bound the kernel memory).  NOTE, UNAUDITED.
-- Credit: Laczkovich (DCG 48 (2012)), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIIcGenWitB

namespace Erdos634.Draft.LaczFormal.GenWit

open Z2

/-- row `k`: tile `k` is separated from every later tile. -/
def rowOK (k : Nat) : Bool := (tileTab.drop (k + 1)).all (sepB (tileTab.getD k default))
def rowsB (a b : Nat) : Bool := (List.range' a (b - a)).all rowOK

theorem rows_0_11 : rowsB 0 11 = true := by decide +kernel
theorem rows_11_23 : rowsB 11 23 = true := by decide +kernel
theorem rows_23_36 : rowsB 23 36 = true := by decide +kernel
theorem rows_36_50 : rowsB 36 50 = true := by decide +kernel
theorem rows_50_65 : rowsB 50 65 = true := by decide +kernel
theorem rows_65_82 : rowsB 65 82 = true := by decide +kernel
theorem rows_82_102 : rowsB 82 102 = true := by decide +kernel
theorem rows_102_127 : rowsB 102 127 = true := by decide +kernel
theorem rows_127_168 : rowsB 127 168 = true := by decide +kernel
theorem rows_168_204 : rowsB 168 204 = true := by decide +kernel

theorem rowsB_spec {a b k : Nat} (h : rowsB a b = true) (h1 : a ≤ k) (h2 : k < b) : rowOK k = true := by
  unfold rowsB at h
  rw [List.all_eq_true] at h
  exact h k (List.mem_range'.mpr ⟨k - a, by omega, by omega⟩)

theorem rowOK_all (k : Nat) (hk : k < 204) : rowOK k = true := by
  by_cases c0 : k < 11
  · exact rowsB_spec rows_0_11 (by omega) c0
  by_cases c11 : k < 23
  · exact rowsB_spec rows_11_23 (by omega) c11
  by_cases c23 : k < 36
  · exact rowsB_spec rows_23_36 (by omega) c23
  by_cases c36 : k < 50
  · exact rowsB_spec rows_36_50 (by omega) c36
  by_cases c50 : k < 65
  · exact rowsB_spec rows_50_65 (by omega) c50
  by_cases c65 : k < 82
  · exact rowsB_spec rows_65_82 (by omega) c65
  by_cases c82 : k < 102
  · exact rowsB_spec rows_82_102 (by omega) c82
  by_cases c102 : k < 127
  · exact rowsB_spec rows_102_127 (by omega) c102
  by_cases c127 : k < 168
  · exact rowsB_spec rows_127_168 (by omega) c127
  by_cases c168 : k < 204
  · exact rowsB_spec rows_168_204 (by omega) c168
  omega

end Erdos634.Draft.LaczFormal.GenWit
