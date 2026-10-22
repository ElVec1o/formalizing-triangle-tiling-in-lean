-- Draft/LaczFormalIIcGenWitD2.lean -- WITNESS of the GENERIC Case IIc block (alpha != beta), step D2: kernel evaluation of the area-sum identity and the corner-count checks
-- (the alpha/beta corner balance is checked in index chunks to bound the kernel memory).  NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012)), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIIcGenWitB

namespace Erdos634.Draft.LaczFormal.GenWit

open Z2

theorem sums_ok : sumZ (tileTab.map fun t => absZ (detT t)) = sumZ (fanTab.map fun t => absZ (detT t)) := by decide +kernel
theorem cor_ok : corB = true := by decide +kernel

def fpt (p : Pt) : Bool := alphaL.count p == betaL.count p
def regRow (i : Nat) : Bool := fpt (alphaL.getD i (zero, zero)) && fpt (betaL.getD i (zero, zero))
def regRows (a b : Nat) : Bool := (List.range' a (b - a)).all regRow

theorem reg_0_34 : regRows 0 34 = true := by decide +kernel
theorem reg_34_68 : regRows 34 68 = true := by decide +kernel
theorem reg_68_102 : regRows 68 102 = true := by decide +kernel
theorem reg_102_136 : regRows 102 136 = true := by decide +kernel
theorem reg_136_170 : regRows 136 170 = true := by decide +kernel
theorem reg_170_204 : regRows 170 204 = true := by decide +kernel

theorem regRows_spec {a b k : Nat} (h : regRows a b = true) (h1 : a ≤ k) (h2 : k < b) : regRow k = true := by
  unfold regRows at h
  rw [List.all_eq_true] at h
  exact h k (List.mem_range'.mpr ⟨k - a, by omega, by omega⟩)

theorem regRow_all (k : Nat) (hk : k < 204) : regRow k = true := by
  by_cases c0 : k < 34
  · exact regRows_spec reg_0_34 (by omega) c0
  by_cases c34 : k < 68
  · exact regRows_spec reg_34_68 (by omega) c34
  by_cases c68 : k < 102
  · exact regRows_spec reg_68_102 (by omega) c68
  by_cases c102 : k < 136
  · exact regRows_spec reg_102_136 (by omega) c102
  by_cases c136 : k < 170
  · exact regRows_spec reg_136_170 (by omega) c136
  by_cases c170 : k < 204
  · exact regRows_spec reg_170_204 (by omega) c170
  omega

end Erdos634.Draft.LaczFormal.GenWit
