-- Draft/LaczFormalR2Chunk.lean -- chunked kernel certificates: `allCertR n lo len` checks the first index a0 in [lo, lo+len) only, so that one `decide +kernel` stays small;
-- `allCert_of_chunks` glues consecutive chunks to `allCert n`.  UNAUDITED.  Credit: Laczkovich (1995, Lemma S); our CaseACorF.
import Erdos634.Draft.CaseACorF

namespace Erdos634.Draft.LaczFormal
open Erdos634.LemmaS

def allCertR (n lo len : ℕ) : Bool :=
  (List.range' lo len).all fun a0 => (List.range n).all fun a1 =>
    if 1 ≤ a0 ∧ 1 ≤ a1 ∧ a0 + a1 < n ∧ Nat.gcd a0 (Nat.gcd a1 (n - a0 - a1)) = 1 then
      cert n a0 a1 (n - a0 - a1) else true

theorem allCertR_split (n lo l1 l2 : ℕ) :
    allCertR n lo (l1 + l2) = (allCertR n lo l1 && allCertR n (lo + l1) l2) := by
  unfold allCertR
  have : List.range' lo (l1 + l2) = List.range' lo l1 ++ List.range' (lo + l1) l2 := by
    rw [List.range'_append_1] <;> simp
  rw [this, List.all_append]

theorem allCert_eq_R (n : ℕ) : allCert n = allCertR n 0 n := by
  unfold allCert allCertR
  rw [List.range_eq_range']

theorem allCertR_nil (n lo : ℕ) : allCertR n lo 0 = true := by
  simp [allCertR]

end Erdos634.Draft.LaczFormal
