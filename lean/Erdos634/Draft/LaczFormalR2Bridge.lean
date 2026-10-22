-- Draft/LaczFormalR2Bridge.lean -- glue from chunked LIGHT certificates (`Erdos634.Lite.allCertR`, checked in small processes) to `CaseACorF.allCert n = true`.  UNAUDITED.
-- Credit: Laczkovich (1995, Lemma S); our CaseACorF.
import Erdos634.Draft.CaseACorF
import Erdos634.Draft.LaczFormalR2Lite

namespace Erdos634.Draft.LaczFormal
open Erdos634.LemmaS

theorem lite_cert (n a0 a1 a2 : ℕ) : Erdos634.Lite.cert n a0 a1 a2 = cert n a0 a1 a2 := rfl

theorem lite_allCertR (n lo len : ℕ) : Erdos634.Lite.allCertR n lo len =
    (List.range' lo len).all fun a0 => (List.range n).all fun a1 =>
      if 1 ≤ a0 ∧ 1 ≤ a1 ∧ a0 + a1 < n ∧ Nat.gcd a0 (Nat.gcd a1 (n - a0 - a1)) = 1 then
        cert n a0 a1 (n - a0 - a1) else true := rfl

/-- Chunks of `len` consecutive first indices, starting at the points of `L`, certify `allCert n`. -/
theorem allCert_of_lite_chunks (n len : ℕ) (L : List ℕ)
    (hL : ∀ lo ∈ L, Erdos634.Lite.allCertR n lo len = true)
    (hcov : ∀ a0 < n, ∃ lo ∈ L, lo ≤ a0 ∧ a0 < lo + len) : allCert n = true := by
  unfold allCert
  rw [List.all_eq_true]
  intro a0 ha0
  rw [List.mem_range] at ha0
  obtain ⟨lo, hlo, h1, h2⟩ := hcov a0 ha0
  have := hL lo hlo
  rw [lite_allCertR, List.all_eq_true] at this
  exact this a0 (by rw [List.mem_range']; exact ⟨a0 - lo, by omega, by omega⟩)

end Erdos634.Draft.LaczFormal
