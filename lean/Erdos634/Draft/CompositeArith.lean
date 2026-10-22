/-
Draft/CompositeArith.lean — arithmetic leaves for N = 14, 42, 62, 70 (all squarefree, N ≡ 2 mod 4) used by
`CompositeFinal2`.  Nothing here is geometric.  UNAUDITED; formalization debt, NOT /goal progress.
No sorry, no native_decide (`decide +kernel` only on closed finite Nat/ZMod statements).
Contents: squarefree; valuations; non-residues; `IsoQRef N` (refined S3 arithmetic); `IsoH9 N`; `HArith N`;
not-sum-of-two-squares; `NoF4 N` (14, 62 only; FALSE for 42 and 70: 42 = 6·7 = (1+5)(2+5), 70 = 7·10 = (3+4)(6+4));
S2 arithmetic `S2Arith N` (14, 62: 2-adic obstruction).
-/
import Erdos634.Draft.CompositeS3Refined
import Erdos634.Draft.CaseALemmaHN
import Erdos634.Draft.ChainCompositeR8

namespace Erdos634.Draft.CompositeArith

open Erdos634.Geometry Erdos634.Draft.CompositeGen2

set_option synthInstance.maxSize 1000
set_option synthInstance.maxHeartbeats 400000

theorem s3Closed_of_isoQRef (N : ℕ) (h : IsoQRef N) : S3Closed N :=
  fun D α β a b c hα hrel hd t₀ t₁ ht h0 h1 => Row11.excluded_isoQRef_any_label D hα hrel hd ht h0 h1 h

/-- Bounded-check form of `IsoQRef` for `N ≤ 100`. -/
theorem isoQRef_of_check (N : ℕ) (hN0 : 0 < N) (hN : N ≤ 100)
    (hchk : ∀ e : ℕ, e < 10 → ∀ d : ℕ, d < 8 → ∀ m : ℕ, m < 31 → 1 ≤ e → 1 ≤ d → e ^ 2 + 4 * e * d + 2 * d ^ 2 ∣ N →
      N * d = m ^ 2 * ((2 * e + d) * (e ^ 2 + 4 * e * d + 2 * d ^ 2)) → False) : IsoQRef N := by
  apply isoQRef_of_dvd_case
  intro e d m he hd hQ heq
  have hle : e ^ 2 + 4 * e * d + 2 * d ^ 2 ≤ N := Nat.le_of_dvd hN0 hQ
  have he' : e < 10 := by nlinarith
  have hd' : d < 8 := by nlinarith
  have hK : 1 ≤ (2 * e + d) * (e ^ 2 + 4 * e * d + 2 * d ^ 2) := by nlinarith
  have hm : m < 31 := by
    by_contra h
    have h31 : 31 ≤ m := by omega
    have : 961 ≤ m ^ 2 := by nlinarith
    have h2 : m ^ 2 ≤ N * d := by rw [heq]; exact Nat.le_mul_of_pos_right _ (by omega)
    nlinarith
  exact hchk e he' d hd' m hm he hd hQ heq

theorem isoQRef_14 : IsoQRef 14 := isoQRef_of_check 14 (by norm_num) (by norm_num) (by decide +kernel)
theorem isoQRef_42 : IsoQRef 42 := isoQRef_of_check 42 (by norm_num) (by norm_num) (by decide +kernel)
theorem isoQRef_62 : IsoQRef 62 := isoQRef_of_check 62 (by norm_num) (by norm_num) (by decide +kernel)
/-- N = 70: the reduced Row-11 equation HAS an arithmetic solution (e, d, m) = (2, 1, 1), Q = 14, 70·1 = 1²·5·14.
So `IsoQRef 70` is FALSE and S3 at 70 is NOT closed by arithmetic: `S3Closed 70` stays a named hypothesis. -/
theorem not_isoQRef_70 : ¬ IsoQRef 70 := fun h => h 2 1 1 (by norm_num) (by norm_num) (by decide) (by norm_num)

/-- Negative control: `IsoQDvd N` is FALSE at these N (so the original S3 leaf cannot be used). -/
theorem not_isoQDvd_14 : ¬ IsoQDvd 14 := fun h => by have := h 1 1 le_rfl le_rfl (by decide) (by decide); omega
theorem not_isoQDvd_42 : ¬ IsoQDvd 42 := fun h => by have := h 1 1 le_rfl le_rfl (by decide) (by decide); omega
theorem not_isoQDvd_62 : ¬ IsoQDvd 62 := fun h => by have := h 1 3 le_rfl (by norm_num) (by decide) (by decide); omega
theorem not_isoQDvd_70 : ¬ IsoQDvd 70 := fun h => by have := h 1 1 le_rfl le_rfl (by decide) (by decide); omega

end Erdos634.Draft.CompositeArith

#print axioms Erdos634.Draft.CompositeArith.isoQRef_14
#print axioms Erdos634.Draft.CompositeArith.isoQRef_42
#print axioms Erdos634.Draft.CompositeArith.isoQRef_62
#print axioms Erdos634.Draft.CompositeArith.not_isoQRef_70
#print axioms Erdos634.Draft.CompositeArith.not_isoQDvd_62
