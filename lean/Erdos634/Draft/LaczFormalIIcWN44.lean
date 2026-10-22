-- Draft/LaczFormalIIcWN44.lean -- Laczkovich (DCG 48 (2012)), Sect. 6.3, Lemma 6.2 (`IIcNoKites`), step (h), part 5:
-- `chord_signs`: cutting a simple polygon q along a chord whose open part misses q and along which `wind q = c`: the two pieces have orientations
-- sigma1 = - sigma2 if c = 0 (exterior chord) and sigma1 = sigma2 = c if c <> 0 (interior chord).
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 6.3), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIIcWN43

open scoped Classical Fin.NatCast
open Complex Filter Topology

namespace Erdos634.Draft.LaczFormal.WN

variable {n : ℕ} [NeZero n]

/-- The winding dichotomy with sign `σ`. -/
def Dich (q : Fin n → ℂ) (σ : ℝ) : Prop := (σ = 1 ∨ σ = -1) ∧ ∀ z : ℂ, z ∉ edgeSet q → wind q z = 0 ∨ wind q z = σ

theorem sign_arith {σ1 σ2 A B c : ℝ} (h1 : σ1 = 1 ∨ σ1 = -1) (h2 : σ2 = 1 ∨ σ2 = -1) (hA : A = 0 ∨ A = σ1)
    (hA' : A - 1 = 0 ∨ A - 1 = σ1) (hB : B = 0 ∨ B = σ2) (hB' : B + 1 = 0 ∨ B + 1 = σ2) (hc : A + B = c) :
    (c = 0 → σ1 = -σ2) ∧ (c ≠ 0 → σ1 = c ∧ σ2 = c) := by
  rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl <;> rcases hA with hA | hA <;> rcases hA' with hA' | hA' <;>
    rcases hB with hB | hB <;> rcases hB' with hB' | hB' <;>
    refine ⟨fun h => ?_, fun h => ?_⟩ <;> first | (exfalso; linarith) | (exfalso; apply h; linarith) | (constructor <;> linarith) | norm_num

theorem phi_phi_last (a : Fin n) {d : ℕ} (hdn : d ≤ n) : phi (phi a d) (n - d) = a := by
  unfold phi
  rw [add_assoc, ← Nat.cast_add, Nat.add_sub_cancel' hdn]; simp

end Erdos634.Draft.LaczFormal.WN
