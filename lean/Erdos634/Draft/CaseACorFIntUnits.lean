-- Draft/CaseACorFIntUnits.lean — closes the one Lean-level discrepancy (D-a) of the Part-0
-- statement-match audit of node A6 (Corollary F, Draft/CaseACorF.lean): PROOF_lemmaS.md P2 defines
-- R(a) with "every INTEGER k with gcd(k, n) = 1"; `relSpace` quantifies over k : ℕ.  They agree:
-- ((·)) is 1-periodic and k ≡ k mod n.  `lemmaS_finite_int` is Corollary F with the paper's ℤ-units.
-- Formalization debt; NOT /goal progress.  Imported into All.lean (All.lean:628).
import Erdos634.Draft.CaseACorF

namespace Erdos634.LemmaS

/-- R(a) with integer units, exactly as written in PROOF_lemmaS.md P2. -/
def relSpaceInt (n : ℕ) (a : Fin 3 → ℕ) : Submodule ℚ (Fin 3 → ℚ) :=
  ⨅ (k : ℤ) (_ : Int.gcd k n = 1),
    LinearMap.ker (∑ i, saw ((k * (a i : ℤ) : ℤ) / (n : ℚ)) •
      LinearMap.proj (R := ℚ) (φ := fun _ : Fin 3 => ℚ) i)

theorem saw_add_int (t : ℚ) (m : ℤ) : saw (t + m) = saw t := by
  unfold saw; rw [Int.fract_add_intCast]

theorem mem_relSpaceInt {n : ℕ} {a : Fin 3 → ℕ} {e : Fin 3 → ℚ} :
    e ∈ relSpaceInt n a ↔
      ∀ k : ℤ, Int.gcd k n = 1 → ∑ i, saw ((k * (a i : ℤ) : ℤ) / (n : ℚ)) * e i = 0 := by
  simp [relSpaceInt, Submodule.mem_iInf, LinearMap.mem_ker]

theorem relSpaceInt_eq {n : ℕ} (hn : 0 < n) (a : Fin 3 → ℕ) : relSpaceInt n a = relSpace n a := by
  ext e
  rw [mem_relSpaceInt, mem_relSpace]
  constructor
  · intro h k hk
    have := h k (by simpa [Int.gcd_natCast_natCast] using hk)
    simpa using this
  · intro h k hk
    have hn' : (0 : ℤ) < n := by exact_mod_cast hn
    set k' := (k % n).toNat with hk'
    have hk'z : (k' : ℤ) = k % n := Int.toNat_of_nonneg (Int.emod_nonneg _ hn'.ne')
    have hcop : k'.Coprime n := by
      have : Int.gcd (k % n) n = 1 := by rw [Int.gcd_emod]; exact hk
      rw [← hk'z] at this
      simpa [Int.gcd_natCast_natCast] using this
    have := h k' hcop
    rw [← this]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    congr 1
    have hdecomp : (k : ℚ) = (k' : ℚ) + (n : ℚ) * ((k / n : ℤ) : ℚ) := by
      have := Int.emod_add_mul_ediv k n
      rw [← hk'z] at this
      exact_mod_cast this.symm
    have hnq : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
    have : (((k * (a i : ℤ) : ℤ) : ℚ) / n) = ((k' * a i : ℕ) : ℚ) / n + ((k / n * a i : ℤ) : ℚ) := by
      push_cast
      rw [hdecomp]
      field_simp
    rw [this, saw_add_int]

/-- **Corollary F with the paper's integer units** (PROOF_lemmaS.md l.575, R(a) as defined in P2). -/
theorem lemmaS_finite_int {n : ℕ} (hn : n = 21 ∨ n = 28 ∨ n = 42 ∨ n = 66) (a : Fin 3 → ℕ)
    (hpos : ∀ i, 0 < a i) (hsum : ∑ i, a i = n)
    (hgcd : Nat.gcd (a 0) (Nat.gcd (a 1) (a 2)) = 1) :
    relSpaceInt n a = trivSpace n a := by
  have hn0 : 0 < n := by rcases hn with rfl | rfl | rfl | rfl <;> norm_num
  rw [relSpaceInt_eq hn0]
  exact lemmaS_finite hn a hpos hsum hgcd

end Erdos634.LemmaS

#print axioms Erdos634.LemmaS.relSpaceInt_eq
#print axioms Erdos634.LemmaS.lemmaS_finite_int
