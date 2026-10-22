-- Draft/FluxGrids.lean — layer 2, part 4: the rank-2 grid characters `L = ℤπ + ℤθ` (θ ∉ ℚπ),
-- `χ(jπ + kθ) = j + b·k (mod 2)`.  Imported directly by All.lean (stale "NOT imported" header corrected 2026-10-04).
-- Design: (private working notes, not included) §3.6 (`FluxGrids.lean`), specialised to the generator `π`
-- (`n = 1`), which is the grid of rows 11/12 and Beeson III Thm 1 (`θ = α/2 + π/2`, χ₊ = b = 0,
-- χ₋ = b = 1).  The `π/n` generator (`n = 3`, paper's `f_α`, `f_β`) is NOT built here.
--
-- Formalization debt; not progress on the three /goal outcomes.
import Erdos634.Draft.FluxWeight

open scoped Classical

namespace Erdos634.Geometry

/-- The parameter map `(j, k) ↦ jπ + kθ` into `ℝ/2πℤ`. -/
noncomputable def rank2Map (θ : ℝ) : ℤ × ℤ →+ Real.Angle where
  toFun p := p.1 • ((Real.pi : ℝ) : Real.Angle) + p.2 • ((θ : ℝ) : Real.Angle)
  map_zero' := by simp
  map_add' := by
    intro p q
    simp only [Prod.fst_add, Prod.snd_add, add_zsmul]
    abel

theorem rank2Map_apply (θ : ℝ) (j k : ℤ) :
    rank2Map θ (j, k) = (((j : ℝ) * Real.pi + (k : ℝ) * θ : ℝ) : Real.Angle) := by
  show j • ((Real.pi : ℝ) : Real.Angle) + k • ((θ : ℝ) : Real.Angle) = _
  rw [Real.Angle.coe_add, ← Real.Angle.coe_zsmul, ← Real.Angle.coe_zsmul, zsmul_eq_mul,
    zsmul_eq_mul]

/-- The parity `(j, k) ↦ j + b·k (mod 2)`. -/
def rank2Par (b : ZMod 2) : ℤ × ℤ →+ ZMod 2 where
  toFun p := (p.1 : ZMod 2) + b * (p.2 : ZMod 2)
  map_zero' := by simp
  map_add' := by
    intro p q
    simp only [Prod.fst_add, Prod.snd_add, Int.cast_add]
    ring

/-- **The kernel condition.**  `jπ + kθ ∈ 2πℤ` with `θ ∉ ℚπ` forces `k = 0` and `j` even. -/
theorem rank2_ker (θ : ℝ) (hθ : ¬ ∃ r : ℚ, θ = (r : ℝ) * Real.pi) (b : ZMod 2) (p : ℤ × ℤ)
    (hp : rank2Map θ p = 0) : rank2Par b p = 0 := by
  obtain ⟨j, k⟩ := p
  rw [rank2Map_apply, Real.Angle.coe_eq_zero_iff] at hp
  obtain ⟨m, hm⟩ := hp
  rw [zsmul_eq_mul] at hm
  by_cases hk : k = 0
  · subst hk
    have h2 : ((j : ℝ) - 2 * m) * Real.pi = 0 := by
      push_cast at hm
      linear_combination (-1 : ℝ) * hm
    have h3 : (j : ℝ) - 2 * m = 0 := (mul_eq_zero.mp h2).resolve_right Real.pi_ne_zero
    have hj : j = 2 * m := by exact_mod_cast (sub_eq_zero.mp h3)
    show (j : ZMod 2) + b * ((0 : ℤ) : ZMod 2) = 0
    rw [hj]
    push_cast
    have h20 : (2 : ZMod 2) = 0 := by decide
    rw [h20]
    ring
  · exfalso
    apply hθ
    have hk' : (k : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hk
    have h1 : (k : ℝ) * θ = (2 * m - j) * Real.pi := by
      linear_combination (-1 : ℝ) * hm
    refine ⟨((2 * m - j : ℤ) : ℚ) / (k : ℚ), ?_⟩
    push_cast
    rw [div_mul_eq_mul_div, eq_div_iff hk']
    linear_combination h1

/-- **The rank-2 grid character** `L = ℤπ + ℤθ`, `ψ(jπ + kθ) = (−1)^(j + b k)`. -/
noncomputable def GridChar.rank2 (θ : ℝ) (hθ : ¬ ∃ r : ℚ, θ = (r : ℝ) * Real.pi) (b : ZMod 2)
    (anchor : Real.Angle) : GridChar ℝ :=
  GridChar.ofHom (rank2Map θ) (rank2Par b) (rank2_ker θ hθ b) (1, 0)
    (by rw [rank2Map_apply]; push_cast; rw [one_mul, zero_mul, add_zero])
    (by show ((1 : ℤ) : ZMod 2) + b * ((0 : ℤ) : ZMod 2) = 1; push_cast; ring)
    anchor

theorem GridChar.rank2_mem (θ : ℝ) (hθ : ¬ ∃ r : ℚ, θ = (r : ℝ) * Real.pi) (b : ZMod 2)
    (anchor : Real.Angle) (j k : ℤ) :
    (((j : ℝ) * Real.pi + (k : ℝ) * θ : ℝ) : Real.Angle) ∈ (GridChar.rank2 θ hθ b anchor).L := by
  rw [← rank2Map_apply]
  exact AddMonoidHom.mem_range.mpr ⟨(j, k), rfl⟩

theorem GridChar.rank2_chi (θ : ℝ) (hθ : ¬ ∃ r : ℚ, θ = (r : ℝ) * Real.pi) (b : ZMod 2)
    (anchor : Real.Angle) (j k : ℤ) :
    (GridChar.rank2 θ hθ b anchor).chi (((j : ℝ) * Real.pi + (k : ℝ) * θ : ℝ) : Real.Angle)
      = if (j : ZMod 2) + b * (k : ZMod 2) = 0 then 1 else -1 := by
  rw [← rank2Map_apply]
  exact GridChar.ofHom_chi _ _ _ _ _ _ _ (j, k)

theorem GridChar.rank2_sq (θ : ℝ) (hθ : ¬ ∃ r : ℚ, θ = (r : ℝ) * Real.pi) (b : ZMod 2)
    (anchor : Real.Angle) :
    ∀ l ∈ (GridChar.rank2 θ hθ b anchor).L,
      (GridChar.rank2 θ hθ b anchor).chi l * (GridChar.rank2 θ hθ b anchor).chi l = 1 :=
  GridChar.ofHom_sq _ _ _ _ _ _ _

end Erdos634.Geometry

#print axioms Erdos634.Geometry.GridChar.rank2_chi
#print axioms Erdos634.Geometry.GridChar.rank2_sq
