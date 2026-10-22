-- Draft/LaczFormalK1Kill.lean -- killing by K1 (`lemmaK_K1`): if for some unit k the numbers s_T(k) = sum_i {k a_i/n} and s_ABC(k) = sum_j {k u_j/n} differ,
-- no congruent dissection has tile a/n and target u/n.  Instances for the K1-failing (tile, target) pairs of the exceptional n.  UNAUDITED.
-- Credit: Laczkovich (1995, conjugate tilings); our `KConj.lemmaK`, `Case A` K1.
import Erdos634.Draft.LaczFormalCondEConjKill

open scoped BigOperators Classical
open Erdos634.Geometry Erdos634.KConj Erdos634.TilePlacement Erdos634.Draft.TheoremPConditional
open Erdos634.LemmaKStar Erdos634.Geometry.CaseA.LemmaK1

namespace Erdos634.Draft.LaczFormal

variable {N : ℕ}

theorem K1_kill (D : CongruentDissection N) (n : ℕ) (hn : 0 < n) (a u : Fin 3 → ℕ)
    (σ τ : Equiv.Perm (Fin 3))
    (hm : ∀ i, D.model.angleAt (σ i) = (a i : ℕ) * Real.pi / n)
    (ht : ∀ j, D.target.angleAt (τ j) = (u j : ℕ) * Real.pi / n)
    {k : ℤ} (hk : Int.gcd k n = 1) (t t' : ℚ) (hne : t ≠ t')
    (hs : sT n a k = t) (hu : ∑ j, Int.fract (((k * (u j : ℤ) : ℤ) : ℚ) / n) = t') : False := by
  have hpi := Real.pi_pos
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  set A : Fin 3 → ℕ := fun l => a (σ.symm l) with hA
  have hmA : ∀ l, D.model.angleAt l = A l * Real.pi / n := fun l => by
    have := hm (σ.symm l); simpa [hA] using this
  obtain ⟨idx, hidx⟩ := KConj.exists_idx D A hmA
  obtain ⟨hf, -⟩ := KConj.lemmaK D hn A hmA idx hidx
  have hK1 := lemmaK_K1 D hn A hmA (fig D idx) hf hk
  have huu : ∀ j, uu A (fig D idx) (τ j) = u j := by
    intro j
    have h1 := hf (τ j)
    rw [ht j] at h1
    have : ((u j : ℕ) : ℝ) * Real.pi / n = ((uu A (fig D idx) (τ j) : ℕ) : ℝ) * Real.pi / n := h1
    have h2 : ((u j : ℕ) : ℝ) = ((uu A (fig D idx) (τ j) : ℕ) : ℝ) := by
      field_simp at this; exact this
    exact_mod_cast h2.symm
  have hsT : sT n A k = t := by rw [← hs]; exact sT_perm a σ k
  have hsABC : sABC n A (fig D idx) k = t' := by
    rw [← hu, sABC]
    rw [← Equiv.sum_comp τ (fun j => xv n A (fig D idx) k j)]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    unfold xv
    rw [huu j]
  apply hne
  rw [← hsT, ← hsABC]
  exact hK1

theorem fract_int (z : ℤ) (n : ℕ) (hn : 0 < n) : Int.fract ((z : ℚ) / n) = ((z % n : ℤ) : ℚ) / n := by
  have hn' : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [Int.fract, Rat.floor_intCast_div_natCast]
  have : (z % (n : ℤ)) = z - n * (z / n) := Int.emod_def z n
  rw [this]; push_cast; field_simp

/-- `K1_kill` in `TileAngles`/`TgtAngles` form with scalar data; the arithmetic side is closed by `norm_num` through `fract_int`. -/
theorem K1_kill_tri (D : CongruentDissection N) (n : ℕ) (hn : 0 < n) (a0 a1 a2 u0 u1 u2 : ℕ)
    (hT : TileAngles D (a0 * Real.pi / n) (a1 * Real.pi / n) (a2 * Real.pi / n))
    (hG : TgtAngles D (u0 * Real.pi / n) (u1 * Real.pi / n) (u2 * Real.pi / n))
    {k : ℤ} (hk : Int.gcd k n = 1) (t t' : ℚ) (hne : t ≠ t')
    (hs : (((k * a0 : ℤ) % n : ℤ) : ℚ) / n + (((k * a1 : ℤ) % n : ℤ) : ℚ) / n + (((k * a2 : ℤ) % n : ℤ) : ℚ) / n = t)
    (hu : (((k * u0 : ℤ) % n : ℤ) : ℚ) / n + (((k * u1 : ℤ) % n : ℤ) : ℚ) / n + (((k * u2 : ℤ) % n : ℤ) : ℚ) / n = t') :
    False := by
  obtain ⟨σ, h0, h1, h2⟩ := hT
  obtain ⟨τ, g0, g1, g2⟩ := hG
  refine K1_kill D n hn ![a0, a1, a2] ![u0, u1, u2] σ τ ?_ ?_ hk t t' hne ?_ ?_
  · intro i; fin_cases i <;> simp [h0, h1, h2]
  · intro j; fin_cases j <;> simp [g0, g1, g2]
  · rw [← hs]; simp only [sT, yv, Fin.sum_univ_three, fract_int _ n hn]
    simp
  · rw [← hu]; simp only [Fin.sum_univ_three, fract_int _ n hn]
    simp

end Erdos634.Draft.LaczFormal
