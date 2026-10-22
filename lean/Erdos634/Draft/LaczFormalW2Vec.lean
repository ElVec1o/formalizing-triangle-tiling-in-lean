import Erdos634.Draft.LaczFormalW2P2

/-!
# Rule W2: the two common vectors of the first two `cBA` tokens

Erdős #634, band program, rule W2.  Credit: AI assistant (item 3, band program), Beeson–Roșu, Beeson, Laczkovich,
Paliy.  UNAUDITED.

`w2_vectors`: two `cBA` tokens `X→Y` with apex `Z`, `P₁→P₂` with apex `G₂`, in an oriented target, have
`P₁ = A_p + e0`, `P₂ = P₁ + e0`, `G₁ = A_p + v`, `G₂ = P₁ + v` for the same vectors `e0` (length `c`, along the base) and
`v` (length `a`, along the left leg), `|v − e0| = b`, `cross e0 v > 0`.  Also: sides and angle facts of the tile `T'`.
-/

namespace Erdos634.LaczJunction.Walk

open Erdos634.Geometry Erdos634.TilePlacement Erdos634.LaczJunction Erdos634.LaczJunction.Grammar
open Erdos634.Draft.LaczFormal.Graph

variable {N : ℕ}

theorem w2_vectors {D : CongruentDissection N} {e f : ℕ} {α β γ : ℝ} {p q r : Fin 3}
    (S : BandSetup D e f α β γ p q r)
    (hori : 0 < cross (D.target.pts q - D.target.pts p) (D.target.pts r - D.target.pts p))
    {i1 i2 : Fin N} {P1 P2 G1 G2 : Plane}
    (t1 : BaseTok D p q (angOf α β γ) (lenOf (ta e f) (tb e f) (tc e f)) .c .B .A i1
      (D.target.pts p) P1 G1)
    (t2 : BaseTok D p q (angOf α β γ) (lenOf (ta e f) (tb e f) (tc e f)) .c .B .A i2 P1 P2 G2) :
    ∃ e0 v : Plane, P1 = D.target.pts p + e0 ∧ P2 = P1 + e0 ∧ G1 = D.target.pts p + v ∧ G2 = P1 + v ∧
      ‖e0‖ = (tc e f : ℝ) ∧ ‖v‖ = (ta e f : ℝ) ∧ ‖v - e0‖ = (tb e f : ℝ) ∧ 0 < cross e0 v ∧
      (∃ μ : ℝ, 0 < μ ∧ D.target.pts r - D.target.pts p = μ • v) ∧
      (∃ lam : ℝ, 0 < lam ∧ D.target.pts q - D.target.pts p = lam • e0) := by
  set LC := D.target.pts p with hLC
  set RC := D.target.pts q with hRC
  set AP := D.target.pts r with hAP
  obtain ⟨kk0, fi0, g0, hfk0, hgk0, hgf0, hk0, hf0, hg0, hYX0, hZX0, hγ0, hb0, hZa0, hleft0⟩ := cBA_data S hori t1
  obtain ⟨kk1, fi1, g1, hfk1, hgk1, hgf1, hk1, hf1, hg1, hYX1, hZX1, hγ1, hb1, hZa1, hleft1⟩ := cBA_data S hori t2
  have hapos : (0:ℝ) < ta e f := by exact_mod_cast a_pos e f S.he S.hef
  have hcpos : (0:ℝ) < tc e f := by
    have h1 := b_lt_c e f S.he S.hef
    have h2 := b_pos e f S.he S.hef
    exact_mod_cast (by omega : 0 < tc e f)
  have hL' : (ta e f : ℝ) < dist LC AP := S.haL
  have hLpos : 0 < dist LC AP := lt_trans hapos hL'
  have hB' : (tc e f : ℝ) < dist LC RC := S.hcB
  have hBpos : 0 < dist LC RC := lt_trans hcpos hB'
  set e0 : Plane := ((tc e f : ℝ) / dist LC RC) • (RC - LC) with he0def
  set v : Plane := ((ta e f : ℝ) / dist LC AP) • (AP - LC) with hvdef
  have hn1 : ‖RC - LC‖ = dist LC RC := by rw [dist_comm, dist_eq_norm]
  have hn2 : ‖AP - LC‖ = dist LC AP := by rw [dist_comm, dist_eq_norm]
  refine ⟨e0, v, by rw [← hYX0]; abel, by rw [← hYX1]; abel, by rw [← hZX0]; abel, by rw [← hZX1]; abel,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [he0def, norm_smul, Real.norm_of_nonneg (div_nonneg hcpos.le hBpos.le), hn1]
    field_simp
  · rw [hvdef, norm_smul, Real.norm_of_nonneg (div_nonneg hapos.le hLpos.le), hn2]
    field_simp
  · have e1 : v - e0 = G1 - P1 := by
      have h1 : G1 = LC + v := by rw [← hZX0]; abel
      have h2 : P1 = LC + e0 := by rw [← hYX0]; abel
      rw [h1, h2]; abel
    rw [e1, ← dist_eq_norm, dist_comm]; exact hb0
  · rw [he0def, hvdef, cross_smul_left, cross_smul_right]
    have hs1 : 0 < (tc e f : ℝ) / dist LC RC := div_pos hcpos hBpos
    have hs2 : 0 < (ta e f : ℝ) / dist LC AP := div_pos hapos hLpos
    exact mul_pos hs1 (mul_pos hs2 hori)
  · refine ⟨dist LC AP / (ta e f : ℝ), by positivity, ?_⟩
    rw [hvdef, smul_smul]; field_simp; simp
  · refine ⟨dist LC RC / (tc e f : ℝ), by positivity, ?_⟩
    rw [he0def, smul_smul]; field_simp; simp

end Erdos634.LaczJunction.Walk
