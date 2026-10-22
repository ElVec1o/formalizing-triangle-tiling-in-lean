import Erdos634.Draft.LaczFormalColumnAdv

/-!
# Column Lemma, wall frame: copy of `LaczFormalMJBits` (LFrame blocks) for `WFrame`

Credit: AI assistant (Column Lemma proposal), Beeson–Roșu, Beeson, Laczkovich, Paliy.  UNAUDITED.  Generated from the audited
module by renaming `LFrame` to `WFrame`; the leg-specific facts are replaced as documented in `LaczFormalColumnLat`.
-/

namespace Erdos634.LaczCol

open Erdos634.Geometry Erdos634.TilePlacement Erdos634.LaczJunction Erdos634.LaczJunction.Walk
  Erdos634.LaczJunction.Grammar Erdos634.Draft.TraceCovering Erdos634.LaczMJ Erdos634.LaczWall Set

variable {N : ℕ} {D : CongruentDissection N} {e f : ℕ} {α β γ : ℝ} {p q r : Fin 3}

namespace WFrame


variable {D : CongruentDissection N} {e f : ℕ} {α β γ : ℝ} {p q r : Fin 3}
  (F : WFrame D e f α β γ p q r)

theorem lines_meet_once {P P' : Plane} {c1 c2 : ℝ}
    (h1 : cross (F.v - F.e0) P = c1) (h1' : cross (F.v - F.e0) P' = c1)
    (h2 : cross (-F.e0) P = c2) (h2' : cross (-F.e0) P' = c2) : P = P' := by
  have hd1 : cross (F.v - F.e0) (P' - P) = 0 := by rw [cross_sub_right, h1, h1']; ring
  have hd2 : cross F.e0 (P' - P) = 0 := by
    have : cross (-F.e0) (P' - P) = 0 := by rw [cross_sub_right, h2, h2']; ring
    have e1 : cross (-F.e0) (P' - P) = - cross F.e0 (P' - P) := by
      simp only [cross, PiLp.neg_apply]; ring
    linarith
  obtain ⟨t, ht⟩ := on_line_param F.e0_ne hd2
  rw [ht] at hd1
  have : cross (F.v - F.e0) (t • F.e0) = - t * cross F.e0 F.v := by
    rw [cross_smul_right]
    have : cross (F.v - F.e0) F.e0 = - cross F.e0 F.v := by
      simp only [cross, PiLp.sub_apply]; ring
    rw [this]; ring
  rw [this] at hd1
  have ht0 : t = 0 := by
    have := F.hcr
    rcases mul_eq_zero.mp (by linarith : (-t) * cross F.e0 F.v = 0) with h | h
    · linarith
    · linarith
  rw [ht0, zero_smul] at ht
  exact (sub_eq_zero.mp ht).symm

theorem Dp_eq (j : ℝ) (m lv : ℝ) :
    F.pt (m + 1 - j) (lv + j) = F.pt (m + 1) lv + j • (F.v - F.e0) := by
  simp only [pt]; module

theorem Dp_not_mem_open {m lv : ℝ} (hu0 : F.v - F.e0 ≠ 0) {k s : ℕ} :
    F.pt (m + 1 - s) (lv + s) ∉
      openSegment ℝ (F.pt (m + 1 - k) (lv + k)) (F.pt (m + 1 - (k + 1)) (lv + (k + 1))) := by
  intro h
  rw [F.Dp_eq, F.Dp_eq, F.Dp_eq] at h
  rw [openSegment_param (X := F.pt (m + 1) lv) (u := F.v - F.e0) (by simp)] at h
  obtain ⟨x, hx, hxs⟩ := h
  have := lm_injective hu0 hxs
  rw [min_eq_left (by linarith), max_eq_right (by linarith)] at hx
  have h1 : (k : ℝ) < s := by rw [← this]; exact hx.1
  have h2 : (s : ℝ) < k + 1 := by rw [← this]; exact hx.2
  have h1' : k < s := by exact_mod_cast h1
  have h2' : s < k + 1 := by exact_mod_cast h2
  omega


end WFrame

end Erdos634.LaczCol
