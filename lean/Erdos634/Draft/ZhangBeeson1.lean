import Erdos634.Draft.Rows11_13AnyLabel
import Erdos634.Draft.FluxFRow15AnyLabel
import Erdos634.Draft.LaczFormalBZL7d6

/-!
# Zhang (arXiv 2512.22696v4) Theorem 1, the three rows citing Beeson III ("Theorem 3 of [2]", tile with `3 alpha + 2 beta = pi`)

Targets `(2a,b,a+b)` (Beeson row 14), `(2a,a,2b)` (row 15), and the isosceles targets `(a,a,a+2b)`, `(b,b,3a)`, `(a+b,a+b,a)` (rows 11, 12, 13); the
project's rationality rows `Row14/Row15.rational_any_label`, `Row11/12/13.rational_any_label` (Beeson III Thm 3 content, re-proved from the colouring
and flux theory in Lean) give `a = s c`, `b = (1 - s^2) c` with `s` rational, hence the tile sides are pairwise commensurable.
NOTE, UNAUDITED.  Credit: Zhang (arXiv 2512.22696v4, Thm 1), Beeson (arXiv 1206.2229, Thms 3, 4, 8, 12), Beeson-Zhang, Laczkovich.
-/

open scoped Classical
open Erdos634.Geometry Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement Erdos634.Draft.TheoremPConditional

namespace Erdos634.Draft.ZhangBeeson1
open Erdos634.Draft.LaczFormal.RG
open Erdos634.Geometry.Rows11_13AnyLabel

theorem comm_of_rat_sides {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (r : ℚ) (h1 : a = (r : ℝ) * c)
    (h2 : b = (1 - (r : ℝ) ^ 2) * c) : Comm a b ∧ Comm a c := by
  have c1 : Comm c a := comm_of_ratmul hc ha r h1
  have c2 : Comm c b := comm_of_ratmul hc hb (1 - r ^ 2) (by rw [h2]; push_cast; ring)
  exact ⟨comm_trans' (comm_symm' c1) c2, comm_symm' c1⟩

/-- Zhang Thm 1, Beeson-III rows. -/
theorem zhang_thm1_beeson3 {N : ℕ} (D : CongruentDissection N) {α β a b c : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (hrel : 3 * α + 2 * β = Real.pi)
    (h : D.model.ThreeAlphaData α β a b c)
    (hT : TgtAngles D (2 * α) β (α + β) ∨ TgtAngles D (2 * α) α (2 * β) ∨ TgtAngles D α α (α + 2 * β) ∨
      TgtAngles D β β (3 * α) ∨ TgtAngles D (α + β) (α + β) α) :
    Comm a b ∧ Comm a c := by
  have hpos := h
  obtain ⟨σ, h0, o0, h1, o1, h2, o2⟩ := h
  have ha : 0 < a := o0 ▸ D.model.oppLen_pos (σ 0)
  have hb : 0 < b := o1 ▸ D.model.oppLen_pos (σ 1)
  have hc : 0 < c := o2 ▸ D.model.oppLen_pos (σ 2)
  have n01 : σ 0 ≠ σ 1 := fun e => by have := σ.injective e; exact absurd this (by decide)
  have n20 : σ 2 ≠ σ 0 := fun e => by have := σ.injective e; exact absurd this (by decide)
  have n21 : σ 2 ≠ σ 1 := fun e => by have := σ.injective e; exact absurd this (by decide)
  have hh : D.model.ThreeAlphaData α β a b c := hpos
  rcases hT with ⟨τ, t0, t1, -⟩ | ⟨τ, t0, t1, -⟩ | ⟨τ, t0, t1, -⟩ | ⟨τ, t0, t1, -⟩ | ⟨τ, t0, t1, -⟩
  all_goals have tn : τ 0 ≠ τ 1 := fun e => by have := τ.injective e; exact absurd this (by decide)
  · obtain ⟨r, hr⟩ := Row14.rational_any_label D α β hα hrel n01 n20 n21 h0 h1 tn t0 t1
    rw [o0, o2] at hr
    exact comm_of_rat_sides ha hb hc r hr (b_of_rational hrel hh hr)
  · obtain ⟨r, hr, -⟩ := Row15.rational_any_label D α β hα hrel n01 n20 n21 h0 h1 tn t0 t1
    rw [o0, o2] at hr
    exact comm_of_rat_sides ha hb hc r hr (b_of_rational hrel hh hr)
  · obtain ⟨r, hr, hr2⟩ := Row11.rational_any_label D hα hrel hh tn t0 t1
    exact comm_of_rat_sides ha hb hc r hr hr2
  · obtain ⟨r, hr, hr2⟩ := Row12.rational_any_label D hα hrel hh tn t0 t1
    exact comm_of_rat_sides ha hb hc r hr hr2
  · obtain ⟨r, hr, hr2⟩ := Row13.rational_any_label D hα hrel hh tn t0 t1
    exact comm_of_rat_sides ha hb hc r hr hr2

end Erdos634.Draft.ZhangBeeson1
#print axioms Erdos634.Draft.ZhangBeeson1.zhang_thm1_beeson3
