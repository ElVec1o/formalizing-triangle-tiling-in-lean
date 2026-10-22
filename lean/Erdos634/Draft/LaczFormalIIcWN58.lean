-- Draft/LaczFormalIIcWN58.lean -- Laczkovich (DCG 48 (2012), Sect. 6.3), Lemma 6.2 (`IIcNoKites`), step (i), part 2:
-- for non-adjacent vertices a, b of a strictly convex polygon, the neighbours c(a+1), c(a-1) of c a lie strictly on opposite sides of the line through c b and c a.
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 6.3), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIIcWN57

open scoped Classical Fin.NatCast
open Complex Filter Topology

namespace Erdos634.Draft.LaczFormal.WN

variable {N : ℕ} [NeZero N]

theorem im_div_swap {u v : ℂ} (hu : u ≠ 0) (hv : v ≠ 0) :
    (v / u).im = -(u / v).im / Complex.normSq (u / v) ∧ 0 < Complex.normSq (u / v) := by
  have e : v / u = (u / v)⁻¹ := (inv_div u v).symm
  rw [e, Complex.inv_im]
  exact ⟨rfl, Complex.normSq_pos.2 (div_ne_zero hu hv)⟩

theorem side_opposite {c : Fin N → ℂ} {τ : ℝ} (hinj : Function.Injective c) (hn : 3 ≤ N) (hS : SC c τ) (a b : Fin N)
    (hb : b ≠ a) (hb1 : b ≠ a + 1) (hb2 : b ≠ a - 1) :
    0 < τ * sideFn (c b) (c a - c b) (c (a + 1)) ∧ τ * sideFn (c b) (c a - c b) (c (a - 1)) < 0 := by
  have h1 := hS a b hb hb1
  have h2 := hS (a - 1) b hb2 (by rw [sub_add_cancel]; exact hb)
  rw [sub_add_cancel] at h2
  have hd : c b - c a ≠ 0 := sub_ne_zero.2 (fun h => hb (hinj h))
  have he : c (a + 1) - c a ≠ 0 := sub_ne_zero.2 (nd hinj hn a)
  have hf : c a - c (a - 1) ≠ 0 := by
    have := nd hinj hn (a - 1)
    rw [sub_add_cancel] at this
    exact sub_ne_zero.2 this
  set e := c (a + 1) - c a with hedef
  set f := c a - c (a - 1) with hfdef
  set d := c b - c a with hddef
  unfold sideFn at h1 h2 ⊢
  have s1 : (c b - c a) / e = d / e := rfl
  have s2 : (c b - c (a - 1)) / f = d / f + 1 := by
    have : c b - c (a - 1) = d + f := by rw [hddef, hfdef]; ring
    rw [this, add_div, div_self hf]
  rw [s1] at h1
  rw [s2] at h2
  simp only [Complex.add_im, Complex.one_im, add_zero] at h2
  have v1 : (c (a + 1) - c b) / (c a - c b) = 1 - e / d := by
    have : c (a + 1) - c b = e - d := by rw [hedef, hddef]; ring
    have h' : c a - c b = -d := by rw [hddef]; ring
    rw [this, h', div_neg, sub_div, div_self hd]; ring
  have v2 : (c (a - 1) - c b) / (c a - c b) = 1 + f / d := by
    have : c (a - 1) - c b = -d - f := by rw [hddef, hfdef]; ring
    have h' : c a - c b = -d := by rw [hddef]; ring
    rw [this, h']
    have hd' : -d ≠ 0 := neg_ne_zero.2 hd
    field_simp
    ring
  rw [v1, v2]
  simp only [Complex.sub_im, Complex.add_im, Complex.one_im, zero_sub, zero_add]
  obtain ⟨k1, n1⟩ := im_div_swap hd he
  obtain ⟨k2, n2⟩ := im_div_swap hd hf
  constructor
  · rw [k1]
    have : τ * -(-(d / e).im / Complex.normSq (d / e)) = (τ * (d / e).im) / Complex.normSq (d / e) := by ring
    rw [this]
    exact div_pos h1 n1
  · rw [k2]
    have : τ * (-(d / f).im / Complex.normSq (d / f)) = -((τ * (d / f).im) / Complex.normSq (d / f)) := by ring
    rw [this]
    have := div_pos h2 n2
    linarith

end Erdos634.Draft.LaczFormal.WN
