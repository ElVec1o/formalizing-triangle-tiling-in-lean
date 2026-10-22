import Erdos634.Refl.SoundE1

/-! Refl/SoundE2.lean -- soundness of the edge-blocked kind (`edgeBlockedOk`): the clockwise wedge at `v` lies outside the
    target when `d` runs positively along a target edge through `v`.  UNAUDITED. -/

set_option linter.unusedSimpArgs false
open Erdos634.CertNode Erdos634.PlacementCompleteness
open Erdos634.Geometry (Plane)

namespace Refl

/-- pure-real core: moving clockwise off the edge line goes strictly to the negative side. -/
theorem edge_cw_real (σ Dn : ℝ) (hσ : 0 < σ) (hσ2 : σ ^ 2 = Dn) (hDn : 0 < Dn)
    (Ax Ay Bx By vX vY dX dY t s : ℝ)
    (hv : (Bx - Ax) * (vY - Ay) - (vX - Ax) * (By - Ay) = 0)
    (hpar : dX * (By - Ay) - dY * (Bx - Ax) = 0)
    (hpos : 0 < dX * (Bx - Ax) + dY * (By - Ay)) (ht : 0 < t) (hs : 0 < s) :
    (Bx - Ax) * ((vY + t * (dY - s * dX / σ)) - Ay) - ((vX + t * (dX + s * σ * dY)) - Ax) * (By - Ay) < 0 := by
  set ΔX := Bx - Ax
  set ΔY := By - Ay
  have key : 0 < dX * ΔX + Dn * dY * ΔY := by
    have hΔ : 0 < ΔX ^ 2 + ΔY ^ 2 := by
      by_contra hc
      have h1 : ΔX = 0 := by nlinarith [sq_nonneg ΔX, sq_nonneg ΔY]
      have h2 : ΔY = 0 := by nlinarith [sq_nonneg ΔX, sq_nonneg ΔY]
      rw [h1, h2] at hpos; simp at hpos
    have hΔ' : 0 < ΔX ^ 2 + Dn * ΔY ^ 2 := by
      by_contra hc
      have a1 := sq_nonneg ΔX
      have a2 := mul_nonneg hDn.le (sq_nonneg ΔY)
      have h1 : ΔX ^ 2 = 0 := by linarith
      have h2 : Dn * ΔY ^ 2 = 0 := by linarith
      have h3 : ΔY ^ 2 = 0 := by
        rcases mul_eq_zero.mp h2 with h | h
        · exact absurd h hDn.ne'
        · exact h
      rw [h1, h3] at hΔ; simp at hΔ
    have id : (dX * ΔX + Dn * dY * ΔY) * (ΔX ^ 2 + ΔY ^ 2)
        = (dX * ΔX + dY * ΔY) * (ΔX ^ 2 + Dn * ΔY ^ 2) := by
      have : dX * ΔY = dY * ΔX := by linarith
      have e1 : dX * ΔX * ΔY ^ 2 = dY * ΔX ^ 2 * ΔY := by
        calc dX * ΔX * ΔY ^ 2 = (dX * ΔY) * ΔX * ΔY := by ring
          _ = dY * ΔX * ΔX * ΔY := by rw [this]
          _ = dY * ΔX ^ 2 * ΔY := by ring
      nlinarith [e1]
    have : 0 < (dX * ΔX + Dn * dY * ΔY) * (ΔX ^ 2 + ΔY ^ 2) := by
      rw [id]; exact mul_pos hpos hΔ'
    exact (pos_iff_pos_of_mul_pos this).mpr hΔ
  have e : ΔX * ((vY + t * (dY - s * dX / σ)) - Ay) - ((vX + t * (dX + s * σ * dY)) - Ax) * ΔY
      = (ΔX * (vY - Ay) - (vX - Ax) * ΔY) + t * (dY * ΔX - dX * ΔY)
        - t * s * (dX * ΔX + σ ^ 2 * dY * ΔY) / σ := by
    field_simp
    ring
  rw [e, hv, hσ2]
  have h0 : dY * ΔX - dX * ΔY = 0 := by linarith
  rw [h0]
  have : 0 < t * s * (dX * ΔX + Dn * dY * ΔY) / σ := by positivity
  linarith


theorem hblocked_edge_sound (Dn : ℝ) (hD : 0 < Dn) (I : Inst) (hDn : (I.Dn : ℝ) = Dn)
    (htok : I.tgt.ok = true) (n : Node) (hvw : 0 < n.v.w) (hdw : 0 < n.d.w) (e : Nat)
    (h : edgeBlockedOk I n.v n.d e = true)
    {N : ℕ} (D : Erdos634.Geometry.CongruentDissection N)
    (htarget : D.target.carrier = I.tgt.carr Dn) (S : Finset (Fin N)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t s : ℝ, 0 < t → t < δ → 0 < s → s < δ →
      (n.v.re Dn) + t • ((n.d.re Dn) - s • perp (n.d.re Dn)) ∉ unfilled D.toDissection S := by
  refine ⟨1, one_pos, fun t s ht _ hs _ hU => ?_⟩
  have hσ := sr_pos hD
  have hσ2 := sr_sq hD
  set A := I.tgt.vert (e % 3) with hA
  set B := I.tgt.vert ((e + 1) % 3) with hB
  have wA := Tri.vert_w_pos I.tgt htok (e % 3)
  have wB := Tri.vert_w_pos I.tgt htok ((e + 1) % 3)
  rw [← hA] at wA; rw [← hB] at wB
  have rA := Pt.w_pos A wA
  have rB := Pt.w_pos B wB
  have rv := Pt.w_pos n.v hvw
  have rd := Pt.w_pos n.d hdw
  simp only [edgeBlockedOk, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  -- the point, as `rp X Y`
  set X : ℝ := n.v.X + t * (n.d.X + s * sr Dn * n.d.Y) with hX
  set Y : ℝ := n.v.Y + t * (n.d.Y - s * n.d.X / sr Dn) with hY
  have hp : (n.v.re Dn) + t • ((n.d.re Dn) - s • perp (n.d.re Dn)) = rp Dn X Y := by
    apply plane_ext
    · simp only [Pt.re, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul, perp_zero, rp_zero, rp_one, hX]
      ring
    · simp only [Pt.re, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul, perp_one, rp_zero, rp_one, hY]
      field_simp
  have hmem : rp Dn X Y ∈ I.tgt.carr Dn := by
    rw [← hp, ← htarget]; exact hU.1
  have hnn := Tri.edge_nonneg Dn hD I.tgt htok X Y hmem (e % 3) (Nat.mod_lt _ (by norm_num))
  rw [← Tri.edge_mod] at hnn
  have hedge : I.tgt.edge e = linOf A B := by simp [_root_.Tri.edge, hA, hB]
  rw [hedge, evalL_linOf A B (Pt.w_ne _ wA) (Pt.w_ne _ wB)] at hnn
  -- real hypotheses
  have e0 := det3_ef A B n.v (Pt.w_ne _ wA) (Pt.w_ne _ wB) (Pt.w_ne _ hvw)
  have h1' : (det3 A B n.v : ℝ) = 0 := by exact_mod_cast h1
  rw [h1'] at e0
  have hv : ef A.X A.Y B.X B.Y n.v.X n.v.Y = 0 := by
    have : (A.w : ℝ) * B.w * n.v.w * ef A.X A.Y B.X B.Y n.v.X n.v.Y = 0 := e0.symm
    rcases mul_eq_zero.mp this with h | h
    · exfalso; exact (mul_pos (mul_pos rA rB) rv).ne' h
    · exact h
  have hpar : n.d.X * (B.Y - A.Y) - n.d.Y * (B.X - A.X) = 0 := by
    have hc : ((n.d.x * (vsub B A).2 - n.d.y * (vsub B A).1 : ℤ) : ℝ) = 0 := by exact_mod_cast h2
    simp only [vsub, Pt.X, Pt.Y] at hc ⊢
    push_cast at hc
    field_simp at hc ⊢
    nlinarith [hc]
  have hpos : 0 < n.d.X * (B.X - A.X) + n.d.Y * (B.Y - A.Y) := by
    have hc : (0 : ℝ) < ((n.d.x * (vsub B A).1 + n.d.y * (vsub B A).2 : ℤ) : ℝ) := by exact_mod_cast h3
    simp only [vsub, Pt.X, Pt.Y] at hc ⊢
    push_cast at hc
    have hw : (0:ℝ) < n.d.w * A.w * B.w := by positivity
    have eq : (n.d.x : ℝ) / n.d.w * ((B.x : ℝ) / B.w - A.x / A.w) + n.d.y / n.d.w * ((B.y : ℝ) / B.w - A.y / A.w)
        = ((n.d.x : ℝ) * (B.x * A.w - A.x * B.w) + n.d.y * (B.y * A.w - A.y * B.w)) / (n.d.w * A.w * B.w) := by
      field_simp
    rw [eq]; exact div_pos hc hw
  have key := edge_cw_real (sr Dn) Dn hσ hσ2 hD A.X A.Y B.X B.Y n.v.X n.v.Y n.d.X n.d.Y t s hv hpar hpos ht hs
  unfold ef at hnn
  have : 0 ≤ (A.w : ℝ) * B.w * ((B.X - A.X) * (Y - A.Y) - (X - A.X) * (B.Y - A.Y)) := hnn
  have := mul_nonneg_iff_of_pos_left (mul_pos rA rB) |>.mp this
  linarith

end Refl
