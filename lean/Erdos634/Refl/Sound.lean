import Erdos634.Refl.Check
import Erdos634.CertNode

/-! Soundness PROTOTYPE for the reflective checker: the two once-and-for-all bridge lemmas
    (Farkas certificates; det3/homogeneous points <-> CertNode.ef / rp / rtri). -/

open Erdos634.CertNode Erdos634.Geometry

namespace Refl

def evalL (l : Lin) (X Y : ℝ) : ℝ := (l.α : ℝ) * X + (l.β : ℝ) * Y + (l.γ : ℝ)

def Sat (c : Lin × Bool) (X Y : ℝ) : Prop := if c.2 then 0 < evalL c.1 X Y else 0 ≤ evalL c.1 X Y

/-- Farkas: the certificate arithmetic forces `a X + b Y + g` to be `≥ 0` (resp. `> 0`),
    so a negative (resp. zero-with-strict) constant is a contradiction. -/
theorem fk_sound (X Y : ℝ) : ∀ (cs : List (Lin × Bool)) (ms : List Nat) (a b g : Int) (st : Bool),
    (∀ c ∈ cs, Sat c X Y) →
    0 ≤ (a : ℝ) * X + b * Y + g → (st = true → 0 < (a : ℝ) * X + b * Y + g) →
    fk cs ms a b g st = true → False := by
  intro cs
  induction cs with
  | nil =>
    intro ms a b g st _ h0 hs hk
    cases ms <;> simp only [fk, Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true, decide_eq_true_eq] at hk <;>
    · obtain ⟨⟨rfl, rfl⟩, hg | ⟨hg, hst⟩⟩ := hk
      · simp at h0; have : (g : ℝ) < 0 := by exact_mod_cast hg
        linarith
      · simp at h0 hs; have := hs hst; simp [hg] at this
  | cons c cs ih =>
    intro ms a b g st hcs h0 hs hk
    cases ms with
    | nil =>
      simp only [fk, Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true, decide_eq_true_eq] at hk
      obtain ⟨⟨rfl, rfl⟩, hg | ⟨hg, hst⟩⟩ := hk
      · simp at h0; have : (g : ℝ) < 0 := by exact_mod_cast hg
        linarith
      · simp at h0 hs; have := hs hst; simp [hg] at this
    | cons m ms =>
      obtain ⟨l, s⟩ := c
      have hc := hcs (l, s) (by simp)
      simp only [fk] at hk
      refine ih ms _ _ _ _ (fun c hc' => hcs c (by simp [hc'])) ?_ ?_ hk
      · have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
        have : 0 ≤ evalL l X Y := by
          unfold Sat at hc; split_ifs at hc <;> linarith
        push_cast
        nlinarith [mul_nonneg hm this, h0, show (a : ℝ) * X + b * Y + g + m * evalL l X Y
            = (a + m * l.α : ℝ) * X + (b + m * l.β : ℝ) * Y + (g + m * l.γ : ℝ) by unfold evalL; ring]
      · intro hst
        push_cast
        have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
        have hL : 0 ≤ evalL l X Y := by
          unfold Sat at hc; split_ifs at hc <;> linarith
        have e : (a : ℝ) * X + b * Y + g + m * evalL l X Y
            = (a + m * l.α : ℝ) * X + (b + m * l.β : ℝ) * Y + (g + m * l.γ : ℝ) := by unfold evalL; ring
        simp only [Bool.or_eq_true, Bool.and_eq_true, bne_iff_ne, ne_eq] at hst
        rcases hst with h | ⟨hs', hm0⟩
        · have := hs h; nlinarith [mul_nonneg hm hL]
        · have hmpos : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm0
          have : 0 < evalL l X Y := by
            unfold Sat at hc; simp [hs'] at hc; exact hc
          nlinarith [mul_pos hmpos this]

theorem farkas_sound (X Y : ℝ) (cs : List (Lin × Bool)) (ms : List Nat)
    (hsat : ∀ c ∈ cs, Sat c X Y) (h : farkas cs ms = true) : False :=
  fk_sound X Y cs ms 0 0 0 false hsat (by simp) (by simp) h


/-! ## Homogeneous points and the CertNode vocabulary -/

/-- semantic X-coordinate `x/w` -/
noncomputable def _root_.Pt.X (p : Pt) : ℝ := (p.x : ℝ) / p.w
noncomputable def _root_.Pt.Y (p : Pt) : ℝ := (p.y : ℝ) / p.w

/-- the sign of the rational edge functional is the sign of the integer determinant -/
theorem det3_ef (a b c : Pt) (ha : (a.w : ℝ) ≠ 0) (hb : (b.w : ℝ) ≠ 0) (hc : (c.w : ℝ) ≠ 0) :
    (det3 a b c : ℝ) = a.w * b.w * c.w * ef a.X a.Y b.X b.Y c.X c.Y := by
  unfold det3 ef Pt.X Pt.Y
  push_cast
  field_simp
  ring

/-- an edge line evaluated at `(X, Y)` is `wa wb · ef` -/
theorem evalL_linOf (a b : Pt) (ha : (a.w : ℝ) ≠ 0) (hb : (b.w : ℝ) ≠ 0) (X Y : ℝ) :
    evalL (linOf a b) X Y = a.w * b.w * ef a.X a.Y b.X b.Y X Y := by
  unfold evalL linOf ef Pt.X Pt.Y
  push_cast
  field_simp
  ring


end Refl
