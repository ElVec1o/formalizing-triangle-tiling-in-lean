import Erdos634.Refl.CheckM
import Erdos634.Refl.SoundStage13

/-! Refl/SoundM2.lean -- `killsSoundM`: `killsSound` (Stage 11) for `NodeM` children.  Verbatim copy with
    `Node → NodeM`, `killsCheckM → killsCheckM`. -/

set_option linter.unusedSimpArgs false
open Erdos634.CertNode Erdos634.PlacementCompleteness Erdos634.SixPlacements
open Erdos634.Geometry (Plane)

namespace Refl

theorem killsSoundM (Dn : ℝ) (hD : 0 < Dn) (I : Inst) (hDn : (I.Dn : ℝ) = Dn)
    (htok : I.tgt.ok = true) (v d : Pt) (hvw : 0 < v.w) (hdw : 0 < d.w)
    (hdu : d.x * d.x + I.Dn * d.y * d.y = d.w * d.w)
    (cfg : List _root_.Tri) (hcfgok : ∀ t ∈ cfg, t.ok = true)
    {N : ℕ} (D : Erdos634.Geometry.CongruentDissection N)
    (htarget : D.target.carrier = I.tgt.carr Dn) (j : Fin N)
    (hreal : ∀ t ∈ cfg, ∃ i, i ≠ j ∧ (D.tile i).carrier = t.carr Dn)
    (R : NodeM → List _root_.Tri → Bool) :
    ∀ (ks : List Kill) (ps : List Place) (ch : List NodeM),
      (∀ p ∈ ps, 0 < p.l1 ∧ 0 < p.pd ∧ 0 < p.qd ∧ 0 < p.qn) →
      (∀ c p, p ∈ ps → R c (cfg ++ [placeTri I v d p]) = true →
        (D.tile j).carrier = (placeTri I v d p).carr Dn → False) →
      killsCheckM I cfg v d ks ps ch R = true →
      ∀ p ∈ ps, (D.tile j).carrier = (placeTri I v d p).carr Dn → False := by
  intro ks
  induction ks with
  | nil =>
    intro ps ch _ _ hk p hp
    cases ps with
    | nil => simp at hp
    | cons _ _ => simp [killsCheckM] at hk
  | cons k ks ih =>
    intro ps ch hpl hR hk p hp hj
    cases ps with
    | nil => simp [killsCheckM] at hk
    | cons p' ps =>
      have hpl' := hpl p' (List.mem_cons_self ..)
      obtain ⟨pl1, ppd, pqd, pqn⟩ := hpl'
      have htri := placeTri_ok I v d p' hvw hdw hdu (by exact_mod_cast (hDn ▸ hD : (0:ℝ) < I.Dn)) pl1 ppd pqd pqn
      have hwb : 0 < (placeTri I v d p').b.w := by
        show 0 < v.w * d.w; positivity
      have hwc : 0 < (placeTri I v d p').c.w := by
        show 0 < v.w * d.w * p'.pd * p'.qd; positivity
      by_cases hpp : p = p'
      · subst hpp
        -- the head kill applies
        cases k with
        | esc q e =>
          simp only [killsCheckM, killOk, Bool.and_eq_true, decide_eq_true_eq] at hk
          obtain ⟨hdet, -⟩ := hk
          cases q
          · simp only [Bool.false_eq_true, if_false] at hdet
            exact esc_sound_D Dn hD I htok D htarget _ j hj e _ hwb
              (Tri.vert_re_mem Dn (placeTri I v d p) 1) hdet
          · simp only [if_true] at hdet
            exact esc_sound_D Dn hD I htok D htarget _ j hj e _ hwc
              (Tri.vert_re_mem Dn (placeTri I v d p) 2) hdet
        | ovl m w =>
          simp only [killsCheckM, killOk] at hk
          cases hm : cfg[m]? with
          | none => rw [hm] at hk; simp at hk
          | some U =>
            rw [hm] at hk
            simp only [Bool.and_eq_true, decide_eq_true_eq] at hk
            obtain ⟨⟨⟨hw, h1⟩, h2⟩, -⟩ := hk
            have hUm : U ∈ cfg := List.mem_of_getElem? hm
            obtain ⟨i, hij, hi⟩ := hreal U hUm
            exact ovl_sound_D Dn hD D _ U htri (hcfgok U hUm) i j hij hi hj w hw h1 h2
        | child =>
          simp only [killsCheckM] at hk
          cases ch with
          | nil => simp at hk
          | cons c cs =>
            simp only [Bool.and_eq_true] at hk
            exact hR c p (List.mem_cons_self ..) hk.1 hj
      · have hpps : p ∈ ps := (List.mem_cons.mp hp).resolve_left hpp
        have hpl2 : ∀ q ∈ ps, 0 < q.l1 ∧ 0 < q.pd ∧ 0 < q.qd ∧ 0 < q.qn :=
          fun q hq => hpl q (List.mem_cons_of_mem _ hq)
        have hR2 : ∀ c q, q ∈ ps → R c (cfg ++ [placeTri I v d q]) = true →
            (D.tile j).carrier = (placeTri I v d q).carr Dn → False :=
          fun c q hq => hR c q (List.mem_cons_of_mem _ hq)
        cases k with
        | esc q e =>
          simp only [killsCheckM, Bool.and_eq_true] at hk
          exact ih ps ch hpl2 hR2 hk.2 p hpps hj
        | ovl m w =>
          simp only [killsCheckM] at hk
          cases hm : cfg[m]? with
          | none => simp [killOk, hm] at hk
          | some U =>
            simp only [killOk, hm, Bool.and_eq_true] at hk
            exact ih ps ch hpl2 hR2 hk.2 p hpps hj
        | child =>
          simp only [killsCheckM] at hk
          cases ch with
          | nil => simp at hk
          | cons c cs =>
            simp only [Bool.and_eq_true] at hk
            exact ih ps cs hpl2 hR2 hk.2 p hpps hj

#print axioms Refl.killsSoundM
end Refl
