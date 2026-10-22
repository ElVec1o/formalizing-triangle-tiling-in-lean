import Erdos634.Draft.LaczFormalWalkTok

/-!
# The base walk of a band dissection, as `BaseTok` entries

Erdős #634, base-`β` band.  Credit: Laczkovich (DCG 48 (2012), Sect. 4), AI assistant (item 3, band program),
Beeson–Roșu, Beeson, Paliy.  UNAUDITED.  Axiom-clean; no `sorry`.

`base_walk`: for a `BandSetup` whose target is positively oriented on `p → q` there is a walk `L` of tile steps
along the base `[A_p, A_q]` (`side_walk_exists`), with parameters `0 ≤ s < t ≤ 1` strictly increasing,
no repeated entry, and every entry a `BaseTok` of the token read off by `elemTok`.
-/

namespace Erdos634.LaczJunction.Walk

open Erdos634.Geometry Erdos634.TilePlacement Erdos634.LaczJunction Erdos634.LaczJunction.Grammar
open Erdos634.Draft.LaczFormal.Graph

variable {N : ℕ}

theorem mem_segment_of_param {X0 Y0 : Plane} {s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 1) :
    X0 + s • (Y0 - X0) ∈ segment ℝ X0 Y0 := by
  refine ⟨1 - s, s, by linarith, h0, by ring, ?_⟩
  module

theorem dist_param {X0 Y0 : Plane} {s : ℝ} (h0 : 0 ≤ s) :
    dist X0 (X0 + s • (Y0 - X0)) = s * dist X0 Y0 := by
  rw [dist_self_add_right, norm_smul, Real.norm_of_nonneg h0, dist_comm, dist_eq_norm]

theorem base_walk {D : CongruentDissection N} {e f : ℕ} {α β γ : ℝ} {p q r : Fin 3}
    (S : BandSetup D e f α β γ p q r)
    (hori : 0 < crs (toV2 (D.target.pts q - D.target.pts p)) (toV2 (D.target.pts r - D.target.pts p))) :
    ∃ L : List (Fin N × Plane × Plane),
      WalkT D.toDissection (toV2 (D.target.pts q - D.target.pts p)) (D.target.pts p) (D.target.pts q) L ∧
      (∀ x ∈ L, ∃ s t : ℝ, 0 ≤ s ∧ s < t ∧ t ≤ 1 ∧
        x.2.1 = D.target.pts p + s • (D.target.pts q - D.target.pts p) ∧
        x.2.2 = D.target.pts p + t • (D.target.pts q - D.target.pts p)) ∧
      L.Nodup ∧
      (∀ x ∈ L, ∃ kk fi g : Fin 3, fi ≠ kk ∧ g ≠ kk ∧ g ≠ fi ∧ (D.tile x.1).pts kk = x.2.1 ∧
        (D.tile x.1).pts fi = x.2.2 ∧
        0 < crs (toV2 (D.target.pts q - D.target.pts p)) (toV2 ((D.tile x.1).pts g - x.2.1)) ∧
        BaseTok D p q (angOf α β γ) (lenOf (ta e f) (tb e f) (tc e f))
        (elemTok D α β x).side (elemTok D α β x).left (elemTok D α β x).right x.1 x.2.1 x.2.2
        ((D.tile x.1).pts g)) := by
  have hne : D.target.pts p ≠ D.target.pts q := by
    intro h
    have : crs (toV2 (D.target.pts q - D.target.pts p)) (toV2 (D.target.pts r - D.target.pts p)) = 0 := by
      rw [← h]; simp [crs, toV2]
    linarith
  have hw : D.target.pts q - D.target.pts p ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  have hside : TriStep D.target (toV2 (D.target.pts q - D.target.pts p)) (D.target.pts p)
      (D.target.pts q) := by
    refine ⟨p, q, r, rfl, rfl, S.hpq.symm, S.hpr.symm, S.hqr.symm, ⟨?_, ?_⟩, hori⟩
    · simp [crs]; ring
    · have := nsq_pos (toV2_ne_zero hw)
      unfold dt nsq at *
      nlinarith
  obtain ⟨L, hL⟩ := side_walk_exists D.toDissection hside
  have hpar := walk_param hne hL (t0 := 0) (t1 := 1) (by simp) (by simp)
  obtain ⟨-, hpar, hnd⟩ := hpar
  refine ⟨L, hL, fun x hx => ?_, hnd, fun x hx => ?_⟩
  · obtain ⟨s, t, h0, h1, h2, h3, h4⟩ := hpar x hx
    exact ⟨s, t, h0, h1, h2, h3, h4⟩
  · obtain ⟨s, t, h0, h1, h2, h3, h4⟩ := hpar x hx
    have hstep := walkT_mem_step hL x hx
    obtain ⟨kk, fi, g, hk, hf, hfk, hgk, hgf, -, hleft⟩ := hstep
    refine ⟨kk, fi, g, hfk, hgk, hgf, hk, hf, hleft, ?_⟩
    have hnw : 0 < dist (D.target.pts p) (D.target.pts q) := dist_pos.mpr hne
    have := elem_baseTok S x.1 kk fi g hfk hgk hgf (U := x.2.1) (U' := x.2.2) hk hf rfl
      (by rw [h3]; exact mem_segment_of_param h0 (by linarith))
      (by rw [h4]; exact mem_segment_of_param (by linarith) h2)
      (by rw [h3, h4, dist_param h0, dist_param (by linarith)]; nlinarith)
    exact this

#print axioms base_walk

end Erdos634.LaczJunction.Walk
