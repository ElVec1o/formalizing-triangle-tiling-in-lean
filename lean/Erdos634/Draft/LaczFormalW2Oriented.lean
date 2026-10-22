import Erdos634.Draft.LaczFormalW2More

/-!
# Rule W2 for an oriented target

Erdős #634, band program, rule W2 (`PROOF_W2.md`).  Credit: AI assistant (item 3, band program), Beeson–Roșu (the tile, the
relation lattice), Beeson, Laczkovich (fans, chord covers), Paliy.  UNAUDITED.

`w2_oriented`: in the band setting (`e ≥ 2`, `f ≥ 3`, left leg `> 2a`, target oriented counterclockwise `(p,q,r)`),
the base word cannot begin `cBA, cBA, X` with `X ∈ {bAG, cAB, bGA}`.

Proof (the chord version of `PROOF_W2.md`; the fan lemma of `LaczFormalFanSucc` is not needed here).  With the vectors
`e0 = P₁ − A_p`, `v = G₁ − A_p`, `u = v − e0`, `V₂ = A_p + 2v`, `G₂ = midpoint P₂ V₂`:
* if no tile edge above the line `G₁G₂` passes through `G₂`: the far side of `[G₁,G₂]` is one `c`-edge (`D3`), a tile
  `(G₁ β, G₂ α, V₂ γ)`; with it the far side of `[P₂,V₂]` is two `b`-edges (`D2`); the one on `[G₂,V₂]` presents `γ` at `G₂`
  (no double `γ` at `V₂`) and the one on `[P₂,G₂]` presents `γ` at `G₂` (five tiles overfill `G₂`) or `γ` at `P₂`
  (boundary figure at `P₂` against the third token);
* otherwise a tile `S₀` presents `π` at `G₂`; no edge on the line `P₂G₂` passes through `G₂` (the angles at `G₂` would
  overflow); the far side of `[P₂,G₂]` is one `b`-edge (`b` is written only as `b`), and as above.
-/

namespace Erdos634.LaczJunction.Walk

open Erdos634.Geometry Erdos634.TilePlacement Erdos634.LaczJunction Erdos634.LaczJunction.Grammar
open Erdos634.Draft.LaczFormal.Graph Erdos634.Geometry.Dissection Erdos634.VertexFigureReal
open Erdos634.Draft.TraceCovering

variable {N : ℕ}

set_option maxHeartbeats 2000000 in
theorem w2_core {D : CongruentDissection N} {e f : ℕ} {α β γ : ℝ} {p q r : Fin 3}
    (S : BandSetup D e f α β γ p q r) (he2 : 2 ≤ e) (hf3 : 3 ≤ f)
    (hori : 0 < cross (D.target.pts q - D.target.pts p) (D.target.pts r - D.target.pts p))
    (hL2 : 2 * (ta e f : ℝ) < dist (D.target.pts p) (D.target.pts r))
    {i1 i2 : Fin N} {P1 P2 G1 G2 : Plane}
    (t1 : BaseTok D p q (angOf α β γ) (lenOf (ta e f) (tb e f) (tc e f)) .c .B .A i1
      (D.target.pts p) P1 G1)
    (t2 : BaseTok D p q (angOf α β γ) (lenOf (ta e f) (tb e f) (tc e f)) .c .B .A i2 P1 P2 G2)
    (hP2seg : P2 ∈ openSegment ℝ (D.target.pts p) (D.target.pts q))
    {Q : Prop}
    (hB : ∀ (iW : Fin N) (kP kG : Fin 3), kP ≠ kG → (D.tile iW).pts kP = P2 → (D.tile iW).pts kG = G2 →
      (D.tile iW).localAngle P2 = γ → (D.tile iW).localAngle G2 = α → iW ≠ i2 →
      (∀ j, cross (G2 - P2) ((D.tile iW).pts j - P2) ≤ 0) → Q) : Q := by
  classical
  obtain ⟨hαβ, hβγ, hαγ, hab, hbc, hac⟩ := BandSetup.distinct S
  set LC := D.target.pts p with hLC
  set RC := D.target.pts q with hRC
  set AP := D.target.pts r with hAP
  have hne : LC ≠ RC := by
    intro h
    have : cross (RC - LC) (AP - LC) = 0 := by rw [← h]; simp [cross]
    linarith
  obtain ⟨e0, v, hP1, hP2, hG1, hG2, hce, hva, hub, hcr, ⟨μ, hμ, hAPv⟩, ⟨lam, hlam, hRCe⟩⟩ :=
    w2_vectors S hori t1 t2
  have hP1 : P1 = LC + e0 := hP1
  have hG1 : G1 = LC + v := hG1
  have hAPv : AP - LC = μ • v := hAPv
  have hRCe : RC - LC = lam • e0 := hRCe
  obtain ⟨i', kP, kG, kH, hGP, hHP, hHG, hi'1, hi'2, hP', hG', hH', hγ'⟩ := w2_step1_tok S hori t1 t2
  obtain ⟨kk0, fi0, g0, hfk0, hgk0, hgf0, hk0, hf0, hg0, -, -, hγ0, hb0, hZa0, hleft0⟩ := cBA_data S hori t1
  obtain ⟨kk1, fi1, g1, hfk1, hgk1, hgf1, hk1, hf1, hg1, -, -, hγ1, hb1, hZa1, hleft1⟩ := cBA_data S hori t2
  have hapos : (0:ℝ) < ta e f := by exact_mod_cast a_pos e f S.he S.hef
  have hbpos : (0:ℝ) < tb e f := by exact_mod_cast b_pos e f S.he S.hef
  have hcpos : (0:ℝ) < tc e f := by
    have h1 := b_lt_c e f S.he S.hef
    have h2 := b_pos e f S.he S.hef
    exact_mod_cast (by omega : 0 < tc e f)
  have hαπ : α ≠ Real.pi := by intro h; have := S.hrel; have := S.hβ0; linarith [S.hα0]
  have hβπ : β ≠ Real.pi := by intro h; have := S.hrel; have := S.hα0; linarith [Real.pi_pos]
  have hγπ : γ ≠ Real.pi := by intro h; have := S.hγdef; have := S.hrel; have := S.hα0; have := S.hβ0; linarith
  have hγ0' : γ ≠ 0 := by intro h; have := S.hγdef; have := S.hα0; have := S.hβ0; linarith
  have ndg : ∀ {w : Plane}, w ∈ frontier D.target.carrier → w ∉ Set.range D.target.pts → ∀ i j : Fin N, i ≠ j →
      (D.tile i).localAngle w = γ → (D.tile j).localAngle w = γ → False := by
    intro w hw hnw i j hij h1 h2
    exact congruentDissection_no_double_gamma D α β γ hαβ hαγ hαπ S.hα0.ne' hβγ hβπ S.hβ0.ne' hγπ hγ0'
      Real.pi_ne_zero S.hγdef S.hrel S.hirr S.hα' S.hβ' S.hγ' hw hnw i j hij h1 h2
  set u : Plane := v - e0 with hudef
  set V2 : Plane := LC + (2:ℝ) • v with hV2def
  have hu : u = G2 - P2 := by rw [hudef, hG2, hP2]; abel
  have hV2 : V2 = P2 + (2:ℝ) • u := by
    rw [hV2def, hudef, hP2, hP1]; module
  have hG2e : G2 = G1 + e0 := by rw [hG2, hG1, hP1]; abel
  have he0 : e0 ≠ 0 := by intro h; rw [h] at hcr; simp [cross] at hcr
  have hv0 : v ≠ 0 := by intro h; rw [h] at hcr; simp [cross] at hcr
  -- μ > 2
  have hμ2 : 2 < μ := by
    have h1 : dist LC AP = μ * (ta e f : ℝ) := by
      rw [dist_comm, dist_eq_norm, hAPv, norm_smul, Real.norm_of_nonneg hμ.le, hva]
    rw [h1] at hL2
    nlinarith
  have hG1seg : G1 ∈ openSegment ℝ LC AP := by
    have : G1 = LC + (1 / μ) • (AP - LC) := by rw [hG1, hAPv, smul_smul, one_div, inv_mul_cancel₀ hμ.ne', one_smul]
    rw [this]
    exact mem_open_param (by positivity) (by rw [div_lt_one hμ]; linarith)
  have hV2seg : V2 ∈ openSegment ℝ LC AP := by
    have : V2 = LC + (2 / μ) • (AP - LC) := by
      rw [hV2def, hAPv, smul_smul, div_mul_cancel₀ _ hμ.ne']
    rw [this]
    exact mem_open_param (by positivity) (by rw [div_lt_one hμ]; linarith)
  obtain ⟨hint1, hbef1, hbey1⟩ := chord_geometry D.target S.hpq S.hpr S.hqr hP2seg hV2seg
  have hG2lm : G2 = AffineMap.lineMap P2 V2 (1 / 2 : ℝ) := by
    rw [AffineMap.lineMap_apply]; simp only [vsub_eq_sub, vadd_eq_add]; rw [hV2, hu]; module
  have hG2int : G2 ∈ interior D.target.carrier := by
    rw [hG2lm]; exact hint1 (1 / 2) (by norm_num) (by norm_num)
  have hα2 : (D.tile i2).localAngle P2 = α := by simpa [angOf] using t2.right_angle
  have hαa : sideOpp D.model 0 = (ta e f : ℝ) := S.hsa
  have hT'G1 : (D.tile i').localAngle G1 = α := by
    have := (angle_of_opp D α β γ S.hα' S.hβ' S.hγ' hab hbc hac i' kG kP kH hGP hHG.symm hHP.symm).1
      (by rw [hP', hH', hZa1, S.hsa])
    rw [hG'] at this; exact this
  have hT'G2 : (D.tile i').localAngle G2 = β := by
    have := (angle_of_opp D α β γ S.hα' S.hβ' S.hγ' hab hbc hac i' kH kP kG hHP hHG hGP.symm).2.1
      (by rw [hP', hG', hb0, S.hsb])
    rw [hH'] at this; exact this
  have hG1front : G1 ∈ frontier D.target.carrier ∧ G1 ∉ Set.range D.target.pts :=
    side_frontier D.target S.hpr S.hpq S.hqr.symm hG1seg
  have hV2front : V2 ∈ frontier D.target.carrier ∧ V2 ∉ Set.range D.target.pts :=
    side_frontier D.target S.hpr S.hpq S.hqr.symm hV2seg
  have hP2front : P2 ∈ frontier D.target.carrier ∧ P2 ∉ Set.range D.target.pts :=
    side_frontier D.target S.hpq S.hpr S.hqr hP2seg
  have cneg : ∀ a b : Plane, cross a (-b) = - cross a b := by
    intro a b; simp only [cross, PiLp.neg_apply]; ring
  have F3a : ∀ k : Fin 3, k ≠ k + 1 := by decide
  have F3b : ∀ k : Fin 3, k ≠ k + 2 := by decide
  have F3c : ∀ k : Fin 3, k + 1 ≠ k + 2 := by decide
  have hGdist : dist G1 G2 = (tc e f : ℝ) := by
    rw [dist_comm, dist_eq_norm, hG2e, add_sub_cancel_left, hce]
  have hcrU1 : 0 < cross u (G1 - P2) := by
    have e1 : G1 - P2 = v - (2:ℝ) • e0 := by rw [hG1, hP2, hP1]; module
    have e2 : cross (v - e0) (v - (2:ℝ) • e0) = cross e0 v := by
      simp only [cross, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]; ring
    rw [e1, hudef, e2]; exact hcr
  have hcrU2 : 0 < cross u (P1 - P2) := by
    have e1 : P1 - P2 = -e0 := by rw [hP2]; abel
    have e2 : cross (v - e0) (-e0) = cross e0 v := by
      simp only [cross, PiLp.sub_apply, PiLp.neg_apply]; ring
    rw [e1, hudef, e2]; exact hcr
  have ne_ang : ∀ {i j : Fin N} {a b : ℝ}, (D.tile i).localAngle G2 = a → (D.tile j).localAngle G2 = b →
      a ≠ b → i ≠ j := by
    intro i j a b ha hb hab' h; subst h; exact hab' (ha.symm.trans hb)
  have hG1G2 : G2 - G1 = e0 := by rw [hG2e]; abel
  have hVG : V2 - G2 = u := by rw [hV2, hu]; module
  have hdGV : dist G2 V2 = (tb e f : ℝ) := by rw [dist_comm, dist_eq_norm, hVG, hub]
  have hdPG : dist P2 G2 = (tb e f : ℝ) := by rw [dist_comm, dist_eq_norm, ← hu, hub]
  obtain ⟨idx1, hT1e⟩ := edge_idx (D.tile i2) fi1 g1 hgf1
  rw [hf1, hg1] at hT1e
  by_cases hZH : Straddled D.toDissection (-(crossL e0)) (-(cross e0 G1)) G2
  · -- a tile presents `π` at `G₂`, with an edge along the horizontal through `G₂`
    obtain ⟨eS, heS, hS⟩ := hZH
    have hS0 : (D.tile eS.1).localAngle G2 = Real.pi := localAngle_pi_of_openSegment (D.tile eS.1) eS.2 hS
    have hSabove : ∀ j, 0 ≤ cross e0 ((D.tile eS.1).pts j - G1) := by
      intro j
      have := (Dissection.mem_lineChain.mp heS).2.2 j
      simp only [LinearMap.neg_apply, crossL_apply] at this
      have e1 : cross e0 ((D.tile eS.1).pts j - G1) = cross e0 ((D.tile eS.1).pts j) - cross e0 G1 :=
        cross_sub_right _ _ _
      rw [e1]; linarith
    have hu0 : u ≠ 0 := by intro h; rw [h, norm_zero] at hub; linarith
    have hG2u : G2 = P2 + (1 : ℝ) • u := by rw [one_smul, hu]; abel
    have hα0 := S.hα0
    have hβ0 := S.hβ0
    have hγdef := S.hγdef
    have hrel := S.hrel
    by_cases hZL : Straddled D.toDissection (crossL u) (cross u P2) G2
    · exfalso
      obtain ⟨eT, heT, hT⟩ := hZL
      have hT0 := localAngle_pi_of_openSegment (D.tile eT.1) eT.2 hT
      obtain ⟨sX, sY, hXe, hYe, hcs⟩ := straddle_param hu0 (t0 := 1) (c := cross u P2) rfl heT
        (by rw [← hG2u]; exact hT)
      have hbelow : ∃ j, cross e0 ((D.tile eT.1).pts j - G1) < 0 := by
        have key : ∀ s : ℝ, s < 1 → cross e0 (P2 + s • u - G1) < 0 := by
          intro s hs
          have : cross e0 (P2 + s • u - G1) = (s - 1) * cross e0 v := by
            rw [hP2, hP1, hG1, hudef]
            simp only [cross, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]; ring
          rw [this]; nlinarith [mul_pos (sub_pos.mpr hs) hcr]
        rcases hcs with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact ⟨eT.2, by rw [hXe]; exact key sX h1⟩
        · exact ⟨eT.2 + 1, by rw [hYe]; exact key sY h1⟩
      have hTS : eT.1 ≠ eS.1 := by
        intro h
        obtain ⟨j, hj⟩ := hbelow
        have := hSabove j
        rw [← h] at this; linarith
      have hsum := angle_sum_four D.toDissection hG2int (a := eS.1) (b := eT.1) (c := i2) (d := i')
        hTS.symm (ne_ang hS0 hγ1 hγπ.symm) (ne_ang hS0 hT'G2 hβπ.symm) (ne_ang hT0 hγ1 hγπ.symm)
        (ne_ang hT0 hT'G2 hβπ.symm) hi'2.symm
      rw [hS0, hT0, hγ1, hT'G2] at hsum
      linarith
    · have hne' : P2 ≠ G2 := by
        intro h; have : u = 0 := by rw [hu, ← h]; simp
        exact hu0 this
      have hlm2 : ∀ t : ℝ, AffineMap.lineMap P2 G2 t = AffineMap.lineMap P2 V2 (t / 2) := by
        intro t
        rw [AffineMap.lineMap_apply, AffineMap.lineMap_apply]
        simp only [vsub_eq_sub, vadd_eq_add]
        rw [← hu, hV2]; module
      have hint2 : ∀ t : ℝ, 0 < t → t < 1 → AffineMap.lineMap P2 G2 t ∈ interior D.target.carrier := by
        intro t h0 h1; rw [hlm2]; exact hint1 (t / 2) (by linarith) (by linarith)
      have hbef2 : ∀ t : ℝ, t < 0 → AffineMap.lineMap P2 G2 t ∉ D.target.carrier := by
        intro t h0; rw [hlm2]; exact hbef1 (t / 2) (by linarith)
      have hnear2 : ∀ t : ℝ, 0 < t → t < 1 → ∃ (i : Fin N) (k : Fin 3),
          AffineMap.lineMap P2 G2 t ∈ (D.tile i).edge k := by
        intro t h0 h1
        refine ⟨i2, idx1, ?_⟩
        rw [hT1e, segment_eq_image_lineMap]
        exact ⟨t, ⟨h0.le, h1.le⟩, rfl⟩
      have hg0 : (crossL u : Plane →ₗ[ℝ] ℝ) ≠ 0 := by
        intro h
        apply hu0
        apply eq_zero_of_cross_eq_zero
        intro w
        have := congrArg (fun g : Plane →ₗ[ℝ] ℝ => g w) h
        simpa using this
      have hgP : (crossL u : Plane →ₗ[ℝ] ℝ) P2 = cross u P2 := by simp [crossL_apply]
      have hgG : (crossL u : Plane →ₗ[ℝ] ℝ) G2 = cross u P2 := by
        simp only [crossL_apply]
        rw [hG2u, cross_add_right, cross_smul_right, Erdos634.Geometry.cross_self]; ring
      obtain ⟨iW, kW, hW, hWright⟩ := L3_one_g D.toDissection (ta e f) (tb e f) (tc e f) (tb e f)
        (fun x y z h => by
          obtain ⟨hx, hy, hz⟩ := cover_unique e f x y z S.he S.hef S.hcop h
          omega)
        (fun i k => w2_habc S i k) hne' hdPG (crossL u) (cross u P2) hg0 hgP hgG hint2 hbef2 hnear2 hZL
      have hWd : dist ((D.tile iW).pts kW) ((D.tile iW).pts (kW + 1)) = sideOpp D.model 1 := by
        rcases hW with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rw [h1, h2, hdPG, S.hsb]
        · rw [h1, h2, dist_comm, hdPG, S.hsb]
      have hWcases : ((D.tile iW).localAngle P2 = α ∧ (D.tile iW).localAngle G2 = γ) ∨
          ((D.tile iW).localAngle P2 = γ ∧ (D.tile iW).localAngle G2 = α ∧
            ∃ kP kG : Fin 3, kP ≠ kG ∧ (D.tile iW).pts kP = P2 ∧ (D.tile iW).pts kG = G2) := by
        rcases bedge_ends_perm D α β γ S.hα' S.hβ' S.hγ' hab hbc hac iW kW hWd with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
          rcases hW with ⟨e1, e2⟩ | ⟨e1, e2⟩
        · left; rw [e1] at h1; rw [e2] at h2; exact ⟨h1, h2⟩
        · right; rw [e2] at h2; rw [e1] at h1; exact ⟨h2, h1, kW + 1, kW, (F3a kW).symm, e2, e1⟩
        · right; rw [e1] at h1; rw [e2] at h2; exact ⟨h1, h2, kW, kW + 1, F3a kW, e1, e2⟩
        · left; rw [e2] at h2; rw [e1] at h1; exact ⟨h2, h1⟩
      have hi2W : i2 ≠ iW := by
        intro h
        have := hWright kk1
        simp only [crossL_apply] at this
        rw [← h, hk1] at this
        have e1 : cross u P1 - cross u P2 = cross u (P1 - P2) := (cross_sub_right _ _ _).symm
        linarith
      rcases hWcases with ⟨-, hWG⟩ | ⟨hWP, hWG, kP', kG', hkne, hkP', hkG'⟩
      · exfalso
        have hsum := angle_sum_four D.toDissection hG2int (a := eS.1) (b := i2) (c := i') (d := iW)
          (ne_ang hS0 hγ1 hγπ.symm) (ne_ang hS0 hT'G2 hβπ.symm) (ne_ang hS0 hWG hγπ.symm) hi'2.symm hi2W
          (ne_ang hT'G2 hWG hβγ)
        rw [hS0, hγ1, hT'G2, hWG] at hsum
        linarith
      · refine hB iW kP' kG' hkne hkP' hkG' hWP hWG (Ne.symm hi2W) ?_
        intro j
        have := hWright j
        simp only [crossL_apply] at this
        rw [← hu]
        have e1 : cross u ((D.tile iW).pts j - P2) = cross u ((D.tile iW).pts j) - cross u P2 :=
          cross_sub_right _ _ _
        rw [e1]; linarith
  · obtain ⟨iY, kY, hkY, hYabove⟩ := w2_horizontal S he2 hori hG2e hG1 hce hcr ⟨μ, hμ, hAPv⟩ hG1seg hG2int
      i' kG kH hHG hG' hH' hZH
    obtain ⟨k0, k1, k2, h01, h02, h12, hy0, hy1⟩ : ∃ k0 k1 k2 : Fin 3, k0 ≠ k1 ∧ k0 ≠ k2 ∧ k1 ≠ k2 ∧
        (D.tile iY).pts k0 = G1 ∧ (D.tile iY).pts k1 = G2 := by
      rcases hkY with ⟨a, b⟩ | ⟨a, b⟩
      · exact ⟨kY, kY + 1, kY + 2, F3a kY, F3b kY, F3c kY, a, b⟩
      · exact ⟨kY + 1, kY, kY + 2, (F3a kY).symm, F3c kY, F3b kY, b, a⟩
    -- the tile Yh presents beta at G1
    have hiYmem : G1 ∈ (D.tile iY).carrier := by
      rw [← hy0]; exact subset_convexHull ℝ _ (Set.mem_range_self _)
    obtain ⟨iU, hUang, hU0, hU1, h01', hall⟩ :=
      boundary_three_tiles S hG1front.1 hG1front.2 i1 i' hγ0 hT'G1
    have hiY1 : iY ≠ i1 := by
      intro h
      have := hYabove kk0
      rw [h, hk0] at this
      have e1 : LC - G1 = -v := by rw [hG1]; abel
      rw [e1, cneg] at this
      linarith
    have hiY2 : iY ≠ i' := by
      intro h
      have := hYabove kP
      rw [h, hP'] at this
      have e1 : P1 - G1 = e0 - v := by rw [hG1, hP1]; abel
      rw [e1, cross_sub_right, Erdos634.Geometry.cross_self] at this
      linarith
    have hiYU : iY = iU := by
      rcases hall iY hiYmem with h | h | h
      · exact absurd h hiY1
      · exact absurd h hiY2
      · exact h
    have hYb : (D.tile iY).localAngle G1 = β := by rw [hiYU]; exact hUang
    have hYc := cbeta_tile S iY k0 k1 k2 h01 h02 h12 (by rw [hy0]; exact hYb)
      (by rw [hy0, hy1, hGdist, S.hsc])
    obtain ⟨hYd02, hYa1, hYg2, hYd12⟩ := hYc
    rw [hy0] at hYd02
    rw [hy1] at hYa1 hYd12
    -- the third vertex of Yh is V2
    have hJcr : 0 < cross e0 ((D.tile iY).pts k2 - G1) := by
      have h1 := hYabove k2
      have h2 := tile_cross_ne (D.tile iY) k0 k1 k2 h01 h02 h12
      rw [hy0, hy1, hG1G2] at h2
      exact lt_of_le_of_ne h1 (Ne.symm h2)
    have hV2G1 : V2 - G1 = v := by rw [hV2def, hG1]; module
    have hne12 : G1 ≠ G2 := by
      intro h; apply he0; rw [← hG1G2, ← h]; simp
    have hJV2 : (D.tile iY).pts k2 = V2 := by
      refine two_circles hne12 ?_ ?_ ?_
      · rw [hYd02, S.hsa, dist_comm, dist_eq_norm, hV2G1, hva]
      · rw [hYd12, S.hsb, dist_comm G2 V2, dist_eq_norm, hVG, hub]
      · rw [hG1G2, hV2G1]; exact mul_pos hJcr hcr
    have hYg2' : (D.tile iY).localAngle V2 = γ := by rw [← hJV2]; exact hYg2
    have hYa1' : (D.tile iY).localAngle G2 = α := hYa1
    -- the chord P2 V2
    obtain ⟨idx2, hYe⟩ := edge_idx (D.tile iY) k1 k2 h12.symm
    rw [hy1, hJV2] at hYe
    obtain ⟨ia, ka, ib, kb, hneab, hia, hib, hsa, hsb⟩ := w2_chord2b S hf3 hu hV2 hub hP2seg hV2seg i2 idx1 hT1e
      iY idx2 hYe
    -- the tile on [G2,V2]
    have hbd : dist ((D.tile ib).pts kb) ((D.tile ib).pts (kb + 1)) = sideOpp D.model 1 := by
      rcases hib with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1, h2, hdGV, S.hsb]
      · rw [h1, h2, dist_comm, hdGV, S.hsb]
    have hibY : iY ≠ ib := by
      intro h
      have := hsb k0
      rw [← h, hy0] at this
      linarith
    have hibG : (D.tile ib).localAngle G2 = γ := by
      rcases bedge_ends_perm D α β γ S.hα' S.hβ' S.hγ' hab hbc hac ib kb hbd with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
        rcases hib with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · rw [e2] at h2; exact (ndg hV2front.1 hV2front.2 iY ib hibY hYg2' h2).elim
      · rw [e2] at h2; exact h2
      · rw [e1] at h1; exact h1
      · rw [e1] at h1; exact (ndg hV2front.1 hV2front.2 iY ib hibY hYg2' h1).elim
    -- the tile on [P2,G2]
    have hba : dist ((D.tile ia).pts ka) ((D.tile ia).pts (ka + 1)) = sideOpp D.model 1 := by
      rcases hia with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1, h2, hdPG, S.hsb]
      · rw [h1, h2, dist_comm, hdPG, S.hsb]
    have hiaib : ib ≠ ia := by
      intro h
      by_cases hk : ka = kb
      · apply hneab; rw [hk, h]
      · exact tile_edges_ne S ia ka kb hk (hba.trans (by rw [← h]; exact hbd.symm))
    have hi2ib : i2 ≠ ib := by
      intro h
      have := hsb kk1
      rw [← h, hk1] at this
      linarith
    have hi2ia : i2 ≠ ia := by
      intro h
      have := hsa kk1
      rw [← h, hk1] at this
      linarith
    have hiacases : ((D.tile ia).localAngle P2 = α ∧ (D.tile ia).localAngle G2 = γ) ∨
        ((D.tile ia).localAngle P2 = γ ∧ (D.tile ia).localAngle G2 = α ∧
          ∃ kP kG : Fin 3, kP ≠ kG ∧ (D.tile ia).pts kP = P2 ∧ (D.tile ia).pts kG = G2) := by
      rcases bedge_ends_perm D α β γ S.hα' S.hβ' S.hγ' hab hbc hac ia ka hba with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
        rcases hia with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · left; rw [e1] at h1; rw [e2] at h2; exact ⟨h1, h2⟩
      · right; rw [e2] at h2; rw [e1] at h1; exact ⟨h2, h1, ka + 1, ka, (F3a ka).symm, e2, e1⟩
      · right; rw [e1] at h1; rw [e2] at h2; exact ⟨h1, h2, ka, ka + 1, F3a ka, e1, e2⟩
      · left; rw [e2] at h2; rw [e1] at h1; exact ⟨h2, h1⟩
    rcases hiacases with ⟨-, hiaG⟩ | ⟨hiaP, hiaG, kP', kG', hkne, hkP', hkG'⟩
    · exfalso
      have hsum := angle_sum_five D.toDissection hG2int (a := i2) (b := i') (c := iY) (d := ib) (g := ia)
        hi'2.symm (ne_ang hγ1 hYa1' (Ne.symm hαγ)) hi2ib hi2ia (ne_ang hT'G2 hYa1' (Ne.symm hαβ))
        (ne_ang hT'G2 hibG hβγ) (ne_ang hT'G2 hiaG hβγ) (ne_ang hYa1' hibG hαγ) (ne_ang hYa1' hiaG hαγ) hiaib
      rw [hγ1, hT'G2, hYa1', hibG, hiaG] at hsum
      have := S.hγdef; have := S.hrel; have := S.hα0
      linarith
    · refine hB ia kP' kG' hkne hkP' hkG' hiaP hiaG (Ne.symm hi2ia) ?_
      intro j
      rw [← hu]; exact hsa j



/-- **Rule W2 for an oriented target** (`PROOF_W2.md`): the base word cannot begin `cBA, cBA, X` with
`X ∈ {bAG, cAB, bGA}`.  The core `w2_core` produces the tile of type `B` on the far side of `[P₂, G₂]`
(`γ` at `P₂`, `α` at `G₂`); the third token excludes it (`w2_P2_clash`). -/
theorem w2_oriented {D : CongruentDissection N} {e f : ℕ} {α β γ : ℝ} {p q r : Fin 3}
    (S : BandSetup D e f α β γ p q r) (he2 : 2 ≤ e) (hf3 : 3 ≤ f)
    (hori : 0 < cross (D.target.pts q - D.target.pts p) (D.target.pts r - D.target.pts p))
    (hL2 : 2 * (ta e f : ℝ) < dist (D.target.pts p) (D.target.pts r))
    {i1 i2 i3 : Fin N} (hne3 : i3 ≠ i2)
    {P1 P2 P3 G1 G2 Z3 : Plane} {x3 : Side} {l3 r3 : Corner}
    (hlr : (x3 = .b ∧ l3 = .A) ∨ (x3 = .c ∧ l3 = .A) ∨ (x3 = .b ∧ l3 = .G ∧ r3 = .A))
    (t1 : BaseTok D p q (angOf α β γ) (lenOf (ta e f) (tb e f) (tc e f)) .c .B .A i1
      (D.target.pts p) P1 G1)
    (t2 : BaseTok D p q (angOf α β γ) (lenOf (ta e f) (tb e f) (tc e f)) .c .B .A i2 P1 P2 G2)
    (t3 : BaseTok D p q (angOf α β γ) (lenOf (ta e f) (tb e f) (tc e f)) x3 l3 r3 i3 P2 P3 Z3) :
    False := by
  classical
  set LC := D.target.pts p with hLC
  set RC := D.target.pts q with hRC
  set AP := D.target.pts r with hAP
  have hne : LC ≠ RC := by
    intro h
    have : cross (RC - LC) (AP - LC) = 0 := by rw [← h]; simp [cross]
    linarith
  obtain ⟨e0, v, hP1, hP2, hG1, hG2, hce, hva, hub, hcr, ⟨μ, hμ, hAPv⟩, ⟨lam, hlam, hRCe⟩⟩ :=
    w2_vectors S hori t1 t2
  have hP1 : P1 = LC + e0 := hP1
  have hRCe : RC - LC = lam • e0 := hRCe
  have hP2ne : P2 ≠ LC := by
    intro h
    have : e0 + e0 = 0 := by
      have h1 : P2 = LC + (e0 + e0) := by rw [hP2, hP1]; abel
      rw [h1] at h
      simpa using h
    have : cross e0 v = 0 := by
      have : e0 = 0 := by
        have h2 : (2:ℝ) • e0 = 0 := by rw [two_smul]; exact this
        simpa using h2
      rw [this]; simp [cross]
    linarith
  have hP2seg : P2 ∈ openSegment ℝ LC RC := basetok_left_open hne t3 hP2ne
  have hG2P3 : G2 ≠ P3 := by
    intro h
    obtain ⟨s3, -, -, hs3⟩ := seg_param_of_mem t3.right_mem
    have h1 : cross (RC - LC) (G2 - LC) = 0 := by
      rw [h, hs3]
      have : LC + s3 • (RC - LC) - LC = s3 • (RC - LC) := by abel
      rw [this, cross_smul_right, Erdos634.Geometry.cross_self]; ring
    have h2 : G2 - LC = e0 + v := by rw [hG2, hP1]; abel
    rw [h2, hRCe, cross_smul_left, cross_add_right, Erdos634.Geometry.cross_self] at h1
    have : 0 < lam * cross e0 v := mul_pos hlam hcr
    linarith
  have hα2 : (D.tile i2).localAngle P2 = α := by simpa [angOf] using t2.right_angle
  have hdPG : dist P2 G2 = (tb e f : ℝ) := by
    have hu : G2 - P2 = v - e0 := by rw [hG2, hP2]; abel
    rw [dist_comm, dist_eq_norm, hu, hub]
  exact w2_core S he2 hf3 hori hL2 t1 t2 hP2seg
    (fun iW kP kG hkne hkP hkG hWP _ _ _ =>
      w2_P2_clash S hP2seg hα2 hne3 x3 l3 r3 hlr t3 hWP kP kG hkne hkP hkG hdPG hG2P3)

#print axioms w2_oriented

end Erdos634.LaczJunction.Walk
