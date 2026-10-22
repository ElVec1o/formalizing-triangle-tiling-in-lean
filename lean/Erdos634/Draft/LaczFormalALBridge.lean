import Erdos634.Draft.LaczFormalALMain
import Erdos634.Draft.LaczFormalMJBridge
import Erdos634.Draft.LaczFormalMJWalk

/-!
# From base tokens to the exchanged lattice frame: Lemma A(j) at the level of tokens

Erdős #634, base-`β` row, thick analogue of `M(j)`.  Credit: AI assistant (Lemma A(k) proposal), Beeson–Roșu, Beeson,
Laczkovich, Paliy.  UNAUDITED.  Axiom-clean; no `sorry`.  Port of `LaczFormalMJBridge` (`cBA` tokens) to `aBG` tokens.

* `AF.canon`: the exchanged frame at `A_p`, `e0 = (a/|A_pA_q|)(A_q − A_p)`, `v = (c/|A_pA_r|)(A_r − A_p)`.
* `apex_dir_a`, `aBG_data`: an `aBG` base token has `Y − X = e0` and `Z − X = v` (the apex lies along the left leg).
* `al_oriented`: in a counterclockwise target, `j ≥ 1` consecutive `aBG` base tokens followed by a token with left angle
  `α` or `γ` (`bAG`, `cAB`, `bGA`, `aGB`) are impossible, for `j ≤ f − 1`, base `> j a`, left leg `> j c`.
-/

namespace Erdos634.LaczAL

open Erdos634.Geometry Erdos634.TilePlacement Erdos634.LaczJunction Erdos634.LaczJunction.Walk
  Erdos634.LaczJunction.Grammar Erdos634.Draft.TraceCovering Erdos634.LaczMJ Set Erdos634.Draft.LaczFormal.Graph

variable {N : ℕ}

/-- The exchanged frame at `A_p` determined by the base and left-leg directions. -/
noncomputable def AF.canon {D : CongruentDissection N} {e f : ℕ} {α β γ : ℝ} {p q r : Fin 3}
    (S : BandSetup D e f α β γ p q r)
    (hori : 0 < cross (D.target.pts q - D.target.pts p) (D.target.pts r - D.target.pts p))
    (hb : ‖((tc e f : ℝ) / dist (D.target.pts p) (D.target.pts r)) • (D.target.pts r - D.target.pts p) -
      ((ta e f : ℝ) / dist (D.target.pts p) (D.target.pts q)) • (D.target.pts q - D.target.pts p)‖ = (tb e f : ℝ)) :
    AF D e f α β γ p q r where
  S := S
  e0 := ((ta e f : ℝ) / dist (D.target.pts p) (D.target.pts q)) • (D.target.pts q - D.target.pts p)
  v := ((tc e f : ℝ) / dist (D.target.pts p) (D.target.pts r)) • (D.target.pts r - D.target.pts p)
  he0 := by
    have hd : dist (D.target.pts p) (D.target.pts q) = ‖D.target.pts q - D.target.pts p‖ := by
      rw [dist_comm, dist_eq_norm]
    have hpos : 0 < dist (D.target.pts p) (D.target.pts q) :=
      dist_pos.mpr (fun h => by
        have : cross (D.target.pts q - D.target.pts p) (D.target.pts r - D.target.pts p) = 0 := by
          rw [← h]; simp [cross]
        linarith)
    have ha : (0 : ℝ) < ta e f := AF.ta_pos S
    rw [norm_smul, Real.norm_of_nonneg (div_nonneg ha.le hpos.le), ← hd]
    field_simp
  hv := by
    have hd : dist (D.target.pts p) (D.target.pts r) = ‖D.target.pts r - D.target.pts p‖ := by
      rw [dist_comm, dist_eq_norm]
    have hpos : 0 < dist (D.target.pts p) (D.target.pts r) :=
      dist_pos.mpr (fun h => by
        have : cross (D.target.pts q - D.target.pts p) (D.target.pts r - D.target.pts p) = 0 := by
          rw [← h]; simp [cross]
        linarith)
    have hc : (0 : ℝ) < tc e f := LFrame.tc_pos S
    rw [norm_smul, Real.norm_of_nonneg (div_nonneg hc.le hpos.le), ← hd]
    field_simp
  hu := by rw [← hb, norm_sub_rev]
  hcr := by
    have hpq : 0 < dist (D.target.pts p) (D.target.pts q) :=
      dist_pos.mpr (fun h => by
        have : cross (D.target.pts q - D.target.pts p) (D.target.pts r - D.target.pts p) = 0 := by
          rw [← h]; simp [cross]
        linarith)
    have hpr : 0 < dist (D.target.pts p) (D.target.pts r) :=
      dist_pos.mpr (fun h => by
        have : cross (D.target.pts q - D.target.pts p) (D.target.pts r - D.target.pts p) = 0 := by
          rw [← h]; simp [cross]
        linarith)
    have hc : (0 : ℝ) < tc e f := LFrame.tc_pos S
    have ha : (0 : ℝ) < ta e f := AF.ta_pos S
    rw [cross_smul_right, cross_smul_left_]
    have := mul_pos (div_pos ha hpq) (mul_pos (div_pos hc hpr) hori)
    nlinarith
  lam := dist (D.target.pts p) (D.target.pts q) / (ta e f : ℝ)
  mu := dist (D.target.pts p) (D.target.pts r) / (tc e f : ℝ)
  hlam := by
    have hpq : 0 < dist (D.target.pts p) (D.target.pts q) :=
      dist_pos.mpr (fun h => by
        have : cross (D.target.pts q - D.target.pts p) (D.target.pts r - D.target.pts p) = 0 := by
          rw [← h]; simp [cross]
        linarith)
    exact div_pos hpq (AF.ta_pos S)
  hmu := by
    have hpr : 0 < dist (D.target.pts p) (D.target.pts r) :=
      dist_pos.mpr (fun h => by
        have : cross (D.target.pts q - D.target.pts p) (D.target.pts r - D.target.pts p) = 0 := by
          rw [← h]; simp [cross]
        linarith)
    exact div_pos hpr (LFrame.tc_pos S)
  hq := by
    have hpq : 0 < dist (D.target.pts p) (D.target.pts q) :=
      dist_pos.mpr (fun h => by
        have : cross (D.target.pts q - D.target.pts p) (D.target.pts r - D.target.pts p) = 0 := by
          rw [← h]; simp [cross]
        linarith)
    have ha : (0 : ℝ) < ta e f := AF.ta_pos S
    have hmul : dist (D.target.pts p) (D.target.pts q) / (ta e f : ℝ) *
        ((ta e f : ℝ) / dist (D.target.pts p) (D.target.pts q)) = 1 := by
      field_simp
    rw [smul_smul, hmul, one_smul]; abel
  hr := by
    have hpr : 0 < dist (D.target.pts p) (D.target.pts r) :=
      dist_pos.mpr (fun h => by
        have : cross (D.target.pts q - D.target.pts p) (D.target.pts r - D.target.pts p) = 0 := by
          rw [← h]; simp [cross]
        linarith)
    have hc : (0 : ℝ) < tc e f := LFrame.tc_pos S
    have hmul : dist (D.target.pts p) (D.target.pts r) / (tc e f : ℝ) *
        ((tc e f : ℝ) / dist (D.target.pts p) (D.target.pts r)) = 1 := by
      field_simp
    rw [smul_smul, hmul, one_smul]; abel

/-- **I0 for `aBG`.**  The apex of a base tile with `β` at its left vertex and an `a`-edge on the base lies at
`X + (c/L)(R − P)`: the direction of the left leg. -/
theorem apex_dir_a {D : CongruentDissection N} {e f : ℕ} {α β γ : ℝ} {p q r : Fin 3}
    (S : BandSetup D e f α β γ p q r)
    (hori : 0 < crs (toV2 (D.target.pts q - D.target.pts p)) (toV2 (D.target.pts r - D.target.pts p)))
    {i : Fin N} {X Y Z : Plane}
    (hpar : ∃ s t : ℝ, 0 ≤ s ∧ s < t ∧ t ≤ 1 ∧ X = D.target.pts p + s • (D.target.pts q - D.target.pts p) ∧
        Y = D.target.pts p + t • (D.target.pts q - D.target.pts p))
    (kk fi g : Fin 3) (hfk : fi ≠ kk) (hgk : g ≠ kk) (hgf : g ≠ fi)
    (hk : (D.tile i).pts kk = X) (hf : (D.tile i).pts fi = Y) (hg : (D.tile i).pts g = Z)
    (hleft : 0 < crs (toV2 (D.target.pts q - D.target.pts p)) (toV2 (Z - X)))
    (hang : (D.tile i).localAngle ((D.tile i).pts kk) = β)
    (hZc : dist X Z = (tc e f : ℝ)) :
    Z - X = ((tc e f : ℝ) / dist (D.target.pts p) (D.target.pts r)) • (D.target.pts r - D.target.pts p) := by
  obtain ⟨hαβ, hβγ, hαγ, hab, hbc, hac⟩ := BandSetup.distinct S
  set P := D.target.pts p with hP
  set Q := D.target.pts q with hQ
  set R := D.target.pts r with hR
  have hβang : cornerAngle ((D.tile i).pts fi) ((D.tile i).pts kk) ((D.tile i).pts g) = β := by
    rw [← localAngle_as_angle _ kk fi g hfk hgk hgf]; exact hang
  rw [hf, hk, hg] at hβang
  obtain ⟨s, t, h0, hst, ht1, hs, ht⟩ := hpar
  have hne : P ≠ Q := by
    intro h
    have : crs (toV2 (Q - P)) (toV2 (R - P)) = 0 := by rw [← h]; simp [crs, toV2]
    linarith
  have hw : Q - P ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  have hv : Y - X = (t - s) • (Q - P) := by rw [ht, hs, sub_smul]; abel
  have hcpos : (0 : ℝ) < tc e f := LFrame.tc_pos S
  have hZ0 : 0 < dist X Z := by rw [hZc]; exact hcpos
  have hPZ : Z - X ≠ 0 := by
    intro h; rw [sub_eq_zero] at h; rw [h, dist_self] at hZ0; exact lt_irrefl _ hZ0
  have hL : ta e f < dist P R := by exact_mod_cast S.haL
  have hapos : (0 : ℝ) < ta e f := AF.ta_pos S
  have hPR : R - P ≠ 0 := by
    intro h; rw [sub_eq_zero] at h; rw [h, dist_self] at hL
    linarith
  have hang1 : InnerProductGeometry.angle (Q - P) (Z - X) = β := by
    unfold cornerAngle at hβang
    rw [EuclideanGeometry.angle, vsub_eq_sub, vsub_eq_sub, hv,
      InnerProductGeometry.angle_smul_left_of_pos _ _ (by linarith)] at hβang
    exact hβang
  have hang2 : InnerProductGeometry.angle (Q - P) (R - P) = β := by
    have := S.cornerP
    unfold cornerAngle at this
    rw [EuclideanGeometry.angle, vsub_eq_sub, vsub_eq_sub] at this
    exact this
  have hc1 : 0 < cross (Q - P) (Z - X) := by rwa [← crs_toV2]
  have hc2 : 0 < cross (Q - P) (R - P) := by rwa [← crs_toV2]
  have hdir := dir_eq_of_angle hw hPZ hPR hc1 hc2 (hang1.trans hang2.symm)
  have hnZ : ‖Z - X‖ = tc e f := by
    rw [← dist_eq_norm, dist_comm, hZc]
  have hnR : ‖R - P‖ = dist P R := by rw [← dist_eq_norm, dist_comm]
  rw [hnZ, hnR] at hdir
  have hLpos : 0 < dist P R := lt_trans hapos hL
  have h2 : (dist P R)⁻¹ • ((dist P R) • (Z - X)) = (dist P R)⁻¹ • ((tc e f : ℝ) • (R - P)) := by
    rw [hdir]
  rw [smul_smul, inv_mul_cancel₀ hLpos.ne', one_smul, smul_smul] at h2
  rw [h2]; congr 1; ring

/-- **Coordinates of an `aBG` token.** -/
theorem aBG_data {D : CongruentDissection N} {e f : ℕ} {α β γ : ℝ} {p q r : Fin 3}
    (S : BandSetup D e f α β γ p q r)
    (hori : 0 < cross (D.target.pts q - D.target.pts p) (D.target.pts r - D.target.pts p))
    {i : Fin N} {X Y Z : Plane}
    (h : BaseTok D p q (angOf α β γ) (lenOf (ta e f) (tb e f) (tc e f)) .a .B .G i X Y Z) :
    Y - X = ((ta e f : ℝ) / dist (D.target.pts p) (D.target.pts q)) • (D.target.pts q - D.target.pts p) ∧
      Z - X = ((tc e f : ℝ) / dist (D.target.pts p) (D.target.pts r)) • (D.target.pts r - D.target.pts p) ∧
      dist Y Z = (tb e f : ℝ) ∧ 0 < cross (D.target.pts q - D.target.pts p) (Z - X) := by
  obtain ⟨hαβ, hβγ, hαγ, hab, hbc, hac⟩ := BandSetup.distinct S
  obtain ⟨hab', hbc', hac'⟩ := BandSetup.dist3 S
  set LC := D.target.pts p with hLC
  set RC := D.target.pts q with hRC
  have hleft := basetok_hleft S.hpq S.hpr S.hqr hori h
  have hori' : 0 < crs (toV2 (RC - LC)) (toV2 (D.target.pts r - LC)) := by rw [crs_toV2]; exact hori
  have hne : LC ≠ RC := by
    intro h0
    have : cross (RC - LC) (D.target.pts r - LC) = 0 := by rw [← h0]; simp [cross]
    linarith
  have hXY : dist X Y = (ta e f : ℝ) := by simpa [lenOf] using h.length
  have hangX : (D.tile i).localAngle X = β := by simpa [angOf] using h.left_angle
  have hlab := tv_lab S h.verts
  have key : dist X Z = (tc e f : ℝ) ∧ dist Y Z = (tb e f : ℝ) := by
    rcases hlab with ⟨h1, h2, h3, h4, h5, h6⟩ | ⟨h1, h2, h3, h4, h5, h6⟩ |
        ⟨h1, h2, h3, h4, h5, h6⟩ | ⟨h1, h2, h3, h4, h5, h6⟩ | ⟨h1, h2, h3, h4, h5, h6⟩ |
        ⟨h1, h2, h3, h4, h5, h6⟩
    · exact absurd (h1.symm.trans hangX) hαβ
    · exact absurd (h1.symm.trans hangX) hαβ
    · exact absurd (hXY.symm.trans h6) hac'
    · exact ⟨h5, h4⟩
    · exact absurd (h1.symm.trans hangX) hβγ.symm
    · exact absurd (h1.symm.trans hangX) hβγ.symm
  obtain ⟨kk, fi, g, hfk, hgk, hgf, hk, hf, hg⟩ : ∃ kk fi g : Fin 3, fi ≠ kk ∧ g ≠ kk ∧ g ≠ fi ∧
      (D.tile i).pts kk = X ∧ (D.tile i).pts fi = Y ∧ (D.tile i).pts g = Z := by
    obtain ⟨j, hj | hj⟩ := h.verts
    · obtain ⟨n1, n2, n3⟩ := fin3_aux' j
      exact ⟨j, j + 1, j + 2, n1, n2, n3, hj.1, hj.2.1, hj.2.2⟩
    · obtain ⟨n1, n2, n3⟩ := fin3_aux' j
      exact ⟨j, j + 2, j + 1, n2, n1, n3.symm, hj.1, hj.2.2, hj.2.1⟩
  have hw : RC - LC ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  obtain ⟨sx, hsx0, hsx1, hX⟩ := seg_param_of_mem h.left_mem
  obtain ⟨sy, hsy0, hsy1, hY⟩ := seg_param_of_mem h.right_mem
  have hlt : sx < sy := by
    have := h.order
    rw [hX, hY, dist_param_left _ _ hsx0, dist_param_left _ _ hsy0] at this
    have hwn : 0 < ‖RC - LC‖ := norm_pos_iff.mpr hw
    by_contra hh; push_neg at hh
    nlinarith
  have hleft' : 0 < crs (toV2 (RC - LC)) (toV2 (Z - X)) := by rw [crs_toV2]; exact hleft
  have hvec := apex_dir_a S hori' (i := i) (X := X) (Y := Y) (Z := Z) ⟨sx, sy, hsx0, hlt, hsy1, hX, hY⟩
    kk fi g hfk hgk hgf hk hf hg hleft' (by rw [hk]; exact hangX) key.1
  refine ⟨?_, hvec, key.2, hleft⟩
  have hdist : dist X Y = (sy - sx) * ‖RC - LC‖ := by
    have : Y = X + (sy - sx) • (RC - LC) := by rw [hX, hY]; module
    rw [this, dist_comm, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg (by linarith)]
  have hB : dist LC RC = ‖RC - LC‖ := by rw [dist_comm, dist_eq_norm]
  rw [hB]
  have hwn : 0 < ‖RC - LC‖ := norm_pos_iff.mpr hw
  have hcs : (ta e f : ℝ) = (sy - sx) * ‖RC - LC‖ := by rw [← hXY, hdist]
  have : Y - X = (sy - sx) • (RC - LC) := by rw [hX, hY]; module
  rw [this]; congr 1; field_simp; linarith

/-- **Lemma A(j) for tokens, counterclockwise target.**  `j ≥ 1` consecutive `aBG` base tokens followed by a token with
left angle `α` or `γ` (`bAG`, `cAB`, `bGA`, `aGB`) do not occur (`j ≤ f − 1`, base `> j a`, left leg `> j c`). -/
theorem al_oriented {D : CongruentDissection N} {e f : ℕ} {α β γ : ℝ} {p q r : Fin 3}
    (S : BandSetup D e f α β γ p q r)
    (hori : 0 < cross (D.target.pts q - D.target.pts p) (D.target.pts r - D.target.pts p))
    {m : ℕ} (hjf : m + 1 ≤ f - 1)
    (hbase : ((m + 1 : ℕ) : ℝ) * ta e f < dist (D.target.pts p) (D.target.pts q))
    (hleg : ((m + 1 : ℕ) : ℝ) * tc e f < dist (D.target.pts p) (D.target.pts r))
    (tile : ℕ → Fin N) (P Z : ℕ → Plane) (hP0 : P 0 = D.target.pts p)
    (htok : ∀ k, k < m + 1 → BaseTok D p q (angOf α β γ) (lenOf (ta e f : ℝ) (tb e f : ℝ) (tc e f : ℝ))
      .a .B .G (tile k) (P k) (P (k + 1)) (Z k))
    {x : Side} {l rr : Corner} {K Zy : Plane}
    (hlr : (x = .b ∧ l = .A) ∨ (x = .c ∧ l = .A) ∨ (x = .b ∧ l = .G) ∨ (x = .a ∧ l = .G))
    (hY : BaseTok D p q (angOf α β γ) (lenOf (ta e f : ℝ) (tb e f : ℝ) (tc e f : ℝ))
      x l rr (tile (m + 1)) (P (m + 1)) K Zy) : False := by
  classical
  obtain ⟨hαβ, hβγ, hαγ, -, -, -⟩ := BandSetup.distinct S
  have hne : D.target.pts p ≠ D.target.pts q := by
    intro h
    have : cross (D.target.pts q - D.target.pts p) (D.target.pts r - D.target.pts p) = 0 := by
      rw [← h]; simp [cross]
    linarith
  obtain ⟨hY0, hZ0, hdYZ, -⟩ := aBG_data S hori (htok 0 (by omega))
  have hb : ‖((tc e f : ℝ) / dist (D.target.pts p) (D.target.pts r)) • (D.target.pts r - D.target.pts p) -
      ((ta e f : ℝ) / dist (D.target.pts p) (D.target.pts q)) • (D.target.pts q - D.target.pts p)‖ = (tb e f : ℝ) := by
    rw [← hZ0, ← hY0]
    have : (Z 0 - P 0) - (P (0 + 1) - P 0) = Z 0 - P (0 + 1) := by abel
    rw [this, ← dist_eq_norm, dist_comm]; exact hdYZ
  let F := AF.canon S hori hb
  have hPk : ∀ k, k ≤ m + 1 → P k = F.pt (k : ℝ) 0 := by
    intro k
    induction k with
    | zero => intro _; rw [hP0, Nat.cast_zero, F.pt_zero]
    | succ k ih =>
      intro hk
      obtain ⟨hY1, -, -, -⟩ := aBG_data S hori (htok k (by omega))
      have e1 : P (k + 1) = P k + F.e0 := by
        have : P (k + 1) - P k = F.e0 := hY1
        rw [← this]; abel
      rw [e1, ih (by omega)]
      push_cast
      simp only [AF.pt]; module
  have hZk : ∀ k, k < m + 1 → Z k = P k + F.v := by
    intro k hk
    obtain ⟨-, hZ1, -, -⟩ := aBG_data S hori (htok k hk)
    have : Z k - P k = F.v := hZ1
    rw [← this]; abel
  have hups : ∀ x : ℕ, x ≤ m → F.UpCell (x : ℝ) ((0 : ℕ) : ℝ) := by
    intro x hx
    refine ⟨tile x, ?_⟩
    have h1 := (htok x (by omega)).verts
    have hA : P x = F.pt (x : ℝ) ((0 : ℕ) : ℝ) := by rw [hPk x (by omega)]; simp
    have hB : P (x + 1) = F.pt ((x : ℝ) + 1) ((0 : ℕ) : ℝ) := by
      rw [hPk (x + 1) (by omega)]; push_cast; simp
    have hC : Z x = F.pt (x : ℝ) (((0 : ℕ) : ℝ) + 1) := by
      rw [hZk x (by omega), hPk x (by omega)]; simp only [AF.pt]; simp
    rw [hA, hB, hC] at h1
    exact h1
  have ha : (0 : ℝ) < ta e f := AF.ta_pos S
  have hc : (0 : ℝ) < tc e f := LFrame.tc_pos S
  have hBnd : F.Bnd (m + 1) := by
    refine ⟨?_, ?_⟩
    · show ((m + 1 : ℕ) : ℝ) < dist (D.target.pts p) (D.target.pts q) / (ta e f : ℝ)
      rw [lt_div_iff₀ ha]; exact hbase
    · show ((m + 1 : ℕ) : ℝ) < dist (D.target.pts p) (D.target.pts r) / (tc e f : ℝ)
      rw [lt_div_iff₀ hc]; exact hleg
  have hAR := ((F.AL_main hBnd) m).2 0 (by omega) hjf (Or.inl rfl) hups
  have hJ : P (m + 1) = F.pt ((m : ℝ) + 1) ((0 : ℕ) : ℝ) := by
    rw [hPk (m + 1) le_rfl]; push_cast; simp
  have hvec := basetok_vec S.hpq hY hne
  have hX0 : P (m + 1) ≠ K := by
    intro h
    have := hY.order
    rw [h] at this
    exact lt_irrefl _ this
  have hdpos : 0 < dist (P (m + 1)) K := dist_pos.mpr hX0
  have hbpq : 0 < dist (D.target.pts p) (D.target.pts q) := dist_pos.mpr hne
  refine hAR (tile (m + 1)) K Zy (dist (P (m + 1)) K / (ta e f : ℝ)) ?_ ?_ (div_pos hdpos ha) ?_ ?_ ?_
  · rw [← hJ]; exact hY.verts
  · rw [← hJ]
    have : K - P (m + 1) = (dist (P (m + 1)) K / (ta e f : ℝ)) • F.e0 := by
      rw [hvec]
      show _ = _ • (((ta e f : ℝ) / dist (D.target.pts p) (D.target.pts q)) • (D.target.pts q - D.target.pts p))
      rw [smul_smul]; congr 1; field_simp
    rw [← this]; abel
  · rw [← hJ]
    have hl := hY.length
    rcases hlr with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩
    · exact Or.inr (Or.inl (by simpa [lenOf] using hl))
    · exact Or.inr (Or.inr (by simpa [lenOf] using hl))
    · exact Or.inr (Or.inl (by simpa [lenOf] using hl))
    · exact Or.inl (by simpa [lenOf] using hl)
  · rw [← hJ]
    have h1 := basetok_hleft S.hpq S.hpr S.hqr hori hY
    show 0 < cross (((ta e f : ℝ) / dist (D.target.pts p) (D.target.pts q)) • (D.target.pts q - D.target.pts p)) _
    rw [cross_smul_left_]
    exact mul_pos (div_pos ha hbpq) h1
  · rw [← hJ]
    have hang := hY.left_angle
    rcases hlr with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩
    · simp only [angOf] at hang; rw [hang]; exact hαβ
    · simp only [angOf] at hang; rw [hang]; exact hαβ
    · simp only [angOf] at hang; rw [hang]; exact hβγ.symm
    · simp only [angOf] at hang; rw [hang]; exact hβγ.symm

end Erdos634.LaczAL
