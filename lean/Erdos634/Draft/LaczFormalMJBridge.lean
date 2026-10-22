import Erdos634.Draft.LaczFormalMJMain
import Erdos634.Draft.LaczFormalW2Mirror

/-!
# From base tokens to the lattice frame: the rule `M(j)` at the level of tokens

Erdős #634, base-`β` band, rule `M(j)`.  Credit: AI assistant (item 3, band program, rule `M(j)`), Beeson–Roșu, Beeson,
Laczkovich, Paliy.  UNAUDITED.  Axiom-clean; no `sorry`.

* `LFrame.canon`: the lattice frame at `A_p` with `e0 = (c/|A_pA_q|)(A_q − A_p)`, `v = (a/|A_pA_r|)(A_r − A_p)`.
* `basetok_vec`: any base token `X → Y` has `Y − X = (|XY|/|A_pA_q|)(A_q − A_p)`.
* `mj_oriented`: in a counterclockwise band target, `j ≥ 1` consecutive `cBA` base tokens followed by a token `bAG`, `cAB`
  or `bGA` are impossible (for `j ≤ e`, legs `> j a`, base `> j c`).  Proof: the first `j` tokens are the up cells
  `(k, 0)` of the frame, the next token is a tile `Y` as in `A(j-1)`, and `MJ_main` at level `0`.
-/

namespace Erdos634.LaczMJ

open Erdos634.Geometry Erdos634.TilePlacement Erdos634.LaczJunction Erdos634.LaczJunction.Walk
  Erdos634.LaczJunction.Grammar Erdos634.Draft.TraceCovering Set

variable {N : ℕ}

/-- Any base token: `Y − X` is the corresponding multiple of the base direction. -/
theorem basetok_vec {D : CongruentDissection N} {p q : Fin 3} (hpq : p ≠ q)
    {ang : Corner → ℝ} {len : Side → ℝ} {x : Side} {l rr : Corner} {i : Fin N} {X Y Z : Plane}
    (h : BaseTok D p q ang len x l rr i X Y Z)
    (hne : D.target.pts p ≠ D.target.pts q) :
    Y - X = (dist X Y / dist (D.target.pts p) (D.target.pts q)) • (D.target.pts q - D.target.pts p) := by
  set LC := D.target.pts p with hLC
  set RC := D.target.pts q with hRC
  have hw : RC - LC ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  obtain ⟨sx, hsx0, hsx1, hX⟩ := seg_param_of_mem h.left_mem
  obtain ⟨sy, hsy0, hsy1, hY⟩ := seg_param_of_mem h.right_mem
  have hwn : 0 < ‖RC - LC‖ := norm_pos_iff.mpr hw
  have hlt : sx < sy := by
    have := h.order
    rw [hX, hY, dist_param_left _ _ hsx0, dist_param_left _ _ hsy0] at this
    by_contra hh; push_neg at hh
    nlinarith
  have hdist : dist X Y = (sy - sx) * ‖RC - LC‖ := by
    have : Y = X + (sy - sx) • (RC - LC) := by rw [hX, hY]; module
    rw [this, dist_comm, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg (by linarith)]
  have hB : dist LC RC = ‖RC - LC‖ := by rw [dist_comm, dist_eq_norm]
  rw [hB, hdist]
  have : Y - X = (sy - sx) • (RC - LC) := by rw [hX, hY]; module
  rw [this]; congr 1; field_simp

/-- The frame at `A_p` determined by the base and left-leg directions. -/
noncomputable def LFrame.canon {D : CongruentDissection N} {e f : ℕ} {α β γ : ℝ} {p q r : Fin 3}
    (S : BandSetup D e f α β γ p q r)
    (hori : 0 < cross (D.target.pts q - D.target.pts p) (D.target.pts r - D.target.pts p))
    (hb : ‖((ta e f : ℝ) / dist (D.target.pts p) (D.target.pts r)) • (D.target.pts r - D.target.pts p) -
      ((tc e f : ℝ) / dist (D.target.pts p) (D.target.pts q)) • (D.target.pts q - D.target.pts p)‖ = (tb e f : ℝ)) :
    LFrame D e f α β γ p q r where
  S := S
  e0 := ((tc e f : ℝ) / dist (D.target.pts p) (D.target.pts q)) • (D.target.pts q - D.target.pts p)
  v := ((ta e f : ℝ) / dist (D.target.pts p) (D.target.pts r)) • (D.target.pts r - D.target.pts p)
  he0 := by
    have hd : dist (D.target.pts p) (D.target.pts q) = ‖D.target.pts q - D.target.pts p‖ := by
      rw [dist_comm, dist_eq_norm]
    have hpos : 0 < dist (D.target.pts p) (D.target.pts q) :=
      dist_pos.mpr (fun h => by
        have : cross (D.target.pts q - D.target.pts p) (D.target.pts r - D.target.pts p) = 0 := by
          rw [← h]; simp [cross]
        linarith)
    have hc : (0 : ℝ) < tc e f := LFrame.tc_pos S
    rw [norm_smul, Real.norm_of_nonneg (div_nonneg hc.le hpos.le), ← hd]
    field_simp
  hv := by
    have hd : dist (D.target.pts p) (D.target.pts r) = ‖D.target.pts r - D.target.pts p‖ := by
      rw [dist_comm, dist_eq_norm]
    have hpos : 0 < dist (D.target.pts p) (D.target.pts r) :=
      dist_pos.mpr (fun h => by
        have : cross (D.target.pts q - D.target.pts p) (D.target.pts r - D.target.pts p) = 0 := by
          rw [← h]; simp [cross]
        linarith)
    have ha : (0 : ℝ) < ta e f := by exact_mod_cast a_pos e f S.he S.hef
    rw [norm_smul, Real.norm_of_nonneg (div_nonneg ha.le hpos.le), ← hd]
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
    have ha : (0 : ℝ) < ta e f := by exact_mod_cast a_pos e f S.he S.hef
    rw [cross_smul_right, cross_smul_left_]
    have := mul_pos (div_pos hc hpq) (mul_pos (div_pos ha hpr) hori)
    nlinarith
  lam := dist (D.target.pts p) (D.target.pts q) / (tc e f : ℝ)
  mu := dist (D.target.pts p) (D.target.pts r) / (ta e f : ℝ)
  hlam := by
    have hpq : 0 < dist (D.target.pts p) (D.target.pts q) :=
      dist_pos.mpr (fun h => by
        have : cross (D.target.pts q - D.target.pts p) (D.target.pts r - D.target.pts p) = 0 := by
          rw [← h]; simp [cross]
        linarith)
    exact div_pos hpq (LFrame.tc_pos S)
  hmu := by
    have hpr : 0 < dist (D.target.pts p) (D.target.pts r) :=
      dist_pos.mpr (fun h => by
        have : cross (D.target.pts q - D.target.pts p) (D.target.pts r - D.target.pts p) = 0 := by
          rw [← h]; simp [cross]
        linarith)
    have ha : (0 : ℝ) < ta e f := by exact_mod_cast a_pos e f S.he S.hef
    exact div_pos hpr ha
  hq := by
    have hpq : 0 < dist (D.target.pts p) (D.target.pts q) :=
      dist_pos.mpr (fun h => by
        have : cross (D.target.pts q - D.target.pts p) (D.target.pts r - D.target.pts p) = 0 := by
          rw [← h]; simp [cross]
        linarith)
    have hc : (0 : ℝ) < tc e f := LFrame.tc_pos S
    have hmul : dist (D.target.pts p) (D.target.pts q) / (tc e f : ℝ) *
        ((tc e f : ℝ) / dist (D.target.pts p) (D.target.pts q)) = 1 := by
      field_simp
    rw [smul_smul, hmul, one_smul]; abel
  hr := by
    have hpr : 0 < dist (D.target.pts p) (D.target.pts r) :=
      dist_pos.mpr (fun h => by
        have : cross (D.target.pts q - D.target.pts p) (D.target.pts r - D.target.pts p) = 0 := by
          rw [← h]; simp [cross]
        linarith)
    have ha : (0 : ℝ) < ta e f := by exact_mod_cast a_pos e f S.he S.hef
    have hmul : dist (D.target.pts p) (D.target.pts r) / (ta e f : ℝ) *
        ((ta e f : ℝ) / dist (D.target.pts p) (D.target.pts r)) = 1 := by
      field_simp
    rw [smul_smul, hmul, one_smul]; abel

/-- **The rule `M(j)` for tokens, counterclockwise target.**  `j ≥ 1` consecutive `cBA` base tokens followed by a token
`bAG`, `cAB` or `bGA` do not occur. -/
theorem mj_oriented {D : CongruentDissection N} {e f : ℕ} {α β γ : ℝ} {p q r : Fin 3}
    (S : BandSetup D e f α β γ p q r)
    (hori : 0 < cross (D.target.pts q - D.target.pts p) (D.target.pts r - D.target.pts p))
    {m : ℕ} (hje : m + 1 ≤ e)
    (hbase : ((m + 1 : ℕ) : ℝ) * tc e f < dist (D.target.pts p) (D.target.pts q))
    (hleg : ((m + 1 : ℕ) : ℝ) * ta e f < dist (D.target.pts p) (D.target.pts r))
    (tile : ℕ → Fin N) (P Z : ℕ → Plane) (hP0 : P 0 = D.target.pts p)
    (htok : ∀ k, k < m + 1 → BaseTok D p q (angOf α β γ) (lenOf (ta e f : ℝ) (tb e f : ℝ) (tc e f : ℝ))
      .c .B .A (tile k) (P k) (P (k + 1)) (Z k))
    {x : Side} {l rr : Corner} {K Zy : Plane}
    (hlr : (x = .b ∧ l = .A) ∨ (x = .c ∧ l = .A) ∨ (x = .b ∧ l = .G ∧ rr = .A))
    (hY : BaseTok D p q (angOf α β γ) (lenOf (ta e f : ℝ) (tb e f : ℝ) (tc e f : ℝ))
      x l rr (tile (m + 1)) (P (m + 1)) K Zy) : False := by
  classical
  obtain ⟨hαβ, hβγ, hαγ, -, -, -⟩ := BandSetup.distinct S
  have hne : D.target.pts p ≠ D.target.pts q := by
    intro h
    have : cross (D.target.pts q - D.target.pts p) (D.target.pts r - D.target.pts p) = 0 := by
      rw [← h]; simp [cross]
    linarith
  obtain ⟨-, -, -, -, -, -, -, -, -, hY0, hZ0, -, hdYZ, -, -⟩ := cBA_data S hori (htok 0 (by omega))
  have hb : ‖((ta e f : ℝ) / dist (D.target.pts p) (D.target.pts r)) • (D.target.pts r - D.target.pts p) -
      ((tc e f : ℝ) / dist (D.target.pts p) (D.target.pts q)) • (D.target.pts q - D.target.pts p)‖ = (tb e f : ℝ) := by
    rw [← hZ0, ← hY0]
    have : (Z 0 - P 0) - (P (0 + 1) - P 0) = Z 0 - P (0 + 1) := by abel
    rw [this, ← dist_eq_norm, dist_comm]; exact hdYZ
  let F := LFrame.canon S hori hb
  have hPk : ∀ k, k ≤ m + 1 → P k = F.pt (k : ℝ) 0 := by
    intro k
    induction k with
    | zero => intro _; rw [hP0, Nat.cast_zero, F.pt_zero]
    | succ k ih =>
      intro hk
      obtain ⟨-, -, -, -, -, -, -, -, -, hY1, -, -, -, -, -⟩ := cBA_data S hori (htok k (by omega))
      have e1 : P (k + 1) = P k + F.e0 := by
        have : P (k + 1) - P k = F.e0 := hY1
        rw [← this]; abel
      rw [e1, ih (by omega)]
      push_cast
      simp only [LFrame.pt]; module
  have hZk : ∀ k, k < m + 1 → Z k = P k + F.v := by
    intro k hk
    obtain ⟨-, -, -, -, -, -, -, -, -, -, hZ1, -, -, -, -⟩ := cBA_data S hori (htok k hk)
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
      rw [hZk x (by omega), hPk x (by omega)]; simp only [LFrame.pt]; simp
    rw [hA, hB, hC] at h1
    exact h1
  have hBnd : F.Bnd (m + 1) := by
    refine ⟨?_, ?_⟩
    · show ((m + 1 : ℕ) : ℝ) < dist (D.target.pts p) (D.target.pts q) / (tc e f : ℝ)
      rw [lt_div_iff₀ (LFrame.tc_pos S)]; exact hbase
    · have ha : (0 : ℝ) < ta e f := by exact_mod_cast a_pos e f S.he S.hef
      show ((m + 1 : ℕ) : ℝ) < dist (D.target.pts p) (D.target.pts r) / (ta e f : ℝ)
      rw [lt_div_iff₀ ha]; exact hleg
  have hAR := ((F.MJ_main hBnd) m).2 0 (by omega) hje (Or.inl rfl) hups
  have hJ : P (m + 1) = F.pt ((m : ℝ) + 1) ((0 : ℕ) : ℝ) := by
    rw [hPk (m + 1) le_rfl]; push_cast; simp
  have hvec := basetok_vec S.hpq hY hne
  have hX0 : P (m + 1) ≠ K := by
    intro h
    have := hY.order
    rw [h] at this
    exact lt_irrefl _ this
  have hdpos : 0 < dist (P (m + 1)) K := dist_pos.mpr hX0
  have hc : (0 : ℝ) < tc e f := LFrame.tc_pos S
  have hbpq : 0 < dist (D.target.pts p) (D.target.pts q) := dist_pos.mpr hne
  refine hAR (tile (m + 1)) K Zy (dist (P (m + 1)) K / (tc e f : ℝ)) ?_ ?_ (div_pos hdpos hc) ?_ ?_ ?_
  · rw [← hJ]; exact hY.verts
  · rw [← hJ]
    have : K - P (m + 1) = (dist (P (m + 1)) K / (tc e f : ℝ)) • F.e0 := by
      rw [hvec]
      show _ = _ • (((tc e f : ℝ) / dist (D.target.pts p) (D.target.pts q)) • (D.target.pts q - D.target.pts p))
      rw [smul_smul]; congr 1; field_simp
    rw [← this]; abel
  · rw [← hJ]
    have hl := hY.length
    rcases hlr with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -, -⟩
    · exact Or.inl (by simpa [lenOf] using hl)
    · exact Or.inr (by simpa [lenOf] using hl)
    · exact Or.inl (by simpa [lenOf] using hl)
  · rw [← hJ]
    have h1 := basetok_hleft S.hpq S.hpr S.hqr hori hY
    show 0 < cross (((tc e f : ℝ) / dist (D.target.pts p) (D.target.pts q)) • (D.target.pts q - D.target.pts p)) _
    rw [cross_smul_left_]
    exact mul_pos (div_pos hc hbpq) h1
  · rw [← hJ]
    have hang := hY.left_angle
    rcases hlr with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl, -⟩
    · simp only [angOf] at hang; rw [hang]; exact hαβ
    · simp only [angOf] at hang; rw [hang]; exact hαβ
    · simp only [angOf] at hang; rw [hang]; exact hβγ.symm

open Erdos634.MirrorGauge in
/-- **The rule `M(j)` for tokens, any orientation** (reflect the whole dissection if the target is clockwise). -/
theorem mj_holds {D : CongruentDissection N} {e f : ℕ} {α β γ : ℝ} {p q r : Fin 3}
    (S : BandSetup D e f α β γ p q r)
    {m : ℕ} (hje : m + 1 ≤ e)
    (hbase : ((m + 1 : ℕ) : ℝ) * tc e f < dist (D.target.pts p) (D.target.pts q))
    (hleg : ((m + 1 : ℕ) : ℝ) * ta e f < dist (D.target.pts p) (D.target.pts r))
    (tile : ℕ → Fin N) (P Z : ℕ → Plane) (hP0 : P 0 = D.target.pts p)
    (htok : ∀ k, k < m + 1 → BaseTok D p q (angOf α β γ) (lenOf (ta e f : ℝ) (tb e f : ℝ) (tc e f : ℝ))
      .c .B .A (tile k) (P k) (P (k + 1)) (Z k))
    {x : Side} {l rr : Corner} {K Zy : Plane}
    (hlr : (x = .b ∧ l = .A) ∨ (x = .c ∧ l = .A) ∨ (x = .b ∧ l = .G ∧ rr = .A))
    (hY : BaseTok D p q (angOf α β γ) (lenOf (ta e f : ℝ) (tb e f : ℝ) (tc e f : ℝ))
      x l rr (tile (m + 1)) (P (m + 1)) K Zy) : False := by
  have hne := tile_cross_ne D.target p q r S.hpq S.hpr S.hqr
  rcases lt_trichotomy (cross (D.target.pts q - D.target.pts p) (D.target.pts r - D.target.pts p)) 0 with
    hneg | hz | hpos
  · refine mj_oriented (bandSetup_mirror S) ?_ hje ?_ ?_ tile (fun k => mirrorPt (P k)) (fun k => mirrorPt (Z k))
      (by show mirrorPt (P 0) = _; rw [hP0, mirror_target_pts]) (fun k hk => basetok_mirror (htok k hk)) hlr
      (basetok_mirror hY)
    · rw [mirror_target_pts, mirror_target_pts, mirror_target_pts, mirrorPt_sub, mirrorPt_sub, cross_mirror]
      linarith
    · rw [mirror_target_pts, mirror_target_pts, mirrorPt_dist]; exact hbase
    · rw [mirror_target_pts, mirror_target_pts, mirrorPt_dist]; exact hleg
  · exact absurd hz hne
  · exact mj_oriented S hpos hje hbase hleg tile P Z hP0 htok hlr hY

end Erdos634.LaczMJ
