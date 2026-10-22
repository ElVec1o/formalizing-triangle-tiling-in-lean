import Erdos634.Draft.LaczFormalWalkCount

/-!
# The corner tiles of the base walk

Erdős #634, base-`β` band.  Credit: AI assistant (item 3, band program), Beeson–Roșu (Lemma 23: the corner tile has
angle `β`), Beeson, Laczkovich, Paliy.  UNAUDITED.  Axiom-clean; no `sorry`.

* `dir_eq_of_angle`: two vectors on the same side of `u` forming the same angle with `u` are positive multiples
  of each other.
* `corner_tile_beta`: the tile of the walk entry that starts at a target corner of angle `β` presents `β` there
  (`congruentDissection_base_corner_tile_vertex`: the corner tile is unique).
* `corner_apex`: the apex of the first walk tile, when its base edge is `c`, lies on the left leg.
-/

namespace Erdos634.LaczJunction.Walk

open Erdos634.Geometry Erdos634.TilePlacement Erdos634.LaczJunction Erdos634.LaczJunction.Grammar
open Erdos634.Draft.LaczFormal.Graph

variable {N : ℕ}

theorem dir_eq_of_angle {u v w : Plane} (hu : u ≠ 0) (hv : v ≠ 0) (hw : w ≠ 0)
    (hcv : 0 < cross u v) (hcw : 0 < cross u w)
    (h : InnerProductGeometry.angle u v = InnerProductGeometry.angle u w) :
    ‖w‖ • v = ‖v‖ • w := by
  have hcos := congrArg Real.cos h
  rw [InnerProductGeometry.cos_angle, InnerProductGeometry.cos_angle] at hcos
  have nu := norm_pos_iff.mpr hu
  have nv := norm_pos_iff.mpr hv
  have nw := norm_pos_iff.mpr hw
  have hu2 := Erdos634.Geometry.norm_sq_coords u
  have hv2 := Erdos634.Geometry.norm_sq_coords v
  have hw2 := Erdos634.Geometry.norm_sq_coords w
  have hiv := Erdos634.Geometry.inner_coords u v
  have hiw := Erdos634.Geometry.inner_coords u w
  have hcv' : cross u v = u 0 * v 1 - u 1 * v 0 := rfl
  have hcw' : cross u w = u 0 * w 1 - u 1 * w 0 := rfl
  rw [hiv, hiw] at hcos
  rw [hcv'] at hcv
  rw [hcw'] at hcw
  set a := u 0; set b := u 1; set c := v 0; set d := v 1; set g := w 0; set k := w 1
  set Nu := ‖u‖; set Nv := ‖v‖; set Nw := ‖w‖
  have E1 : Nw * (a * c + b * d) = Nv * (a * g + b * k) := by
    rw [div_eq_div_iff (by positivity) (by positivity)] at hcos
    have : Nu * (Nw * (a * c + b * d) - Nv * (a * g + b * k)) = 0 := by linear_combination hcos
    rcases mul_eq_zero.mp this with h' | h'
    · exact absurd h' nu.ne'
    · linarith
  have L1 : (a * c + b * d) ^ 2 + (a * d - b * c) ^ 2 = Nu ^ 2 * Nv ^ 2 := by
    rw [hu2, hv2]; ring
  have L2 : (a * g + b * k) ^ 2 + (a * k - b * g) ^ 2 = Nu ^ 2 * Nw ^ 2 := by
    rw [hu2, hw2]; ring
  have E2sq : (Nw * (a * d - b * c)) ^ 2 = (Nv * (a * k - b * g)) ^ 2 := by
    have h1 : (Nw * (a * c + b * d)) ^ 2 = (Nv * (a * g + b * k)) ^ 2 := by rw [E1]
    linear_combination Nw ^ 2 * L1 - Nv ^ 2 * L2 - h1
  have E2 : Nw * (a * d - b * c) = Nv * (a * k - b * g) := by
    have p1 : 0 < Nw * (a * d - b * c) := mul_pos nw hcv
    have p2 : 0 < Nv * (a * k - b * g) := mul_pos nv hcw
    exact (pow_left_inj₀ p1.le p2.le two_ne_zero).mp E2sq
  have nu2 : 0 < a ^ 2 + b ^ 2 := by rw [← hu2]; positivity
  have x0 : Nw * c - Nv * g = 0 := by
    have : (a ^ 2 + b ^ 2) * (Nw * c - Nv * g) = 0 := by
      linear_combination a * E1 - b * E2
    rcases mul_eq_zero.mp this with h' | h'
    · exact absurd h' nu2.ne'
    · exact h'
  have x1 : Nw * d - Nv * k = 0 := by
    have : (a ^ 2 + b ^ 2) * (Nw * d - Nv * k) = 0 := by
      linear_combination b * E1 + a * E2
    rcases mul_eq_zero.mp this with h' | h'
    · exact absurd h' nu2.ne'
    · exact h'
  ext i; fin_cases i
  · simp; linarith
  · simp; linarith


theorem corner_cyc (T : Tri) (p q r : Fin 3) (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    {β : ℝ} (h : cornerAngle (T.pts q) (T.pts p) (T.pts r) = β) :
    cornerAngle (T.pts (p + 1)) (T.pts p) (T.pts (p + 2)) = β := by
  rcases fin3_pair p q r hpq.symm hpr.symm hqr.symm with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · subst h1; subst h2; exact h
  · subst h1; subst h2
    unfold cornerAngle at h ⊢
    rw [EuclideanGeometry.angle_comm]; exact h

/-- **The corner tile has angle `β`.** -/
theorem corner_tile_beta {D : CongruentDissection N} {e f : ℕ} {α β γ : ℝ} {p q r : Fin 3}
    (S : BandSetup D e f α β γ p q r) (k : Fin 3)
    (hk : cornerAngle (D.target.pts (k + 1)) (D.target.pts k) (D.target.pts (k + 2)) = β)
    (i : Fin N) (j : Fin 3) (hj : (D.tile i).pts j = D.target.pts k) :
    (D.tile i).localAngle (D.target.pts k) = β := by
  obtain ⟨hαβ, hβγ, hαγ, -, -, -⟩ := BandSetup.distinct S
  have hπ := Real.pi_pos
  have hα0 := S.hα0
  have hβ0 := S.hβ0
  have hr := S.hrel
  have hγd := S.hγdef
  obtain ⟨i0, j0, -, hang, huniq⟩ := Erdos634.Geometry.Dissection.congruentDissection_base_corner_tile_vertex
    D α β γ hαβ hαγ (by intro h; linarith) hα0.ne' hβγ (by intro h; linarith) hβ0.ne'
    (by intro h; linarith) (by intro h; linarith) (by intro h; linarith)
    hπ.ne' hγd hr S.hirr S.hα' S.hβ' S.hγ' k hk
  have hmem : D.target.pts k ∈ (D.tile i).carrier := by
    rw [← hj]; exact subset_convexHull ℝ _ ⟨j, rfl⟩
  rw [huniq i hmem]; exact hang


theorem angOf_inj_B {α β γ : ℝ} (hαβ : α ≠ β) (hβγ : β ≠ γ) {c : Corner}
    (h : angOf α β γ c = β) : c = .B := by
  cases c
  · exact absurd h hαβ
  · rfl
  · exact absurd h hβγ.symm

/-- The data of a base-walk entry used below (as produced by `base_walk`). -/
def StepData (D : CongruentDissection N) (e f : ℕ) (α β γ : ℝ) (p q : Fin 3)
    (x : Fin N × Plane × Plane) : Prop :=
  ∃ kk fi g : Fin 3, fi ≠ kk ∧ g ≠ kk ∧ g ≠ fi ∧ (D.tile x.1).pts kk = x.2.1 ∧
    (D.tile x.1).pts fi = x.2.2 ∧
    0 < crs (toV2 (D.target.pts q - D.target.pts p)) (toV2 ((D.tile x.1).pts g - x.2.1)) ∧
    BaseTok D p q (angOf α β γ) (lenOf (ta e f) (tb e f) (tc e f))
      (elemTok D α β x).side (elemTok D α β x).left (elemTok D α β x).right x.1 x.2.1 x.2.2
      ((D.tile x.1).pts g)

/-- **`okFirst`**: the first walk entry starts at the corner `A_p` and presents `β` there, so its token has left
angle `B`. -/
theorem first_left_B {D : CongruentDissection N} {e f : ℕ} {α β γ : ℝ} {p q r : Fin 3}
    (S : BandSetup D e f α β γ p q r) {x : Fin N × Plane × Plane} (hx0 : x.2.1 = D.target.pts p)
    (hsd : StepData D e f α β γ p q x) : (elemTok D α β x).left = .B := by
  obtain ⟨hαβ, hβγ, -⟩ := BandSetup.distinct S
  obtain ⟨kk, fi, g, -, -, -, hk, -, -, hbt⟩ := hsd
  have hang := corner_tile_beta S p (corner_cyc D.target p q r S.hpq S.hpr S.hqr S.cornerP) x.1 kk
    (hk.trans hx0)
  have := hbt.left_angle
  rw [hx0, hang] at this
  exact angOf_inj_B hαβ hβγ this.symm

/-- **`okLast`**: the last walk entry ends at the corner `A_q`, so its token has right angle `B`. -/
theorem last_right_B {D : CongruentDissection N} {e f : ℕ} {α β γ : ℝ} {p q r : Fin 3}
    (S : BandSetup D e f α β γ p q r) {x : Fin N × Plane × Plane} (hx1 : x.2.2 = D.target.pts q)
    (hsd : StepData D e f α β γ p q x) : (elemTok D α β x).right = .B := by
  obtain ⟨hαβ, hβγ, -⟩ := BandSetup.distinct S
  obtain ⟨kk, fi, g, -, -, -, -, hf, -, hbt⟩ := hsd
  have hang := corner_tile_beta S q (corner_cyc D.target q p r S.hpq.symm S.hqr S.hpr S.cornerQ) x.1 fi
    (hf.trans hx1)
  have := hbt.right_angle
  rw [hx1, hang] at this
  exact angOf_inj_B hαβ hβγ this.symm


/-- The angle at the vertex `kk` of a tile, as an angle between the other two vertices (either order). -/
theorem localAngle_as_angle (T : Tri) (kk fi g : Fin 3) (hfk : fi ≠ kk) (hgk : g ≠ kk) (hgf : g ≠ fi) :
    T.localAngle (T.pts kk) = cornerAngle (T.pts fi) (T.pts kk) (T.pts g) := by
  rw [Tri.localAngle_vertex]
  rcases fin3_pair kk fi g hfk hgk hgf with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · subst h1; subst h2; rfl
  · subst h1; subst h2
    unfold cornerAngle
    rw [EuclideanGeometry.angle_comm]

/-- **The apex of the first walk tile lies on the left leg** (the first token is `c` on the base). -/
theorem first_apex {D : CongruentDissection N} {e f : ℕ} {α β γ : ℝ} {p q r : Fin 3}
    (S : BandSetup D e f α β γ p q r)
    (hori : 0 < crs (toV2 (D.target.pts q - D.target.pts p)) (toV2 (D.target.pts r - D.target.pts p)))
    {x : Fin N × Plane × Plane} (hx0 : x.2.1 = D.target.pts p)
    (hpar : ∃ s t : ℝ, 0 ≤ s ∧ s < t ∧ t ≤ 1 ∧ x.2.1 = D.target.pts p + s • (D.target.pts q - D.target.pts p) ∧
        x.2.2 = D.target.pts p + t • (D.target.pts q - D.target.pts p))
    (hsd : StepData D e f α β γ p q x) (hc : dist x.2.1 x.2.2 = sideOpp D.model 2) :
    ∃ g : Fin 3, (D.tile x.1).pts g ∈ segment ℝ (D.target.pts p) (D.target.pts r) ∧
      ∃ kk fi : Fin 3, fi ≠ kk ∧ g ≠ kk ∧ g ≠ fi ∧ (D.tile x.1).pts kk = x.2.1 ∧
        (D.tile x.1).pts fi = x.2.2 ∧
        BaseTok D p q (angOf α β γ) (lenOf (ta e f) (tb e f) (tc e f))
          (elemTok D α β x).side (elemTok D α β x).left (elemTok D α β x).right x.1 x.2.1 x.2.2
          ((D.tile x.1).pts g) := by
  obtain ⟨hαβ, hβγ, hαγ, hab, hbc, hac⟩ := BandSetup.distinct S
  obtain ⟨kk, fi, g, hfk, hgk, hgf, hk, hf, hleft, hbt⟩ := hsd
  refine ⟨g, ?_, kk, fi, hfk, hgk, hgf, hk, hf, hbt⟩
  set P := D.target.pts p with hP
  set Q := D.target.pts q with hQ
  set R := D.target.pts r with hR
  set Z := (D.tile x.1).pts g with hZ
  have hang : (D.tile x.1).localAngle ((D.tile x.1).pts kk) = β := by
    have := corner_tile_beta S p (corner_cyc D.target p q r S.hpq S.hpr S.hqr S.cornerP) x.1 kk
      (hk.trans hx0)
    rwa [hk, hx0]
  have hc' : dist ((D.tile x.1).pts kk) ((D.tile x.1).pts fi) = sideOpp D.model 2 := by
    rw [hk, hf]; exact hc
  have hZa : dist ((D.tile x.1).pts kk) Z = sideOpp D.model 0 :=
    beta_corner_other_edge S x.1 kk fi g hfk hgk hgf hang hc'
  rw [hk, hx0] at hZa
  have hβang : cornerAngle ((D.tile x.1).pts fi) ((D.tile x.1).pts kk) Z = β := by
    rw [← localAngle_as_angle _ kk fi g hfk hgk hgf]; exact hang
  rw [hf, hk, hx0] at hβang
  obtain ⟨s, t, h0, hst, ht1, hs, ht⟩ := hpar
  have hne : P ≠ Q := by
    intro h
    have : crs (toV2 (Q - P)) (toV2 (R - P)) = 0 := by rw [← h]; simp [crs, toV2]
    linarith
  have hw : Q - P ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  have hs0 : s = 0 := by
    have : P + s • (Q - P) = P + (0:ℝ) • (Q - P) := by rw [← hs, hx0]; simp
    exact smul_injective_of_ne hw (add_left_cancel this)
  subst hs0
  have hv : x.2.2 - P = t • (Q - P) := by rw [ht]; abel
  have hZ0 : 0 < dist P Z := by rw [hZa, S.hsa]; exact_mod_cast a_pos e f S.he S.hef
  have hPZ : Z - P ≠ 0 := by
    intro h; rw [sub_eq_zero] at h; rw [h, dist_self] at hZ0; exact lt_irrefl _ hZ0
  have hL : ta e f < dist P R := by exact_mod_cast S.haL
  have hPR : R - P ≠ 0 := by
    intro h; rw [sub_eq_zero] at h; rw [h, dist_self] at hL
    have := a_pos e f S.he S.hef; have : (0:ℝ) < ta e f := by exact_mod_cast this
    linarith
  have hang1 : InnerProductGeometry.angle (Q - P) (Z - P) = β := by
    unfold cornerAngle at hβang
    rw [EuclideanGeometry.angle, vsub_eq_sub, vsub_eq_sub, hv,
      InnerProductGeometry.angle_smul_left_of_pos _ _ (by linarith)] at hβang
    exact hβang
  have hang2 : InnerProductGeometry.angle (Q - P) (R - P) = β := by
    have := S.cornerP
    unfold cornerAngle at this
    rw [EuclideanGeometry.angle, vsub_eq_sub, vsub_eq_sub] at this
    exact this
  have hc1 : 0 < cross (Q - P) (Z - P) := by
    have := hleft; rw [hx0] at this; rwa [← crs_toV2]
  have hc2 : 0 < cross (Q - P) (R - P) := by rwa [← crs_toV2]
  have hdir := dir_eq_of_angle hw hPZ hPR hc1 hc2 (hang1.trans hang2.symm)
  have hnZ : ‖Z - P‖ = ta e f := by
    rw [← dist_eq_norm, dist_comm, hZa, S.hsa]
  have hnR : ‖R - P‖ = dist P R := by rw [← dist_eq_norm, dist_comm]
  rw [hnZ, hnR] at hdir
  have hLpos : 0 < dist P R := lt_trans (by exact_mod_cast a_pos e f S.he S.hef) hL
  have hZeq : Z = P + ((ta e f : ℝ) / dist P R) • (R - P) := by
    have : Z - P = ((ta e f : ℝ) / dist P R) • (R - P) := by
      have h2 : (dist P R)⁻¹ • ((dist P R) • (Z - P)) = (dist P R)⁻¹ • ((ta e f : ℝ) • (R - P)) := by
        rw [hdir]
      rw [smul_smul, inv_mul_cancel₀ hLpos.ne', one_smul, smul_smul] at h2
      rw [h2]; congr 1; ring
    rw [← this]; abel
  rw [hZeq]
  exact mem_segment_of_param (div_nonneg (by positivity) hLpos.le)
    ((div_le_one hLpos).mpr hL.le)


/-- **The apex of the last walk tile lies on the right leg** (the last token is `c` on the base). -/
theorem last_apex {D : CongruentDissection N} {e f : ℕ} {α β γ : ℝ} {p q r : Fin 3}
    (S : BandSetup D e f α β γ p q r)
    (hori : 0 < crs (toV2 (D.target.pts q - D.target.pts p)) (toV2 (D.target.pts r - D.target.pts p)))
    {x : Fin N × Plane × Plane} (hx1 : x.2.2 = D.target.pts q)
    (hpar : ∃ s t : ℝ, 0 ≤ s ∧ s < t ∧ t ≤ 1 ∧ x.2.1 = D.target.pts p + s • (D.target.pts q - D.target.pts p) ∧
        x.2.2 = D.target.pts p + t • (D.target.pts q - D.target.pts p))
    (hsd : StepData D e f α β γ p q x) (hc : dist x.2.1 x.2.2 = sideOpp D.model 2) :
    ∃ g : Fin 3, (D.tile x.1).pts g ∈ segment ℝ (D.target.pts q) (D.target.pts r) ∧
      ∃ kk fi : Fin 3, fi ≠ kk ∧ g ≠ kk ∧ g ≠ fi ∧ (D.tile x.1).pts kk = x.2.1 ∧
        (D.tile x.1).pts fi = x.2.2 ∧
        BaseTok D p q (angOf α β γ) (lenOf (ta e f) (tb e f) (tc e f))
          (elemTok D α β x).side (elemTok D α β x).left (elemTok D α β x).right x.1 x.2.1 x.2.2
          ((D.tile x.1).pts g) := by
  obtain ⟨hαβ, hβγ, hαγ, hab, hbc, hac⟩ := BandSetup.distinct S
  obtain ⟨kk, fi, g, hfk, hgk, hgf, hk, hf, hleft, hbt⟩ := hsd
  refine ⟨g, ?_, kk, fi, hfk, hgk, hgf, hk, hf, hbt⟩
  set P := D.target.pts p with hP
  set Q := D.target.pts q with hQ
  set R := D.target.pts r with hR
  set Z := (D.tile x.1).pts g with hZ
  have hang : (D.tile x.1).localAngle ((D.tile x.1).pts fi) = β := by
    have := corner_tile_beta S q (corner_cyc D.target q p r S.hpq.symm S.hqr S.hpr S.cornerQ) x.1 fi
      (hf.trans hx1)
    rwa [hf, hx1]
  have hc' : dist ((D.tile x.1).pts fi) ((D.tile x.1).pts kk) = sideOpp D.model 2 := by
    rw [hk, hf, dist_comm]; exact hc
  have hZa : dist ((D.tile x.1).pts fi) Z = sideOpp D.model 0 :=
    beta_corner_other_edge S x.1 fi kk g hfk.symm hgf hgk hang hc'
  rw [hf, hx1] at hZa
  have hβang : cornerAngle ((D.tile x.1).pts kk) ((D.tile x.1).pts fi) Z = β := by
    rw [← localAngle_as_angle _ fi kk g hfk.symm hgf hgk]; exact hang
  rw [hf, hk, hx1] at hβang
  obtain ⟨s, t, h0, hst, ht1, hs, ht⟩ := hpar
  have hne : P ≠ Q := by
    intro h
    have : crs (toV2 (Q - P)) (toV2 (R - P)) = 0 := by rw [← h]; simp [crs, toV2]
    linarith
  have hw : Q - P ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  have ht1' : t = 1 := by
    have : P + t • (Q - P) = P + (1:ℝ) • (Q - P) := by rw [← ht, hx1]; simp
    exact smul_injective_of_ne hw (add_left_cancel this)
  subst ht1'
  have hv : x.2.1 - Q = (s - 1) • (Q - P) := by rw [hs, sub_smul, one_smul]; abel
  have hZ0 : 0 < dist Q Z := by rw [hZa, S.hsa]; exact_mod_cast a_pos e f S.he S.hef
  have hQZ : Z - Q ≠ 0 := by
    intro h; rw [sub_eq_zero] at h; rw [h, dist_self] at hZ0; exact lt_irrefl _ hZ0
  have hL : ta e f < dist Q R := by exact_mod_cast S.haR
  have hQR : R - Q ≠ 0 := by
    intro h; rw [sub_eq_zero] at h; rw [h, dist_self] at hL
    have := a_pos e f S.he S.hef; have : (0:ℝ) < ta e f := by exact_mod_cast this
    linarith
  have hang1 : InnerProductGeometry.angle (Q - P) (Z - Q) = Real.pi - β := by
    unfold cornerAngle at hβang
    rw [EuclideanGeometry.angle, vsub_eq_sub, vsub_eq_sub, hv,
      InnerProductGeometry.angle_smul_left_of_neg _ _ (by linarith),
      InnerProductGeometry.angle_neg_left] at hβang
    linarith
  have hang2 : InnerProductGeometry.angle (Q - P) (R - Q) = Real.pi - β := by
    have := S.cornerQ
    unfold cornerAngle at this
    rw [EuclideanGeometry.angle, vsub_eq_sub, vsub_eq_sub] at this
    have h3 : P - Q = -(Q - P) := by abel
    rw [h3, InnerProductGeometry.angle_neg_left] at this
    linarith
  have hc1 : 0 < cross (Q - P) (Z - Q) := by
    have := hleft
    rw [crs_toV2] at this
    have e1 : cross (Q - P) (Z - x.2.1) = cross (Q - P) (Z - Q) := by
      have : x.2.1 = Q + (s - 1) • (Q - P) := by rw [← hv]; abel
      rw [this]
      unfold cross
      simp only [PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
      ring
    linarith
  have hc2 : 0 < cross (Q - P) (R - Q) := by
    have e1 : cross (Q - P) (R - Q) = cross (Q - P) (R - P) := by
      unfold cross
      simp only [PiLp.sub_apply]
      ring
    rw [e1, ← crs_toV2]; exact hori
  have hdir := dir_eq_of_angle hw hQZ hQR hc1 hc2 (hang1.trans hang2.symm)
  have hnZ : ‖Z - Q‖ = ta e f := by
    rw [← dist_eq_norm, dist_comm, hZa, S.hsa]
  have hnR : ‖R - Q‖ = dist Q R := by rw [← dist_eq_norm, dist_comm]
  rw [hnZ, hnR] at hdir
  have hLpos : 0 < dist Q R := lt_trans (by exact_mod_cast a_pos e f S.he S.hef) hL
  have hZeq : Z = Q + ((ta e f : ℝ) / dist Q R) • (R - Q) := by
    have : Z - Q = ((ta e f : ℝ) / dist Q R) • (R - Q) := by
      have h2 : (dist Q R)⁻¹ • ((dist Q R) • (Z - Q)) = (dist Q R)⁻¹ • ((ta e f : ℝ) • (R - Q)) := by
        rw [hdir]
      rw [smul_smul, inv_mul_cancel₀ hLpos.ne', one_smul, smul_smul] at h2
      rw [h2]; congr 1; ring
    rw [← this]; abel
  rw [hZeq]
  exact mem_segment_of_param (div_nonneg (by positivity) hLpos.le)
    ((div_le_one hLpos).mpr hL.le)

#print axioms last_apex

end Erdos634.LaczJunction.Walk
