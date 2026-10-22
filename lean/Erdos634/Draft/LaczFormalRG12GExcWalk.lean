-- Draft/LaczFormalRG12GExcWalk.lean -- Laczkovich (DCG 48 (2012)), Sect. 6.2, statement (i) for the edges of Gamma_except: NO INNER POINT of an edge `XY` of Gamma_except is a vertex of Gamma_kite.
-- Route (the printed proof, l. 1346-1352): an inner point `V` of `XY` that is a vertex of Gamma_kite is an interior (2,2,2) vertex, so every tile through `V` has `V` as a CORNER (`hvtx`); hence `V` is a division point of
-- BOTH divisions (`div_vertex`: a point strictly inside a tile side cannot be a corner of that tile), the tiles `T_m, T'_n` with head `V` lie in the gamma-runs (`V` is strictly nearer to `X` than `Y`) so they have angle
-- gamma at `V` and flank the ray `-d`, and the division continues along `d` past `V`.  This contradicts `kite_vertex_no_gamma_line` (Fig. 5).
-- Hypotheses: `CaseC`, `a, b` commensurable, `c` not a rational multiple of `a`, gamma < pi/2, != pi/3 (to get the successor/predecessor kite edge), `AngGen`, `HasFansC`, a convex polygon region.
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 6.2), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalRG12GExc

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

variable {N M : ℕ}

theorem scal_unique {d : V2} (hd : d ≠ 0) {a b : ℝ} (h : ((a * d.1, a * d.2) : V2) = (b * d.1, b * d.2)) : a = b := by
  have h1 : a * d.1 = b * d.1 := congrArg Prod.fst h
  have h2 : a * d.2 = b * d.2 := congrArg Prod.snd h
  by_contra hne
  apply hd
  have h3 : (a - b) * d.1 = 0 := by linarith
  have h4 : (a - b) * d.2 = 0 := by linarith
  have hab : a - b ≠ 0 := sub_ne_zero.mpr hne
  exact Prod.ext ((mul_eq_zero.mp h3).resolve_left hab) ((mul_eq_zero.mp h4).resolve_left hab)

theorem coord_of {A X : Plane} {t : ℝ} {d : V2} (h : toV2 (A - X) = (t * d.1, t * d.2)) : A 0 = X 0 + t * d.1 ∧ A 1 = X 1 + t * d.2 := by
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  simp only [toV2_sub] at h1 h2
  constructor <;> linarith

theorem pt_eq_of_pos {A B X : Plane} {t : ℝ} {d : V2} (hA : toV2 (A - X) = (t * d.1, t * d.2)) (hB : toV2 (B - X) = (t * d.1, t * d.2)) : A = B := by
  obtain ⟨a0, a1⟩ := coord_of hA
  obtain ⟨b0, b1⟩ := coord_of hB
  ext i
  fin_cases i
  · simp only [Fin.zero_eta]; linarith
  · simp only [Fin.mk_one]; linarith

/-- A point strictly inside a side of a tile (in the sense of a left step) is not a corner of that tile. -/
theorem open_side_inner {T : Tri} {d' : V2} {X0 Y0 V : Plane} (hS : TriStep T d' X0 Y0) {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1)
    (hV : V = X0 + τ • (Y0 - X0)) (hvtx : V ∈ T.carrier → ∃ k, T.pts k = V) : False := by
  have hS' := hS
  obtain ⟨kk, f, g, hk, hf, hfk, hgk, hgf, hpar, hleft⟩ := hS'
  have hX0 : X0 ∈ T.carrier := hk ▸ subset_convexHull ℝ _ ⟨kk, rfl⟩
  have hY0 : Y0 ∈ T.carrier := hf ▸ subset_convexHull ℝ _ ⟨f, rfl⟩
  have hVT : V ∈ T.carrier := by
    rw [hV]; exact T.convex.add_smul_sub_mem hX0 hY0 ⟨hτ0.le, hτ1.le⟩
  have hvec : toV2 (V - X0) = (τ * (toV2 (Y0 - X0)).1, τ * (toV2 (Y0 - X0)).2) := by
    rw [hV]; unfold toV2; ext <;> simp
  have hne : toV2 (Y0 - X0) ≠ 0 := hpar.ne_left
  have hline : crs d' (toV2 (V - X0)) = 0 := by
    rw [hvec]
    have := hpar.1
    unfold crs at this ⊢
    simp only at this ⊢
    nlinarith [this]
  have hV1 : V ≠ X0 := by
    intro h
    have : toV2 (V - X0) = 0 := by rw [h]; unfold toV2; ext <;> simp
    rw [hvec] at this
    apply hne
    have a1 : τ * (toV2 (Y0 - X0)).1 = 0 := congrArg Prod.fst this
    have a2 : τ * (toV2 (Y0 - X0)).2 = 0 := congrArg Prod.snd this
    exact Prod.ext ((mul_eq_zero.mp a1).resolve_left hτ0.ne') ((mul_eq_zero.mp a2).resolve_left hτ0.ne')
  have hV2 : V ≠ Y0 := by
    intro h
    have : toV2 (V - X0) = toV2 (Y0 - X0) := by rw [h]
    rw [hvec] at this
    apply hne
    have a1 : τ * (toV2 (Y0 - X0)).1 = (toV2 (Y0 - X0)).1 := congrArg Prod.fst this
    have a2 : τ * (toV2 (Y0 - X0)).2 = (toV2 (Y0 - X0)).2 := congrArg Prod.snd this
    have b1 : (τ - 1) * (toV2 (Y0 - X0)).1 = 0 := by linarith
    have b2 : (τ - 1) * (toV2 (Y0 - X0)).2 = 0 := by linarith
    have hτ : τ - 1 ≠ 0 := by linarith
    exact Prod.ext ((mul_eq_zero.mp b1).resolve_left hτ) ((mul_eq_zero.mp b2).resolve_left hτ)
  obtain ⟨m, hm0, hmpos⟩ := open_side_of_triStep hS hVT hline hV1 hV2
  obtain ⟨k, hk'⟩ := hvtx hVT
  exact edge_coords_not_vertex T m V hm0 hmpos k hk'

/-- **A step element of a division containing `V` strictly inside its side**: `V` is not a corner of that tile. -/
theorem not_inner_step (D : RegionDissection N) {b : Bool} {d : V2} (hd : d ≠ 0) {e : Fin N × Plane × Plane} (he : StepU D b d e) {X V : Plane}
    {t0 t1 v : ℝ} (h0 : toV2 (e.2.1 - X) = (t0 * d.1, t0 * d.2)) (h1 : toV2 (e.2.2 - X) = (t1 * d.1, t1 * d.2))
    (hv : toV2 (V - X) = (v * d.1, v * d.2)) (h01 : t0 < v) (h1v : v < t1)
    (hvtx : V ∈ (D.tile e.1).carrier → ∃ k, (D.tile e.1).pts k = V) : False := by
  obtain ⟨a0, a1⟩ := coord_of h0
  obtain ⟨b0, b1⟩ := coord_of h1
  obtain ⟨c0, c1⟩ := coord_of hv
  have hpos : 0 < t1 - t0 := by linarith
  cases b
  · -- right tiles: `TriStep (neg2 d) e.2.2 e.2.1`
    have he' : TriStep (D.tile e.1) (neg2 d) e.2.2 e.2.1 := by simpa [StepU] using he
    refine open_side_inner he' (τ := (t1 - v) / (t1 - t0)) (by apply div_pos <;> linarith) (by rw [div_lt_one hpos]; linarith) ?_ hvtx
    ext i
    fin_cases i
    · simp only [Fin.zero_eta, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
      rw [c0, a0, b0]; field_simp; ring
    · simp only [Fin.mk_one, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
      rw [c1, a1, b1]; field_simp; ring
  · have he' : TriStep (D.tile e.1) d e.2.1 e.2.2 := by simpa [StepU] using he
    refine open_side_inner he' (τ := (v - t0) / (t1 - t0)) (by apply div_pos <;> linarith) (by rw [div_lt_one hpos]; linarith) ?_ hvtx
    ext i
    fin_cases i
    · simp only [Fin.zero_eta, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
      rw [c0, a0, b0]; field_simp; ring
    · simp only [Fin.mk_one, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
      rw [c1, a1, b1]; field_simp; ring

/-- **A corner point of a division**: if every tile through `V` has `V` as a corner and `V` lies on the segment at parameter `0 < v < T`, then `V` is the head of an element and the tail of an element of the division. -/
theorem div_vertex (D : RegionDissection N) {b : Bool} {d : V2} (hd : d ≠ 0) {X Z : Plane} {L : List (Fin N × Plane × Plane)} (W : WalkU D b d X Z L)
    {V : Plane} {v T : ℝ} (hv : toV2 (V - X) = (v * d.1, v * d.2)) (hv0 : 0 < v) (hT : toV2 (Z - X) = (T * d.1, T * d.2)) (hvT : v < T)
    (hvtx : ∀ i, V ∈ (D.tile i).carrier → ∃ k, (D.tile i).pts k = V) :
    (∃ e ∈ L, e.2.2 = V) ∧ (∃ e ∈ L, e.2.1 = V) := by
  have hst := walkU_mem_step W
  constructor
  · obtain ⟨e, he, t0, t1, h0, h1, ht0, ht1⟩ := walkU_cover' W hd hT v hv0 hvT.le
    refine ⟨e, he, ?_⟩
    rcases ht1.eq_or_lt with h | h
    · rw [← h] at h1; exact pt_eq_of_pos h1 hv
    · exact (not_inner_step D hd (hst e he) h0 h1 hv ht0 h (hvtx e.1)).elim
  · obtain ⟨e, he, t0, t1, h0, h1, ht0, ht1⟩ := walkU_cover W hd hT v hv0.le hvT
    refine ⟨e, he, ?_⟩
    rcases ht0.eq_or_lt with h | h
    · rw [h] at h0; exact pt_eq_of_pos h0 hv
    · exact (not_inner_step D hd (hst e he) h0 h1 hv h ht1 (hvtx e.1)).elim

theorem walkU_single_end {D : RegionDissection N} {b : Bool} {d : V2} {X Y : Plane} {e : Fin N × Plane × Plane} (W : WalkU D b d X Y [e]) : Y = e.2.2 := by
  cases W with
  | cons hS W' => cases W'; rfl

/-- Data of a `γ`-run: the prefix walk to `H` (nonempty), the suffix walk from `H`, the prefix property. -/
theorem grun_split (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3)) {b : Bool} {d : V2} {X Z : Plane} {L : List (Fin N × Plane × Plane)}
    (W : WalkU D.toRegionDissection b d X Z L) {H : Plane} (hr : GRunEnd D idx L H) :
    ∃ L' L'' : List (Fin N × Plane × Plane), L = L' ++ L'' ∧ L' ≠ [] ∧ WalkU D.toRegionDissection b d X H L' ∧ WalkU D.toRegionDissection b d H Z L'' ∧
      (∀ x ∈ L', GammaHead D idx x) := by
  obtain ⟨L', L'', hL, hne, hall, -, e0, hlast, he0⟩ := hr
  subst hL
  obtain ⟨M, w1, w2⟩ := walkU_append.mp W
  have hM : M = H := by
    obtain ⟨L0, hL0⟩ : ∃ L0, L' = L0 ++ [e0] := ⟨L'.dropLast, (List.dropLast_append_getLast? e0 (Option.mem_def.mpr hlast)).symm⟩
    rw [hL0] at w1
    obtain ⟨M', -, w3⟩ := walkU_append.mp w1
    rw [walkU_single_end w3, he0]
  subst hM
  exact ⟨L', L'', rfl, hne, w1, w2, hall⟩

theorem dist_pos {X H : Plane} {t : ℝ} {d : V2} (ht : 0 ≤ t) (h : toV2 (H - X) = (t * d.1, t * d.2)) :
    dist X H = t * Real.sqrt (d.1 ^ 2 + d.2 ^ 2) := by
  obtain ⟨a0, a1⟩ := coord_of h
  rw [EuclideanSpace.dist_eq, Fin.sum_univ_two]
  simp only [Real.dist_eq, sq_abs]
  rw [a0, a1]
  have : (X 0 - (X 0 + t * d.1)) ^ 2 + (X 1 - (X 1 + t * d.2)) ^ 2 = t ^ 2 * (d.1 ^ 2 + d.2 ^ 2) := by ring
  rw [this, Real.sqrt_mul (sq_nonneg t), Real.sqrt_sq ht]

theorem pos_le_of_dist_le {X H H' : Plane} {t t' : ℝ} {d : V2} (hd : d ≠ 0) (ht : 0 ≤ t) (ht' : 0 ≤ t') (h : toV2 (H - X) = (t * d.1, t * d.2))
    (h' : toV2 (H' - X) = (t' * d.1, t' * d.2)) (hle : dist X H ≤ dist X H') : t ≤ t' := by
  rw [dist_pos ht h, dist_pos ht' h'] at hle
  have hs : 0 < Real.sqrt (d.1 ^ 2 + d.2 ^ 2) := by
    apply Real.sqrt_pos.mpr
    by_contra hh
    push Not at hh
    apply hd
    have e1 : d.1 ^ 2 = 0 := le_antisymm (by nlinarith [sq_nonneg d.2]) (sq_nonneg _)
    have e2 : d.2 ^ 2 = 0 := le_antisymm (by nlinarith [sq_nonneg d.1]) (sq_nonneg _)
    exact Prod.ext (pow_eq_zero_iff (two_ne_zero) |>.mp e1) (pow_eq_zero_iff (two_ne_zero) |>.mp e2)
  exact le_of_mul_le_mul_right hle hs

/-- A point of the open segment `XH` has parameter `b * tH` with `0 < b < 1`. -/
theorem seg_param {X H V : Plane} {tH : ℝ} {d : V2} (hV : V ∈ openSegment ℝ X H) (h : toV2 (H - X) = (tH * d.1, tH * d.2)) :
    ∃ b : ℝ, 0 < b ∧ b < 1 ∧ toV2 (V - X) = ((b * tH) * d.1, (b * tH) * d.2) := by
  obtain ⟨a, b, ha, hb, hab, hVe⟩ := hV
  obtain ⟨h0, h1⟩ := coord_of h
  refine ⟨b, hb, by linarith, ?_⟩
  have e0 : V 0 = a * X 0 + b * H 0 := by rw [← hVe]; simp
  have e1 : V 1 = a * X 1 + b * H 1 := by rw [← hVe]; simp
  have ha' : a = 1 - b := by linarith
  rw [toV2_sub]
  ext
  · simp only; rw [e0, h0, ha']; ring
  · simp only; rw [e1, h1, ha']; ring

/-- Every tile through an interior `(2,2,2)` vertex has it as a corner. -/
theorem tile_vertex_222 (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (idx : Fin N → Equiv.Perm (Fin 3))
    (hidxA : ∀ i v, D.model.angleAt (idx i v) = (D.tile i).angleAt v) {V : Plane} (hint : V ∈ interior D.region)
    (c0 : cnt D idx V 0 = 2) (c1 : cnt D idx V 1 = 2) (c2 : cnt D idx V 2 = 2) (G : AngGen (fun l => D.model.angleAt l)) :
    ∀ i, V ∈ (D.tile i).carrier → ∃ k, (D.tile i).pts k = V := by
  intro i hi
  obtain ⟨F, s, ℓ, hF, hlab, hsurj, -⟩ := fan222_tile D idx hidxA hint c0 c1 c2 G
  obtain ⟨j, -, hj⟩ := hsurj ⟨i, hi⟩
  obtain ⟨k, hk, -⟩ := hlab j
  rw [hj] at hk
  exact ⟨k, hk⟩

/-- An element of the division whose head `V` lies strictly before the end `H` of the run belongs to the run. -/
theorem elem_in_prefix (D : RegionDissection N) {b : Bool} {d : V2} (hd : d ≠ 0) {X H Z V : Plane} {L L' L'' : List (Fin N × Plane × Plane)}
    (hdec : L = L' ++ L'') (w2 : WalkU D b d H Z L'') {e : Fin N × Plane × Plane} (he : e ∈ L) (hVe : e.2.2 = V) {v t : ℝ}
    (hv : toV2 (V - X) = (v * d.1, v * d.2)) (hH : toV2 (H - X) = (t * d.1, t * d.2)) (hvt : v < t) : e ∈ L' := by
  rw [hdec] at he
  rcases List.mem_append.mp he with h | h
  · exact h
  · exfalso
    obtain ⟨S, hS0, hS, -, hel⟩ := walkU_pos w2
    obtain ⟨u0, u1, hu0, hu1, hu00, hlt, -⟩ := hel e h
    rw [hVe] at hu1
    have e1 := toV2_sub3 V H X
    rw [hv, hH, hu1] at e1
    simp only at e1
    have := scal_unique hd (a := v) (b := u1 + t) (by
      rw [e1]; ext <;> simp only <;> ring)
    linarith

set_option maxHeartbeats 3200000 in
/-- **Statement (i) for `Γ_except`** (Laczkovich, DCG 48 (2012), Sect. 6.2): no inner point `V` of an edge `XY` of `Γ_except` is a vertex of `Γ_kite`. -/
theorem gexc_interior_not_kite [NeZero M] (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (hC : CaseC D idx) (hab : Comm (slen D 0) (slen D 1)) (hac : ¬ Comm (slen D 0) (slen D 2))
    (h1 : D.model.angleAt 2 < Real.pi / 2) (h3 : D.model.angleAt 2 ≠ Real.pi / 3) (G : AngGen (fun l => D.model.angleAt l))
    {X Y V : Plane} (hE : GExc D idx X Y) (hV : V ∈ openSegment ℝ X Y)
    (hK : (∃ X', GKite D idx X' V) ∨ (∃ Z', GKite D idx V Z')) : False := by
  classical
  obtain ⟨X', Z', hXV, hVZ⟩ : ∃ X' Z', GKite D idx X' V ∧ GKite D idx V Z' := by
    rcases hK with ⟨X', hX⟩ | ⟨Z', hZ⟩
    · obtain ⟨Z', hZ'⟩ := gkite_succ_exists D P hreg idx hC hab hac h1 h3 hX
      exact ⟨X', Z', hX, hZ'⟩
    · obtain ⟨X', hX', -⟩ := gkite_pred_unique D P hreg idx hC hab hac h1 h3 hZ
      exact ⟨X', Z', hX', hZ⟩
  obtain ⟨⟨hVint, c0, c1, c2⟩, -⟩ := gkite_vertex_type D P hreg idx hC.hidxA hC.hregc h1 h3 hXV
  have hvtx := tile_vertex_222 D idx hC.hidxA hVint c0 c1 c2 G
  obtain ⟨d, Zp, L1, L2, H1, H2, hd, hnb, W1, W2, hL1, hL2, -, -, hr1, hr2, hY⟩ := hE
  have WU1 := walkU_of_T W1
  have WU2 := walkU_of_R W2
  obtain ⟨L1', L1'', hdec1, hne1, p1, s1, hall1⟩ := grun_split D idx WU1 hr1
  obtain ⟨L2', L2'', hdec2, hne2, p2, s2, hall2⟩ := grun_split D idx WU2 hr2
  obtain ⟨t1, ht10, hH1, hpos1, -⟩ := walkU_pos p1
  obtain ⟨t2, ht20, hH2, hpos2, -⟩ := walkU_pos p2
  have ht1 : 0 < t1 := hpos1 hne1
  have ht2 : 0 < t2 := hpos2 hne2
  obtain ⟨TL, hTL0, hTL, -, -⟩ := walkU_pos WU1
  obtain ⟨S1, hS10, hS1, -, -⟩ := walkU_pos s1
  -- TL = t1 + S1
  have hTLe : t1 ≤ TL := by
    have e1 := toV2_sub3 Zp H1 X
    rw [hTL, hH1, hS1] at e1
    simp only at e1
    have := scal_unique hd (a := TL) (b := S1 + t1) (by rw [e1]; ext <;> simp only <;> ring)
    linarith
  -- the parameter of V
  obtain ⟨v, hv0, hv1, hv2, hvpos⟩ : ∃ v : ℝ, 0 < v ∧ v < t1 ∧ v < t2 ∧ toV2 (V - X) = (v * d.1, v * d.2) := by
    rcases hY with ⟨rfl, hle⟩ | ⟨rfl, hle⟩
    · obtain ⟨b, hb0, hb1, hbv⟩ := seg_param hV hH1
      have := pos_le_of_dist_le hd ht10 ht20 hH1 hH2 hle
      refine ⟨b * t1, by positivity, by nlinarith, by nlinarith, hbv⟩
    · obtain ⟨b, hb0, hb1, hbv⟩ := seg_param hV hH2
      have := pos_le_of_dist_le hd ht20 ht10 hH2 hH1 hle
      refine ⟨b * t2, by positivity, by nlinarith, by nlinarith, hbv⟩
  have hvT : v < TL := lt_of_lt_of_le hv1 hTLe
  -- the divisions have V as a division point
  obtain ⟨⟨eL, heL, heLV⟩, ⟨eL', heL', heL'V⟩⟩ := div_vertex D.toRegionDissection hd WU1 hvpos hv0 hTL hvT hvtx
  obtain ⟨⟨eR, heR, heRV⟩, -⟩ := div_vertex D.toRegionDissection hd WU2 hvpos hv0 hTL hvT hvtx
  have heLp : eL ∈ L1' := elem_in_prefix D.toRegionDissection hd hdec1 s1 heL heLV hvpos hH1 hv1
  have heRp : eR ∈ L2' := elem_in_prefix D.toRegionDissection hd hdec2 s2 heR heRV hvpos hH2 hv2
  obtain ⟨kgi, hkgi, hgli⟩ := hall1 eL heLp
  obtain ⟨kgj, hkgj, hglj⟩ := hall2 eR heRp
  have hiL : TriStep (D.tile eL.1) d eL.2.1 eL.2.2 := by simpa [StepU] using walkU_mem_step WU1 eL heL
  have hjR : TriStep (D.tile eR.1) (neg2 d) eR.2.2 eR.2.1 := by simpa [StepU] using walkU_mem_step WU2 eR heR
  have hnL : TriStep (D.tile eL'.1) d eL'.2.1 eL'.2.2 := by simpa [StepU] using walkU_mem_step WU1 eL' heL'
  rw [heLV] at hiL hkgi
  rw [heRV] at hjR hkgj
  rw [heL'V] at hnL
  exact kite_vertex_no_gamma_line D P hreg idx hC h1 h3 G hXV hVZ hiL hjR hnL ⟨kgi, hkgi, hgli⟩ ⟨kgj, hkgj, hglj⟩

end Erdos634.Draft.LaczFormal.RG

#print axioms Erdos634.Draft.LaczFormal.RG.gexc_interior_not_kite
