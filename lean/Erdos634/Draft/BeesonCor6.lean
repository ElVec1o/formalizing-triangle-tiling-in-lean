import Erdos634.Draft.BeesonCor6Geom
import Erdos634.Draft.BeesonCor5Legs
import Erdos634.Draft.BeesonT15Conv
import Erdos634.Draft.LaczFormalTransport

/-!
# Beeson (arXiv 1206.2229v4) Corollary 6: the assembly of Fig. 27

NOTE, UNAUDITED.  Credit: Beeson (arXiv 1206.2229, Cor 5, Cor 6, Fig. 27 adapted from Laczkovich's [8, Fig. 5]),
Laczkovich (Discrete Math. 140 (1995); DCG 48 (2012)), Beeson-Zhang, Zhang.

Statement (`cor6_exists`): `a < c`, `a^2 + c b = c^2` (`c | a^2`, `b = c - a^2/c`), `gcd(a,b,c) = 1`.  Then for some
positive integer `L` there is a `CongruentDissection` of `N = L^2 (b+c)(b+2c)` copies of the tile `(a,b,c)` whose target
has sides `L c^2`, `L b (b+2c)`, `L c (b+c)` (angles `(2 alpha, alpha, 2 beta)`; the same triangle as `beeson_thm14`).

Construction (as printed, with the legs made explicit): `L = pp` from `cor5_legs` (leg of Cor 5's triangle `= pp/rr` in
units of the tile); the blue isosceles triangle (Cor 5, laddered by `b c rr`, then transported by the similarity of ratio
`1/s`) has legs `b c L`; the other two are laddered tiles with ratios `(b+c) L` and `c L`.  PRINT NOTE: the printed count
`L^2 (b+c)^2 + c^2 + bc` is a typo for `L^2 ((b+c)^2 + c^2 + bc) = L^2 (b+c)(b+2c)`.  PRINT NOTE 2: Beeson takes the
legs of Cor 5's triangle to be an integer `L`; here only `leg/s = pp/rr` rational is used (and exported by `cor5_legs`),
and the count of the blue part is computed by area, so no integrality of the legs is needed.
-/

namespace Erdos634.BeesonCor6

open Erdos634.Geometry Erdos634.CertCoord Erdos634.RegionDissection Erdos634.Realizable Erdos634.DissectionMap
  Erdos634.TranslateDissection Erdos634.Ladder Erdos634.SssCongruent Erdos634.LaczTransport MeasureTheory
  Erdos634.BeesonCor6Geom Erdos634.BeesonT15Conv
open scoped ENNReal

/-! ### A. transport by explicit similarity ratio -/

theorem transport_of_dist {N : ℕ} (D : CongruentDissection N) (T' : Tri) (r : ℝ) (hr : 0 < r)
    (hdist : ∀ x y, dist (T'.pts x) (T'.pts y) = r * dist (D.target.pts x) (D.target.pts y)) :
    ∃ D' : CongruentDissection N, D'.target.carrier = T'.carrier ∧
      D'.model.Congruent (scaleTri r hr.ne' D.model) := by
  set p : Plane := D.target.pts 0 with hp
  set hom := homothetyEquiv p r hr.ne' with hhom
  have hU : (mapTri hom D.target).Congruent T' := by
    refine congruent_of_dist (fun i j => ?_)
    show dist (hom (D.target.pts i)) (hom (D.target.pts j)) = _
    rw [hhom, homothetyEquiv_dist, abs_of_pos hr, hdist]
  obtain ⟨f, σ, hf⟩ := hU
  let D₁ := scaleDissection p r hr.ne' D
  let g : Plane ≃ᵃⁱ[ℝ] Plane := f.toRealAffineIsometryEquiv
  refine ⟨isoCongruentDissection g D₁, ?_, ?_⟩
  · rw [iso_target, mapTri_carrier]
    show g.toAffineEquiv '' (mapTri hom D.target).carrier = T'.carrier
    rw [← mapTri_carrier]
    simp only [Tri.carrier, mapTri]
    have hpts : (g.toAffineEquiv ∘ (hom ∘ D.target.pts)) = T'.pts ∘ σ := by
      funext k
      exact hf k
    rw [hpts, Function.Surjective.range_comp σ.surjective]
  · rw [iso_model]
    refine congruent_of_dist (fun i j => ?_)
    show dist (hom (D.model.pts i)) (hom (D.model.pts j)) = dist ((scaleTri r hr.ne' D.model).pts i)
      ((scaleTri r hr.ne' D.model).pts j)
    rw [hhom, homothetyEquiv_dist, scaleTri_pts, scaleTri_pts, dist_homothety]

/-! ### B. scaling and congruence -/

theorem scaleTri_one_congr (T : Tri) : (scaleTri 1 one_ne_zero T).Congruent T := by
  refine congruent_of_dist (fun i j => ?_)
  simp only [scaleTri_pts, dist_homothety, abs_one, one_mul]

theorem scaleTri_congr (r : ℝ) (hr : r ≠ 0) {M S : Tri} (h : M.Congruent S) :
    (scaleTri r hr M).Congruent (scaleTri r hr S) := by
  obtain ⟨f, σ, hf⟩ := h
  refine congruent_of_dist_perm σ (fun i j => ?_)
  simp only [scaleTri_pts, dist_homothety]
  have := f.dist_eq (M.pts i) (M.pts j)
  rw [hf i, hf j] at this
  rw [← this]

theorem dist_all (T U : Tri) (k : ℝ)
    (e01 : dist (U.pts 0) (U.pts 1) = k * dist (T.pts 0) (T.pts 1))
    (e02 : dist (U.pts 0) (U.pts 2) = k * dist (T.pts 0) (T.pts 2))
    (e12 : dist (U.pts 1) (U.pts 2) = k * dist (T.pts 1) (T.pts 2)) :
    ∀ x y, dist (U.pts x) (U.pts y) = k * dist (T.pts x) (T.pts y) := by
  have e10 : dist (U.pts 1) (U.pts 0) = k * dist (T.pts 1) (T.pts 0) := by
    rw [dist_comm, e01, dist_comm (T.pts 1)]
  have e20 : dist (U.pts 2) (U.pts 0) = k * dist (T.pts 2) (T.pts 0) := by
    rw [dist_comm, e02, dist_comm (T.pts 2)]
  have e21 : dist (U.pts 2) (U.pts 1) = k * dist (T.pts 2) (T.pts 1) := by
    rw [dist_comm, e12, dist_comm (T.pts 2)]
  intro x y
  fin_cases x <;> fin_cases y <;> simp [e01, e02, e12, e10, e20, e21]

/-! ### C. ladder with the distance scaling exported -/

theorem ladder_general {N : ℕ} (D : CongruentDissection N) (k : ℕ) (hk : 0 < k) :
    ∃ E : CongruentDissection (k * k * N), E.model = D.model ∧
      ∀ x y, dist (E.target.pts x) (E.target.pts y) = k * dist (D.target.pts x) (D.target.pts y) := by
  set T := D.target with hT
  have hind : AffineIndependent ℝ ![T.pts 0, T.pts 1, T.pts 2] := by
    have h : (![T.pts 0, T.pts 1, T.pts 2] : Fin 3 → Plane) = T.pts := by
      funext x; fin_cases x <;> rfl
    rw [h]; exact T.indep
  have hDt : D.target = (⟨![T.pts 0, T.pts 1, T.pts 2], hind⟩ : Tri) :=
    Tri.ext' (funext fun x => by fin_cases x <;> rfl)
  obtain ⟨E, hE1, hE2⟩ := Erdos634.Draft.LadderWrap.ladder_dissection (T.pts 0) (T.pts 1) (T.pts 2) hind D hDt k hk
  refine ⟨E, hE2, ?_⟩
  refine dist_all T E.target k ?_ ?_ ?_
  · rw [hE1, Erdos634.Subdivision.bigTri_pts0, Erdos634.Subdivision.bigTri_pts1, dist_P10]
  · rw [hE1, Erdos634.Subdivision.bigTri_pts0, Erdos634.Subdivision.bigTri_pts2, dist_P01]
  · rw [hE1, Erdos634.Subdivision.bigTri_pts1, Erdos634.Subdivision.bigTri_pts2, dist_P12]

/-! ### D. a laddered tile -/

/-- the one-tile dissection of a triangle by itself -/
noncomputable def oneTile (T : Tri) : CongruentDissection 1 where
  target := T
  tile := fun _ => T
  covers := by
    show (⋃ _ : Fin 1, T.carrier) = T.carrier
    exact Set.iUnion_const _
  interiors_disjoint := fun i j hij => absurd (Subsingleton.elim i j) hij
  model := T
  tiles_congruent := fun _ => Tri.Congruent.refl T

theorem piece_tile (K : Cfg) (k : ℕ) (hk : 0 < k) (U : Tri)
    (hU : ∀ x y, dist (U.pts x) (U.pts y) = (k : ℝ) * dist (K.T0.pts x) (K.T0.pts y)) :
    ∃ D : CongruentDissection (k * k * 1), D.target.carrier = U.carrier ∧ D.model.Congruent K.T0 := by
  obtain ⟨E, hE1, hE2⟩ := ladder_general (oneTile K.T0) k hk
  obtain ⟨D, hD1, hD2⟩ := transport_of_dist E U 1 one_pos (fun x y => by
    rw [hU, hE2, one_mul]; rfl)
  refine ⟨D, hD1, ?_⟩
  refine hD2.trans ?_
  rw [hE1]
  exact scaleTri_one_congr K.T0

/-! ### E. the blue (Cor 5) piece -/

set_option maxHeartbeats 1600000 in
theorem piece_blue (a b c : ℕ) (R : Erdos634.LaczL22.RTri) (hRa : R.a = (a : ℚ)) (hRb : R.b = (b : ℚ))
    (hRc : R.c = (c : ℚ)) (ha : 0 < a) (hb : 0 < b) (h : a * a + c * b = c * c) (K : Cfg)
    (hKb : K.b = (b : ℝ)) (hKc : K.c = (c : ℝ))
    (s : ℝ) (hs : 0 < s) {N0 : ℕ} (D : CongruentDissection N0)
    (hiso : dist (D.target.pts 2) (D.target.pts 0) = dist (D.target.pts 2) (D.target.pts 1))
    (hang : Erdos634.Geometry.cornerAngle (D.target.pts 0) (D.target.pts 2) (D.target.pts 1)
      = Erdos634.Geometry.cornerAngle (R.Δ.pts 1) (R.Δ.pts 0) (R.Δ.pts 2))
    (hmod : D.model.Congruent (scaleTri s hs.ne' R.Δ))
    (pp rr : ℕ) (hpp : 0 < pp) (hrr : 0 < rr)
    (hleg : dist (D.target.pts 2) (D.target.pts 0) * (rr : ℝ) = pp * s) (hKp : K.p = (pp : ℝ)) :
    ∃ D3 : CongruentDissection ((b * c * rr) * (b * c * rr) * N0),
      D3.target.carrier = K.T3.carrier ∧ D3.model.Congruent K.T0 := by
  have hcpos : 0 < c := by
    rcases Nat.eq_zero_or_pos c with h0 | h0
    · subst h0; simp at h; omega
    · exact h0
  have haR : (0 : ℝ) < a := Nat.cast_pos.mpr ha
  have hbR : (0 : ℝ) < b := Nat.cast_pos.mpr hb
  have hcR : (0 : ℝ) < c := Nat.cast_pos.mpr hcpos
  have hrrR : (0 : ℝ) < rr := Nat.cast_pos.mpr hrr
  have hppR : (0 : ℝ) < pp := Nat.cast_pos.mpr hpp
  have hhR : (a : ℝ) * a + c * b = c * c := by exact_mod_cast h
  have hR1 : dist (R.Δ.pts 1) (R.Δ.pts 0) = c := by rw [dist_comm, R.hc, hRc]; simp
  have hR2 : dist (R.Δ.pts 2) (R.Δ.pts 0) = b := by rw [R.hb, hRb]; simp
  have hR3 : dist (R.Δ.pts 1) (R.Δ.pts 2) = a := by rw [R.ha, hRa]; simp
  set l0 := dist (D.target.pts 2) (D.target.pts 0) with hl0
  have hne : D.target.pts 2 ≠ D.target.pts 0 := fun he => by
    have := D.target.indep.injective he; exact absurd this (by decide)
  have hl0pos : 0 < l0 := dist_pos.mpr hne
  have hd02 : dist (D.target.pts 0) (D.target.pts 2) = l0 := dist_comm _ _
  have hd12 : dist (D.target.pts 1) (D.target.pts 2) = l0 := by rw [dist_comm, ← hiso]
  set b0 := dist (D.target.pts 0) (D.target.pts 1) with hb0
  have c1 := Erdos634.AngleThreshold.cos_of_sides (D.target.pts 0) (D.target.pts 2) (D.target.pts 1)
    (by rw [hd02]; exact hl0pos.ne') (by rw [hd12]; exact hl0pos.ne')
  have c2 := Erdos634.AngleThreshold.cos_of_sides (R.Δ.pts 1) (R.Δ.pts 0) (R.Δ.pts 2)
    (by rw [hR1]; positivity) (by rw [hR2]; positivity)
  rw [hang, c2, hR1, hR2, hR3, hd02, hd12, ← hb0] at c1
  have ha2 : (a : ℝ) ^ 2 = c * c - c * b := by nlinarith
  have hb0sq : b0 ^ 2 = l0 ^ 2 * (a / c) ^ 2 := by
    field_simp at c1
    have hh2 : (a : ℝ) ^ 2 * l0 ^ 2 = (c * c - c * b) * l0 ^ 2 := by rw [ha2]
    have key : (b : ℝ) * (c * b0 ^ 2 - l0 ^ 2 * (c - b)) = 0 := by linear_combination c1 + hh2
    have h3 : (c : ℝ) * b0 ^ 2 = l0 ^ 2 * (c - b) := by
      rcases mul_eq_zero.mp key with h0 | h0
      · exact absurd h0 hbR.ne'
      · linarith
    rw [div_pow, ← mul_div_assoc, eq_div_iff (by positivity)]
    calc b0 ^ 2 * (c : ℝ) ^ 2 = c * (c * b0 ^ 2) := by ring
      _ = c * (l0 ^ 2 * (c - b)) := by rw [h3]
      _ = l0 ^ 2 * (a : ℝ) ^ 2 := by rw [ha2]; ring
  have hbase : b0 = l0 * (a / c) :=
    Cfg.sqeq dist_nonneg (by positivity) (by rw [hb0sq]; ring)
  -- ladder
  obtain ⟨E, hE1, hE2⟩ := ladder_general D (b * c * rr) (by positivity)
  have hu : (b * c * rr : ℝ) * l0 = b * c * pp * s := by
    have := hleg
    calc (b * c * rr : ℝ) * l0 = b * c * (l0 * rr) := by ring
      _ = _ := by rw [this]; ring
  -- distances of T3
  have hT01 : dist (K.T3.pts 0) (K.T3.pts 1) = a * b * pp := by
    refine Cfg.sqeq dist_nonneg (by positivity) ?_
    rw [K.T3_01, hKb, hKc, hKp]
    nlinarith [hhR]
  have hT02 : dist (K.T3.pts 0) (K.T3.pts 2) = b * c * pp := by
    refine Cfg.sqeq dist_nonneg (by positivity) ?_
    rw [K.T3_02, hKb, hKc, hKp]
  have hT12 : dist (K.T3.pts 1) (K.T3.pts 2) = b * c * pp := by
    refine Cfg.sqeq dist_nonneg (by positivity) ?_
    rw [K.T3_12, hKb, hKc, hKp]
  have hsne : s ≠ 0 := hs.ne'
  have hv : (1 / s) * ((b : ℝ) * c * rr * l0) = b * c * pp := by
    rw [one_div, inv_mul_eq_iff_eq_mul₀ hsne]; linarith [hu]
  have hall := dist_all E.target K.T3 (1 / s) ?_ ?_ ?_
  rotate_left
  · rw [hT01, hE2, ← hb0, hbase]
    push_cast
    have : (1 / s) * ((b : ℝ) * c * rr * (l0 * (a / c))) = ((1 / s) * ((b : ℝ) * c * rr * l0)) * (a / c) := by ring
    rw [this, hv]; field_simp
  · rw [hT02, hE2, hd02]
    push_cast
    exact hv.symm
  · rw [hT12, hE2, hd12]
    push_cast
    exact hv.symm
  obtain ⟨D3, hD1, hD2⟩ := transport_of_dist E K.T3 (1 / s) (by positivity) hall
  refine ⟨D3, hD1, ?_⟩
  -- the model
  have m1 : D3.model.Congruent (scaleTri (1 / s) (by positivity) (scaleTri s hs.ne' R.Δ)) := by
    refine hD2.trans ?_
    rw [hE1]
    exact scaleTri_congr _ _ hmod
  rw [Erdos634.Realizable.scaleTri_scaleTri _ _ (by positivity) hs.ne' (by positivity)] at m1
  have e1 : ∀ (x : ℝ) (hx : x ≠ 0), x = 1 → scaleTri x hx R.Δ = scaleTri 1 one_ne_zero R.Δ := by
    rintro x hx rfl; rfl
  rw [e1 _ _ (by field_simp)] at m1
  refine m1.trans ?_
  refine (Erdos634.LaczL22.congr_of_sq3 K.T0 R.Δ 1 1 one_pos ?_ ?_ ?_).symm
  · have : dist (R.Δ.pts ((1 : Equiv.Perm (Fin 3)) 0)) (R.Δ.pts ((1 : Equiv.Perm (Fin 3)) 1)) = c := by
      simp [R.hc, hRc]
    rw [this, K.T0_01, hKc]; ring
  · have : dist (R.Δ.pts ((1 : Equiv.Perm (Fin 3)) 1)) (R.Δ.pts ((1 : Equiv.Perm (Fin 3)) 2)) = a := by
      simp [R.ha, hRa]
    rw [this, K.T0_12, hKc, hKb]; nlinarith [hhR]
  · have : dist (R.Δ.pts ((1 : Equiv.Perm (Fin 3)) 2)) (R.Δ.pts ((1 : Equiv.Perm (Fin 3)) 0)) = b := by
      simp [R.hb, hRb]
    rw [this, dist_comm, K.T0_02, hKb]; ring


/-! ### F. gluing the three pieces -/

/-- re-model a congruent dissection to the common model `T0` -/
noncomputable def remodel (K : Cfg) {N : ℕ} (D : CongruentDissection N) (hm : D.model.Congruent K.T0) :
    CongruentRegionDissection N :=
  { D.toRegion with
    model := K.T0
    tiles_congruent := fun i => (D.tiles_congruent i).trans hm }

theorem remodel_region (K : Cfg) {N : ℕ} (D : CongruentDissection N) (hm : D.model.Congruent K.T0) :
    (remodel K D hm).region = D.target.carrier := rfl

theorem assemble (K : Cfg) {N1 N2 N3 : ℕ} (D1 : CongruentDissection N1) (D2 : CongruentDissection N2)
    (D3 : CongruentDissection N3) (h1 : D1.target.carrier = K.T1.carrier) (h2 : D2.target.carrier = K.T2.carrier)
    (h3 : D3.target.carrier = K.T3.carrier) (m1 : D1.model.Congruent K.T0) (m2 : D2.model.Congruent K.T0)
    (m3 : D3.model.Congruent K.T0) :
    ∃ E : CongruentDissection (N1 + (N2 + N3)), E.target = K.TT ∧ E.model = K.T0 := by
  set C1 := remodel K D1 m1
  set C2 := remodel K D2 m2
  set C3 := remodel K D3 m3
  have d23 : Disjoint (interior C2.region) (interior C3.region) := by
    show Disjoint (interior D2.target.carrier) (interior D3.target.carrier)
    rw [h2, h3]; exact K.disj_23
  set C23 := unionCongruentRegion C2 C3 rfl d23
  have d1 : Disjoint (interior C1.region) (interior C23.region) := by
    show Disjoint (interior D1.target.carrier) (interior (D2.target.carrier ∪ D3.target.carrier))
    rw [h1, h2, h3]; exact K.disj_1_23
  set C := unionCongruentRegion C1 C23 rfl d1
  have hreg : C.region = K.TT.carrier := by
    show D1.target.carrier ∪ (D2.target.carrier ∪ D3.target.carrier) = _
    rw [h1, h2, h3]; exact K.cover
  exact ⟨C.toCongruentDissection K.TT hreg, rfl, rfl⟩

/-! ### G. the construction of the configuration from `(a,b,c)` -/

theorem cfg_exists (b c : ℕ) (hb : 0 < b) (hbc : b < c) :
    ∃ K : Cfg, K.b = (b : ℝ) ∧ K.c = (c : ℝ) := by
  have hbR : (0 : ℝ) < b := Nat.cast_pos.mpr hb
  have hcR : (0 : ℝ) < c := by exact_mod_cast (by omega : 0 < c)
  have hbcR : (b : ℝ) < c := by exact_mod_cast hbc
  set w : ℝ := b * (b + c) / (2 * c) with hw
  have hw0 : 0 < w := by positivity
  have hwb : w < b := by
    rw [hw, div_lt_iff₀ (by positivity)]; nlinarith
  have hpos : 0 < (b : ℝ) ^ 2 - w ^ 2 := by nlinarith
  refine ⟨⟨b, c, 1, w, Real.sqrt ((b : ℝ) ^ 2 - w ^ 2), hbR, hcR, one_pos, Real.sqrt_pos.mpr hpos, ?_, ?_⟩, rfl, rfl⟩
  · rw [hw]; field_simp
  · rw [Real.sq_sqrt hpos.le]; ring

set_option maxHeartbeats 1600000 in
/-- **Beeson Corollary 6 (existence, count and triangle).**  `a^2 + c b = c^2`, `gcd(a,b,c) = 1`: for some `L >= 1`
a triangle with sides `L c^2`, `L b (b+2c)`, `L c (b+c)` (angles `(2 alpha, alpha, 2 beta)`) is dissected into
`L^2 (b+c)(b+2c)` copies of the tile `(a,b,c)`.  (`M = L (b+c-a)` is the colouring parameter, Beeson Thm 1 / Thm 15,
NOT proved here.) -/
theorem cor6_exists (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (h : a * a + c * b = c * c)
    (hg : Nat.gcd (Nat.gcd a b) c = 1) :
    ∃ L : ℕ, 0 < L ∧ ∃ (T : Tri) (E : CongruentDissection (L * L * ((b + c) * (b + 2 * c)))),
      E.model = T ∧ dist (T.pts 0) (T.pts 1) ^ 2 = (c : ℝ) ^ 2 ∧ dist (T.pts 0) (T.pts 2) ^ 2 = (b : ℝ) ^ 2 ∧
      dist (T.pts 1) (T.pts 2) ^ 2 = (a : ℝ) ^ 2 ∧
      dist (E.target.pts 0) (E.target.pts 1) ^ 2 = ((L * c ^ 2 : ℕ) : ℝ) ^ 2 ∧
      dist (E.target.pts 0) (E.target.pts 2) ^ 2 = ((L * b * (b + 2 * c) : ℕ) : ℝ) ^ 2 ∧
      dist (E.target.pts 1) (E.target.pts 2) ^ 2 = ((L * c * (b + c) : ℕ) : ℝ) ^ 2 := by
  have hcpos : 0 < c := by
    rcases Nat.eq_zero_or_pos c with h0 | h0
    · subst h0; simp at h; omega
    · exact h0
  have hbc : b < c := by
    by_contra hcon
    push_neg at hcon
    have : c * c ≤ c * b := Nat.mul_le_mul_left c hcon
    nlinarith
  have hhR : (a : ℝ) * a + c * b = c * c := by exact_mod_cast h
  obtain ⟨K0, hK0b, hK0c⟩ := cfg_exists b c hb hbc
  have hbR : (0 : ℝ) < b := Nat.cast_pos.mpr hb
  have haR : (0 : ℝ) < a := Nat.cast_pos.mpr ha
  have hcR : (0 : ℝ) < c := Nat.cast_pos.mpr hcpos
  have ha2 : dist (K0.T0.pts 1) (K0.T0.pts 2) = (a : ℝ) :=
    Cfg.sqeq dist_nonneg haR.le (by rw [K0.T0_12, hK0b, hK0c]; nlinarith [hhR])
  have hb2 : dist (K0.T0.pts 2) (K0.T0.pts 0) = (b : ℝ) :=
    Cfg.sqeq dist_nonneg hbR.le (by rw [dist_comm, K0.T0_02, hK0b])
  have hc2 : dist (K0.T0.pts 0) (K0.T0.pts 1) = (c : ℝ) :=
    Cfg.sqeq dist_nonneg hcR.le (by rw [K0.T0_01, hK0c])
  let R : Erdos634.LaczL22.RTri := ⟨K0.T0, a, b, c, by rw [ha2]; simp, by rw [hb2]; simp, by rw [hc2]; simp,
    by exact_mod_cast ha, by exact_mod_cast hb, by exact_mod_cast hcpos⟩
  have hRa : R.a = (a : ℚ) := rfl
  have hRb : R.b = (b : ℚ) := rfl
  have hRc : R.c = (c : ℚ) := rfl
  obtain ⟨s, hs, N0, D, hiso, hang, hmod, pp, rr, hpp, hrr, hleg⟩ :=
    Erdos634.BeesonCor5Legs.cor5_legs a b c ha hb h hg R hRa hRb hRc
  have hppR : (0 : ℝ) < pp := Nat.cast_pos.mpr hpp
  let K : Cfg := { K0 with p := (pp : ℝ), hp := hppR }
  have hKb : K.b = (b : ℝ) := hK0b
  have hKc : K.c = (c : ℝ) := hK0c
  have hKp : K.p = (pp : ℝ) := rfl
  have hk1 : 0 < (b + c) * pp := by positivity
  have hk2 : 0 < c * pp := by positivity
  obtain ⟨D1, hD11, hD12⟩ := piece_tile K ((b + c) * pp) hk1 K.T1 (by
    have e : (((b + c) * pp : ℕ) : ℝ) = (K.b + K.c) * K.p := by rw [hKb, hKc, hKp]; push_cast; ring
    rw [e]; exact K.T1_dist)
  obtain ⟨D2, hD21, hD22⟩ := piece_tile K (c * pp) hk2 K.T2 (by
    have e : ((c * pp : ℕ) : ℝ) = K.c * K.p := by rw [hKc, hKp]; push_cast; ring
    rw [e]; exact K.T2_dist)
  obtain ⟨D3, hD31, hD32⟩ := piece_blue a b c R hRa hRb hRc ha hb h K hKb hKc s hs D hiso hang hmod pp rr hpp hrr
    hleg hKp
  obtain ⟨E, hE1, hE2⟩ := assemble K D1 D2 D3 hD11 hD21 hD31 hD12 hD22 hD32
  -- the count of the blue part, by area
  have hv0 : volume K.T0.carrier ≠ 0 := by
    rw [K.vol_T0]; exact (ENNReal.ofReal_pos.mpr (by have := K.ch_pos; positivity)).ne'
  have hvt : volume K.T0.carrier ≠ ⊤ := by rw [K.vol_T0]; exact ENNReal.ofReal_ne_top
  have hvol := Erdos634.CongruentArea.congruentDissection_volume_target D3
  rw [hD31, Erdos634.CongruentArea.volume_congruent hD32, K.vol_T3_eq] at hvol
  have hN3 : (b * c * rr) * (b * c * rr) * N0 = b * c * pp * pp := by
    have h1 := (ENNReal.mul_left_inj hv0 hvt).mp hvol
    have h2 : ENNReal.ofReal (K.b * K.c * K.p ^ 2) = ((b * c * pp * pp : ℕ) : ENNReal) := by
      rw [← ENNReal.ofReal_natCast]; congr 1; rw [hKb, hKc, hKp]; push_cast; ring
    rw [h2] at h1
    exact_mod_cast h1.symm
  have hN : (b + c) * pp * ((b + c) * pp) * 1 + (c * pp * (c * pp) * 1 + (b * c * rr * (b * c * rr) * N0))
      = pp * pp * ((b + c) * (b + 2 * c)) := by
    rw [hN3]; ring
  obtain ⟨E', hE'1, hE'2⟩ : ∃ E' : CongruentDissection (pp * pp * ((b + c) * (b + 2 * c))),
      E'.target = E.target ∧ E'.model = E.model := by
    rw [← hN]; exact ⟨E, rfl, rfl⟩
  refine ⟨pp, hpp, K.T0, E', ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hE'2, hE2]
  · rw [K.T0_01, hKc]
  · rw [K.T0_02, hKb]
  · rw [K.T0_12, hKc, hKb]; nlinarith [hhR]
  · rw [hE'1, hE1, K.TT_01, hKc, hKp]; push_cast; ring
  · rw [hE'1, hE1, K.TT_02, hKb, hKc, hKp]; push_cast; ring
  · rw [hE'1, hE1, K.TT_12, hKb, hKc, hKp]; push_cast; ring


/-- The conclusion of `cor6_exists`, as a predicate on the tile `(a,b,c)`. -/
def Cor6Concl (a b c : ℕ) : Prop :=
  ∃ L : ℕ, 0 < L ∧ ∃ (T : Tri) (E : CongruentDissection (L * L * ((b + c) * (b + 2 * c)))),
    E.model = T ∧ dist (T.pts 0) (T.pts 1) ^ 2 = (c : ℝ) ^ 2 ∧ dist (T.pts 0) (T.pts 2) ^ 2 = (b : ℝ) ^ 2 ∧
    dist (T.pts 1) (T.pts 2) ^ 2 = (a : ℝ) ^ 2 ∧
    dist (E.target.pts 0) (E.target.pts 1) ^ 2 = ((L * c ^ 2 : ℕ) : ℝ) ^ 2 ∧
    dist (E.target.pts 0) (E.target.pts 2) ^ 2 = ((L * b * (b + 2 * c) : ℕ) : ℝ) ^ 2 ∧
    dist (E.target.pts 1) (E.target.pts 2) ^ 2 = ((L * c * (b + c) : ℕ) : ℝ) ^ 2

/-! ### H. Witnesses: every hypothesis of `cor6_exists` holds, including a tile with `c >= 2b` -/

theorem cor6_wit_234 : Cor6Concl 2 3 4 :=
  cor6_exists 2 3 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem cor6_wit_389 : Cor6Concl 3 8 9 :=
  cor6_exists 3 8 9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem cor6_wit_659 : Cor6Concl 6 5 9 :=
  cor6_exists 6 5 9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- `(12,7,16)`: `c = 16 >= 2b = 14`, outside Beeson Thm 14/15's range `c < 2b`; `N = L^2 * 23 * 39`. -/
theorem cor6_wit_12716 : Cor6Concl 12 7 16 :=
  cor6_exists 12 7 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem cor6_count_12716 : ∃ L : ℕ, 0 < L ∧ ∃ N : ℕ, N = L * L * 897 ∧ ∃ (_ : CongruentDissection N), True := by
  obtain ⟨L, hL, T, E, -⟩ := cor6_wit_12716
  exact ⟨L, hL, _, by ring, E, trivial⟩

/-! ### I. Corollary 7 ("if" direction) and T-C9 ("if" direction) -/

theorem coprime_tile (u v : ℕ) (hu : 0 < u) (huv : u < v) (hcop : Nat.Coprime u v) :
    0 < u * v ∧ 0 < v * v - u * u ∧
      (u * v) * (u * v) + (v * v) * (v * v - u * u) = (v * v) * (v * v) ∧
      Nat.gcd (Nat.gcd (u * v) (v * v - u * u)) (v * v) = 1 := by
  have hle : u * u ≤ v * v := Nat.mul_le_mul huv.le huv.le
  have hlt : u * u < v * v := Nat.mul_lt_mul'' huv huv
  refine ⟨Nat.mul_pos hu (by omega), by omega, ?_, ?_⟩
  · zify [hle]; ring
  · set d := Nat.gcd (Nat.gcd (u * v) (v * v - u * u)) (v * v) with hd
    have hd2 : d ∣ v * v := Nat.gcd_dvd_right _ _
    have hd1 : d ∣ v * v - u * u := (Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_right _ _)
    have hd3 : d ∣ u * u := by
      have := Nat.dvd_sub hd2 hd1
      rwa [Nat.sub_sub_self hle] at this
    have hc : Nat.Coprime (u * u) (v * v) := Nat.Coprime.mul_left (Nat.Coprime.mul_right hcop hcop) (Nat.Coprime.mul_right hcop hcop)
    exact Nat.eq_one_of_dvd_one (hc.gcd_eq_one ▸ Nat.dvd_gcd hd3 hd2)

/-- **Cor 7, "if" direction** (in the form of the tile data): `s = a/c = u/v` rational in lowest terms, `0 < u < v`; the
tile is `(a,b,c) = (u v, v^2 - u^2, v^2)` (`a^2 + c b = c^2`, `gcd = 1`); then the `(2 alpha, alpha, 2 beta)` triangle is
tiled by it (`N = L^2 (b+c)(b+2c)`).  The "only if" direction (Beeson Thm 15, `s` rational) is NOT proved here. -/
theorem cor7_if (u v : ℕ) (hu : 0 < u) (huv : u < v) (hcop : Nat.Coprime u v) :
    Cor6Concl (u * v) (v * v - u * u) (v * v) := by
  obtain ⟨h1, h2, h3, h4⟩ := coprime_tile u v hu huv hcop
  exact cor6_exists _ _ _ h1 h2 h3 h4

/-- `s = 3/4`: tile `(12,7,16)` -/
theorem cor7_wit_34 : Cor6Concl (3 * 4) (4 * 4 - 3 * 3) (4 * 4) :=
  cor7_if 3 4 (by norm_num) (by norm_num) (by norm_num)

/-- a real tile with sides `a,b,c` for any natural data with `a^2 + c b = c^2` (not only Beeson's Thm 24 range) -/
theorem exists_RTri_of_nat (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (h : a * a + c * b = c * c) :
    ∃ R : Erdos634.LaczL22.RTri, R.a = (a : ℚ) ∧ R.b = (b : ℚ) ∧ R.c = (c : ℚ) := by
  have hcpos : 0 < c := by
    rcases Nat.eq_zero_or_pos c with h0 | h0
    · subst h0; simp at h; omega
    · exact h0
  have hbc : b < c := by
    by_contra hcon
    push_neg at hcon
    have : c * c ≤ c * b := Nat.mul_le_mul_left c hcon
    nlinarith
  have hhR : (a : ℝ) * a + c * b = c * c := by exact_mod_cast h
  obtain ⟨K0, hK0b, hK0c⟩ := cfg_exists b c hb hbc
  have hbR : (0 : ℝ) < b := Nat.cast_pos.mpr hb
  have haR : (0 : ℝ) < a := Nat.cast_pos.mpr ha
  have hcR : (0 : ℝ) < c := Nat.cast_pos.mpr hcpos
  have ha2 : dist (K0.T0.pts 1) (K0.T0.pts 2) = (a : ℝ) :=
    Cfg.sqeq dist_nonneg haR.le (by rw [K0.T0_12, hK0b, hK0c]; nlinarith [hhR])
  have hb2 : dist (K0.T0.pts 2) (K0.T0.pts 0) = (b : ℝ) :=
    Cfg.sqeq dist_nonneg hbR.le (by rw [dist_comm, K0.T0_02, hK0b])
  have hc2 : dist (K0.T0.pts 0) (K0.T0.pts 1) = (c : ℝ) :=
    Cfg.sqeq dist_nonneg hcR.le (by rw [K0.T0_01, hK0c])
  exact ⟨⟨K0.T0, a, b, c, by rw [ha2]; simp, by rw [hb2]; simp, by rw [hc2]; simp,
    by exact_mod_cast ha, by exact_mod_cast hb, by exact_mod_cast hcpos⟩, rfl, rfl, rfl⟩

/-- **T-C9, "if" direction**: for rational `s = u/v` (tile `(u v, v^2 - u^2, v^2)`), Cor 5's isosceles triangle with base
angles `alpha + beta` is tiled (by similar copies, scale `s'`).  Instance of `cor5` with the real tile from
`exists_RTri_of_nat`.  The "only if" (Thm 15) is NOT proved here. -/
theorem tc9_if (u v : ℕ) (hu : 0 < u) (huv : u < v) (hcop : Nat.Coprime u v) :
    ∃ R : Erdos634.LaczL22.RTri, R.a = ((u * v : ℕ) : ℚ) ∧ R.b = ((v * v - u * u : ℕ) : ℚ) ∧
      R.c = ((v * v : ℕ) : ℚ) ∧
      ∃ (s : ℝ) (hs : 0 < s) (N : ℕ) (D : CongruentDissection N),
        dist (D.target.pts 2) (D.target.pts 0) = dist (D.target.pts 2) (D.target.pts 1) ∧
        Erdos634.Geometry.cornerAngle (D.target.pts 0) (D.target.pts 2) (D.target.pts 1)
          = Erdos634.Geometry.cornerAngle (R.Δ.pts 1) (R.Δ.pts 0) (R.Δ.pts 2) ∧
        D.model.Congruent (scaleTri s hs.ne' R.Δ) := by
  obtain ⟨h1, h2, h3, h4⟩ := coprime_tile u v hu huv hcop
  obtain ⟨R, hRa, hRb, hRc⟩ := exists_RTri_of_nat _ _ _ h1 h2 h3
  exact ⟨R, hRa, hRb, hRc, Erdos634.BeesonCor5.cor5 _ _ _ h1 h2 h3 h4 R hRa hRb hRc⟩

#print axioms cor6_exists
#print axioms cor6_wit_12716
#print axioms cor7_if
#print axioms tc9_if

end Erdos634.BeesonCor6
