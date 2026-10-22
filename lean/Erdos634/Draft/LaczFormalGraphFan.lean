-- Draft/LaczFormalGraphFan.lean -- D0 (part 1), pure plane geometry: the CYCLIC FAN of a covering family of angular sectors.
--
-- SETTING.  A *sector* is a pair of generators `(p, q)` of vectors in the plane, `p` = clockwise ray, `q` = counterclockwise ray,
-- with width in `(0, pi]`: `0 < cross p q`, or `cross p q = 0` and `dot p q < 0` (a straight sector = half-plane).  Its closed cone is
-- `{z | 0 <= cross p z, 0 <= cross z q}` and its open cone the same with strict inequalities.  A finite family of sectors COVERS the
-- plane when every `z` lies in some closed cone, and is DISJOINT when open cones of distinct members do not meet.
--
-- MAIN RESULTS (no tiling is mentioned; this is the local linear-algebra heart of "the star of tiles around a vertex is an ordered fan"):
--  * `succ_exists`      every sector `s` has a successor sector `t` whose clockwise ray is the positive multiple of the ccw ray of `s`;
--  * `end_inj`          two distinct sectors do not end on the same ray (so the successor map is injective, hence a permutation);
--  * `fan_cycle`        if moreover the widths (= `Complex.arg` of the Hermitian product, i.e. the unoriented angle) add up to `2 pi`,
--                       the successor permutation is ONE cycle through all sectors: the sectors are `s_0, .., s_{k-1}` in counterclockwise
--                       order with `q s_i ~ p s_{i+1}` (indices mod k).
-- UNAUDITED (label NOTE).  Credit: Laczkovich (DCG 48 (2012), Sect. 4: the half-lines h_0..h_n and the triangles T_i in the angular
-- domains between them; Combinatorica 10 (1990)); Beeson (arXiv 1206.2229, 1206.1974: vertex figures); Beeson-Zhang (2604.01314).
import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Complex.Log

namespace Erdos634.Draft.LaczFormal.Graph

/-- Plane vectors as pairs of reals (the instantiation to `EuclideanSpace` takes coordinates 0, 1). -/
abbrev V2 : Type := ℝ × ℝ

def crs (u v : V2) : ℝ := u.1 * v.2 - u.2 * v.1
def dt (u v : V2) : ℝ := u.1 * v.1 + u.2 * v.2
def nsq (u : V2) : ℝ := u.1 ^ 2 + u.2 ^ 2

/-- Admissible sector: width in `(0, pi]`. -/
def SecOK (p q : V2) : Prop := 0 < crs p q ∨ (crs p q = 0 ∧ dt p q < 0)
/-- Closed cone of the sector. -/
def inCone (p q z : V2) : Prop := 0 ≤ crs p z ∧ 0 ≤ crs z q
/-- Open cone of the sector. -/
def inInt (p q z : V2) : Prop := 0 < crs p z ∧ 0 < crs z q
/-- `u` is a positive multiple of `v` (both nonzero). -/
def Par (u v : V2) : Prop := crs u v = 0 ∧ 0 < dt u v

/-! ## Elementary identities -/

theorem nsq_nonneg (u : V2) : 0 ≤ nsq u := by unfold nsq; positivity

theorem nsq_pos {u : V2} (h : u ≠ 0) : 0 < nsq u := by
  unfold nsq
  rcases lt_or_ge 0 (u.1 ^ 2 + u.2 ^ 2) with h1 | h1
  · exact h1
  · exfalso; apply h
    have h1' : u.1 ^ 2 + u.2 ^ 2 = 0 := le_antisymm h1 (by positivity)
    have : u.1 = 0 := by nlinarith [sq_nonneg u.1, sq_nonneg u.2]
    have h2 : u.2 = 0 := by nlinarith [sq_nonneg u.1, sq_nonneg u.2]
    exact Prod.ext this h2

theorem crs_dt_sq (u v : V2) : crs u v ^ 2 + dt u v ^ 2 = nsq u * nsq v := by
  unfold crs dt nsq; ring

theorem id_crs (p q r : V2) : nsq q * crs p r = dt q r * crs p q + crs q r * dt p q := by
  unfold crs dt nsq; ring

theorem id_dt (p q r : V2) : nsq q * dt p r = dt p q * dt q r - crs p q * crs q r := by
  unfold crs dt nsq; ring

theorem SecOK.ne_p {p q : V2} (h : SecOK p q) : p ≠ 0 := by
  rintro rfl
  unfold SecOK crs dt at h
  simp at h

theorem SecOK.ne_q {p q : V2} (h : SecOK p q) : q ≠ 0 := by
  rintro rfl
  unfold SecOK crs dt at h
  simp at h

/-- A nonzero `u` with `crs u v = dt u v = 0` is impossible for nonzero `v`. -/
theorem eq_zero_of_crs_dt {u v : V2} (hv : v ≠ 0) (h1 : crs u v = 0) (h2 : dt u v = 0) : u = 0 := by
  have := crs_dt_sq u v
  rw [h1, h2] at this
  have hn : nsq u * nsq v = 0 := by linarith
  rcases mul_eq_zero.mp hn with h | h
  · by_contra hu
    exact absurd h (nsq_pos hu).ne'
  · exact absurd h (nsq_pos hv).ne'

theorem Par.ne_left {u v : V2} (h : Par u v) : u ≠ 0 := by
  rintro rfl; unfold Par dt at h; simp at h

theorem Par.ne_right {u v : V2} (h : Par u v) : v ≠ 0 := by
  rintro rfl; unfold Par dt at h; simp at h

theorem Par.symm {u v : V2} (h : Par u v) : Par v u := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, ?_⟩
  · unfold crs at h1 ⊢; linarith
  · unfold dt at h2 ⊢; linarith

theorem Par.trans {u v w : V2} (h1 : Par u v) (h2 : Par v w) : Par u w := by
  have hv : 0 < nsq v := nsq_pos h1.ne_right
  obtain ⟨c1, d1⟩ := h1
  obtain ⟨c2, d2⟩ := h2
  have e1 := id_crs u v w
  have e2 := id_dt u v w
  refine ⟨?_, ?_⟩
  · have : nsq v * crs u w = 0 := by rw [e1, c1, c2]; ring
    exact (mul_eq_zero.mp this).resolve_left hv.ne'
  · have : nsq v * dt u w = dt u v * dt v w := by rw [e2, c1]; ring
    have hpos : 0 < nsq v * dt u w := by rw [this]; exact mul_pos d1 d2
    exact (mul_pos_iff_of_pos_left hv).mp hpos

theorem Par.smul {u v : V2} (h : Par u v) : ∃ c : ℝ, 0 < c ∧ u = (c * v.1, c * v.2) := by
  have hv : 0 < nsq v := nsq_pos h.ne_right
  refine ⟨dt u v / nsq v, div_pos h.2 hv, ?_⟩
  have h0 : u.1 * v.2 - u.2 * v.1 = 0 := h.1
  ext
  · show u.1 = (dt u v / nsq v) * v.1
    rw [div_mul_eq_mul_div, eq_div_iff hv.ne']
    unfold dt nsq; linear_combination v.2 * h0
  · show u.2 = (dt u v / nsq v) * v.2
    rw [div_mul_eq_mul_div, eq_div_iff hv.ne']
    unfold dt nsq; linear_combination (-v.1) * h0

theorem smul_par {u v : V2} {c : ℝ} (hc : 0 < c) (hv : v ≠ 0) (h : u = (c * v.1, c * v.2)) : Par u v := by
  subst h
  refine ⟨?_, ?_⟩
  · unfold crs; ring
  · unfold dt
    have := nsq_pos hv
    unfold nsq at this
    nlinarith [mul_pos hc this]

theorem inInt_smul {p q z : V2} {c : ℝ} (hc : 0 < c) (h : inInt p q z) :
    inInt p q (c * z.1, c * z.2) := by
  unfold inInt crs at *
  constructor <;> nlinarith [h.1, h.2]

theorem inInt_smul_iff {p q z : V2} {c : ℝ} (hc : 0 < c) :
    inInt p q (c * z.1, c * z.2) ↔ inInt p q z := by
  refine ⟨fun h => ?_, inInt_smul hc⟩
  have := inInt_smul (inv_pos.mpr hc) h
  have e : ((c⁻¹ * (c * z.1), c⁻¹ * (c * z.2)) : V2) = z := by
    ext <;> simp <;> field_simp
  simpa [e] using this

/-! ## Perturbing along a ray -/

theorem affine_pos_small (A B : ℝ) (hA : 0 < A) : ∃ δ > 0, ∀ ε : ℝ, 0 < ε → ε < δ → 0 < A + ε * B := by
  refine ⟨A / (|B| + 1), by positivity, fun ε hε hεδ => ?_⟩
  have h1 : ε * (|B| + 1) < A := by
    have := (lt_div_iff₀ (by positivity : (0:ℝ) < |B| + 1)).mp hεδ
    linarith
  have h2 : -(ε * |B|) ≤ ε * B := by
    have := neg_abs_le B
    nlinarith
  nlinarith [abs_nonneg B]

/-- Slightly counterclockwise of the ray `q`. -/
def zplus (q : V2) (ε : ℝ) : V2 := (q.1 - ε * q.2, q.2 + ε * q.1)
/-- Slightly clockwise of the ray `q`. -/
def zminus (q : V2) (ε : ℝ) : V2 := (q.1 + ε * q.2, q.2 - ε * q.1)

/-- Just before the end ray `q` of a sector one is in its open cone. -/
theorem minus_ray_int {p q : V2} (hs : SecOK p q) :
    ∃ δ > 0, ∀ ε : ℝ, 0 < ε → ε < δ → inInt p q (zminus q ε) := by
  have hq := nsq_pos hs.ne_q
  have e1 : ∀ ε, crs p (zminus q ε) = crs p q - ε * dt p q := by
    intro ε; unfold crs dt zminus; ring
  have e2 : ∀ ε, crs (zminus q ε) q = ε * nsq q := by
    intro ε; unfold crs zminus nsq; ring
  rcases hs with h | ⟨h0, hd⟩
  · obtain ⟨δ, hδ, H⟩ := affine_pos_small (crs p q) (-(dt p q)) h
    refine ⟨δ, hδ, fun ε hε hεδ => ⟨?_, ?_⟩⟩
    · rw [e1]; have := H ε hε hεδ; linarith
    · rw [e2]; positivity
  · refine ⟨1, one_pos, fun ε hε _ => ⟨?_, ?_⟩⟩
    · rw [e1, h0]; nlinarith
    · rw [e2]; positivity

/-- A point of the open cone stays in the open cone when moved slightly clockwise. -/
theorem minus_ray_int_of_int {p q r : V2} (h1 : 0 < crs p r) (h2 : 0 < crs r q) :
    ∃ δ > 0, ∀ ε : ℝ, 0 < ε → ε < δ → inInt p q (zminus r ε) := by
  have e1 : ∀ ε, crs p (zminus r ε) = crs p r + ε * (-(dt p r)) := by
    intro ε; unfold crs dt zminus; ring
  have e2 : ∀ ε, crs (zminus r ε) q = crs r q + ε * dt r q := by
    intro ε; unfold crs dt zminus; ring
  obtain ⟨d1, hd1, H1⟩ := affine_pos_small (crs p r) (-(dt p r)) h1
  obtain ⟨d2, hd2, H2⟩ := affine_pos_small (crs r q) (dt r q) h2
  refine ⟨min d1 d2, lt_min hd1 hd2, fun ε hε hεδ => ⟨?_, ?_⟩⟩
  · rw [e1]; exact H1 ε hε (lt_of_lt_of_le hεδ (min_le_left _ _))
  · rw [e2]; exact H2 ε hε (lt_of_lt_of_le hεδ (min_le_right _ _))

/-! ## The end ray of a sector is the start ray of a successor -/

theorem affine_limit (A B : ℝ) (h : ∀ N : ℕ, ∃ n : ℕ, N < n ∧ 0 ≤ A + (1 / ((n : ℝ) + 1)) * B) : 0 ≤ A := by
  by_contra hA
  push_neg at hA
  obtain ⟨N, hN⟩ := exists_nat_gt (|B| / (-A))
  obtain ⟨n, hnN, hn⟩ := h N
  have hn1 : (N : ℝ) < n := by exact_mod_cast hnN
  have hpos : (0 : ℝ) < n + 1 := by positivity
  have h1 : |B| / (-A) < (n : ℝ) + 1 := by linarith
  have h2 : |B| < ((n : ℝ) + 1) * (-A) := by
    have := (div_lt_iff₀ (by linarith : (0:ℝ) < -A)).mp h1
    linarith
  have h3 : (1 / ((n : ℝ) + 1)) * B ≤ (1 / ((n : ℝ) + 1)) * |B| :=
    mul_le_mul_of_nonneg_left (le_abs_self B) (by positivity)
  have h4 : (1 / ((n : ℝ) + 1)) * |B| < -A := by
    rw [one_div, inv_mul_lt_iff₀ hpos]; linarith
  linarith

theorem affine_interval {A B ε0 : ℝ} (hA : 0 ≤ A) (h0 : 0 ≤ A + ε0 * B) (hε0 : 0 < ε0) :
    ∀ ε : ℝ, 0 < ε → ε ≤ ε0 → 0 ≤ A + ε * B := by
  intro ε hε hle
  rcases le_total 0 B with hB | hB
  · nlinarith
  · nlinarith

section Family

variable {ι : Type*} [Fintype ι] (p q : ι → V2)

/-- The family covers the plane. -/
def Covers : Prop := ∀ z : V2, ∃ s, inCone (p s) (q s) z
/-- Open cones of distinct members are disjoint. -/
def Disjoint' : Prop := ∀ s t, s ≠ t → ∀ z, ¬ (inInt (p s) (q s) z ∧ inInt (p t) (q t) z)
/-- All members are admissible sectors. -/
def AllOK : Prop := ∀ s, SecOK (p s) (q s)

theorem end_cover (hcov : Covers p q) (r : V2) :
    ∃ t, ∃ δ > 0, 0 ≤ crs (p t) r ∧ 0 ≤ crs r (q t) ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ δ → inCone (p t) (q t) (zplus r ε) := by
  classical
  choose s hs using fun n : ℕ => hcov (zplus r (1 / ((n : ℝ) + 1)))
  haveI : Nonempty ι := ⟨s 0⟩
  obtain ⟨t, ht⟩ := Finite.exists_infinite_fiber s
  have hinf : (s ⁻¹' {t}).Infinite := Set.infinite_coe_iff.mp ht
  have hmem : ∀ N : ℕ, ∃ n : ℕ, N < n ∧ inCone (p t) (q t) (zplus r (1 / ((n : ℝ) + 1))) := by
    intro N
    obtain ⟨n, hn, hnN⟩ := hinf.exists_gt N
    refine ⟨n, hnN, ?_⟩
    have : s n = t := hn
    rw [← this]; exact hs n
  have f1 : ∀ ε : ℝ, crs (p t) (zplus r ε) = crs (p t) r + ε * dt (p t) r := by
    intro ε; unfold crs dt zplus; ring
  have f2 : ∀ ε : ℝ, crs (zplus r ε) (q t) = crs r (q t) + ε * (-(dt r (q t))) := by
    intro ε; unfold crs dt zplus; ring
  have hA1 : 0 ≤ crs (p t) r := affine_limit _ (dt (p t) r) (fun N => by
    obtain ⟨n, hn, h⟩ := hmem N
    exact ⟨n, hn, by rw [← f1]; exact h.1⟩)
  have hA2 : 0 ≤ crs r (q t) := affine_limit _ (-(dt r (q t))) (fun N => by
    obtain ⟨n, hn, h⟩ := hmem N
    exact ⟨n, hn, by rw [← f2]; exact h.2⟩)
  obtain ⟨n0, -, h0⟩ := hmem 0
  refine ⟨t, 1 / ((n0 : ℝ) + 1), by positivity, hA1, hA2, fun ε hε hle => ⟨?_, ?_⟩⟩
  · rw [f1]
    have h01 : 0 ≤ crs (p t) r + (1 / ((n0 : ℝ) + 1)) * dt (p t) r := by rw [← f1]; exact h0.1
    exact affine_interval hA1 h01 (by positivity) ε hε hle
  · rw [f2]
    have h02 : 0 ≤ crs r (q t) + (1 / ((n0 : ℝ) + 1)) * (-(dt r (q t))) := by rw [← f2]; exact h0.2
    exact affine_interval hA2 h02 (by positivity) ε hε hle

/-- The core case analysis: a closed cone containing all slightly-ccw points near the end ray `qs` of `s` starts on that ray. -/
theorem succ_ray_aux {ps qs pt qt : V2} (hs : SecOK ps qs) (ht : SecOK pt qt)
    (hdisj : 0 < crs qs qt → ∀ z, ¬ (inInt ps qs z ∧ inInt pt qt z))
    (A1 : 0 ≤ crs pt qs) (A2 : 0 ≤ crs qs qt) (δ : ℝ) (hδ : 0 < δ)
    (hmem : ∀ ε : ℝ, 0 < ε → ε ≤ δ → inCone pt qt (zplus qs ε)) :
    Par pt qs := by
  have hq : qs ≠ 0 := hs.ne_q
  have hp : pt ≠ 0 := ht.ne_p
  have f1 : ∀ ε : ℝ, crs pt (zplus qs ε) = crs pt qs + ε * dt pt qs := by
    intro ε; unfold crs dt zplus; ring
  have f2 : ∀ ε : ℝ, crs (zplus qs ε) qt = crs qs qt + ε * (-(dt qs qt)) := by
    intro ε; unfold crs dt zplus; ring
  have m1 := (hmem δ hδ le_rfl).1
  have m2 := (hmem δ hδ le_rfl).2
  rw [f1] at m1
  rw [f2] at m2
  rcases A1.eq_or_lt with hA1 | hA1
  · -- crs pt qs = 0
    refine ⟨hA1.symm, ?_⟩
    rw [← hA1] at m1
    have hd0 : 0 ≤ dt pt qs := by nlinarith
    rcases hd0.eq_or_lt with hd | hd
    · exfalso; exact hp (eq_zero_of_crs_dt hq hA1.symm hd.symm)
    · exact hd
  · exfalso
    rcases A2.eq_or_lt with hA2 | hA2
    · have htq := ht.ne_q
      have hd : dt qs qt ≤ 0 := by rw [← hA2] at m2; nlinarith
      have e := id_crs pt qs qt
      rw [← hA2] at e
      have hq' := nsq_pos hq
      have hqt : crs qt qs = 0 := by unfold crs at hA2 ⊢; linarith
      rcases ht with h | ⟨h0, _⟩
      · have : nsq qs * crs pt qt ≤ 0 := by rw [e]; nlinarith
        nlinarith [mul_pos hq' h]
      · have h3 : dt qs qt * crs pt qs = 0 := by rw [h0, mul_zero] at e; linarith
        have h4 : dt qs qt = 0 := (mul_eq_zero.mp h3).resolve_right hA1.ne'
        have h5 : dt qt qs = 0 := by unfold dt at h4 ⊢; linarith
        exact htq (eq_zero_of_crs_dt hq hqt h5)
    · -- qs lies in the open cone of t
      have hst := hdisj hA2
      obtain ⟨d1, hd1, H1⟩ := minus_ray_int hs
      obtain ⟨d2, hd2, H2⟩ := minus_ray_int_of_int hA1 hA2
      set ε := min d1 d2 / 2 with hε
      have hεpos : 0 < ε := by have := lt_min hd1 hd2; positivity
      have hε1 : ε < d1 := by have := min_le_left d1 d2; linarith [lt_min hd1 hd2]
      have hε2 : ε < d2 := by have := min_le_right d1 d2; linarith [lt_min hd1 hd2]
      exact hst (zminus qs ε) ⟨H1 ε hεpos hε1, H2 ε hεpos hε2⟩

/-- Successor: the sector `t` whose clockwise ray continues the counterclockwise ray of `s`. -/
theorem succ_exists (hok : AllOK p q) (hcov : Covers p q) (hdis : Disjoint' p q) (s : ι) :
    ∃ t, Par (p t) (q s) := by
  obtain ⟨t, δ, hδ, A1, A2, hmem⟩ := end_cover p q hcov (q s)
  refine ⟨t, succ_ray_aux (hok s) (hok t) ?_ A1 A2 δ hδ hmem⟩
  intro hpos z
  have hst : s ≠ t := by
    rintro rfl
    unfold crs at hpos
    linarith
  exact hdis s t hst z

/-- Two distinct sectors do not end on the same ray. -/
theorem end_inj (hok : AllOK p q) (hdis : Disjoint' p q) {s s' : ι} (hss : s ≠ s') :
    ¬ Par (q s') (q s) := by
  intro hpar
  obtain ⟨c, hc, hcq⟩ := hpar.smul
  obtain ⟨d1, hd1, H1⟩ := minus_ray_int (hok s)
  obtain ⟨d2, hd2, H2⟩ := minus_ray_int (hok s')
  set ε := min d1 d2 / 2 with hε
  have hεpos : 0 < ε := by have := lt_min hd1 hd2; positivity
  have hε1 : ε < d1 := by have := min_le_left d1 d2; linarith [lt_min hd1 hd2]
  have hε2 : ε < d2 := by have := min_le_right d1 d2; linarith [lt_min hd1 hd2]
  have h1 := H1 ε hεpos hε1
  have h2 := H2 ε hεpos hε2
  have hz : zminus (q s') ε = (c * (zminus (q s) ε).1, c * (zminus (q s) ε).2) := by
    rw [hcq]; unfold zminus; ext <;> simp <;> ring
  rw [hz] at h2
  exact hdis s s' hss (zminus (q s) ε) ⟨h1, (inInt_smul_iff hc).mp h2⟩

/-- The successor map (chosen). -/
theorem succ_map (hok : AllOK p q) (hcov : Covers p q) (hdis : Disjoint' p q) :
    ∃ σ : ι → ι, (∀ s, Par (p (σ s)) (q s)) ∧ Function.Bijective σ := by
  choose σ hσ using succ_exists p q hok hcov hdis
  refine ⟨σ, hσ, ?_⟩
  have hinj : Function.Injective σ := by
    intro s s' h
    by_contra hne
    apply end_inj p q hok hdis hne
    have h1 := hσ s
    have h2 := hσ s'
    rw [← h] at h2
    exact h2.symm.trans h1
  exact ⟨hinj, Finite.injective_iff_surjective.mp hinj⟩

end Family

/-! ## Width and the total angle of a cycle -/

/-- Width of a sector: the argument of the Hermitian product `conj p * q = (dot + i cross)`; for an admissible sector this is the
unoriented angle between `p` and `q`, in `(0, pi]`. -/
noncomputable def wd (p q : V2) : ℝ := Complex.arg ⟨dt p q, crs p q⟩

theorem wd_pos {p q : V2} (h : SecOK p q) : 0 < wd p q := by
  unfold wd
  rcases h with h | ⟨h0, hd⟩
  · have h1 : 0 ≤ Complex.arg ⟨dt p q, crs p q⟩ := Complex.arg_nonneg_iff.mpr (le_of_lt h)
    rcases h1.eq_or_lt with h2 | h2
    · exfalso
      have := (Complex.arg_eq_zero_iff).mp h2.symm
      simp at this
      linarith [this.2]
    · exact h2
  · have : Complex.arg ⟨dt p q, crs p q⟩ = Real.pi := by
      rw [Complex.arg_eq_pi_iff]; exact ⟨hd, h0⟩
    rw [this]; exact Real.pi_pos

theorem wd_le_pi (p q : V2) : wd p q ≤ Real.pi := Complex.arg_le_pi _

/-- **Angle sum of a closed chain of sectors.**  If the sectors `(u_j, v_j)` satisfy `u_{j+1} ~ v_j` (positive multiple) and the chain
closes up (`u_m = u_0`), the widths add up to a multiple of `2 pi`. -/
theorem cycle_angle_sum (m : ℕ) (u v : ℕ → V2) (hu : ∀ j, u j ≠ 0)
    (hpar : ∀ j, Par (u (j + 1)) (v j)) (hper : u m = u 0) :
    ∃ k : ℤ, ∑ j ∈ Finset.range m, wd (u j) (v j) = 2 * Real.pi * k := by
  classical
  set U : ℕ → ℂ := fun j => ⟨(u j).1, (u j).2⟩ with hU
  set W : ℕ → ℂ := fun j => ⟨dt (u j) (v j), crs (u j) (v j)⟩ with hW
  choose c hc hcu using fun j => (hpar j).smul
  have hUne : ∀ j, U j ≠ 0 := by
    intro j h
    apply hu j
    have h1 := congrArg Complex.re h
    have h2 := congrArg Complex.im h
    simp [hU] at h1 h2
    exact Prod.ext h1 h2
  -- conj (U j) * U (j+1) = c j * W j
  have hstep : ∀ j, (starRingEnd ℂ) (U j) * U (j + 1) = (c j : ℂ) * W j := by
    intro j
    have h1 := congrArg Prod.fst (hcu j)
    have h2 := congrArg Prod.snd (hcu j)
    apply Complex.ext
    · simp [hU, hW, dt]
      rw [h1, h2]; ring
    · simp [hU, hW, crs]
      rw [h1, h2]; ring
  have hprod1 : ∏ j ∈ Finset.range m, (starRingEnd ℂ) (U j) * U (j + 1)
      = ∏ j ∈ Finset.range m, (starRingEnd ℂ) (U j) * U j := by
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
    congr 1
    have e1 := Finset.prod_range_succ (fun j => U j) m
    have e2 := Finset.prod_range_succ' (fun j => U j) m
    have hUm : U m = U 0 := by simp [hU, hper]
    have : (∏ j ∈ Finset.range m, U (j + 1)) * U 0 = (∏ j ∈ Finset.range m, U j) * U 0 := by
      rw [← e2, ← hUm, ← e1]
    exact mul_right_cancel₀ (hUne 0) this
  have hnn : ∀ j, (starRingEnd ℂ) (U j) * U j = ((‖U j‖ ^ 2 : ℝ) : ℂ) := by
    intro j; rw [Complex.conj_mul']; push_cast; rfl
  simp only [hstep, hnn] at hprod1
  rw [Finset.prod_mul_distrib] at hprod1
  have hW' : ∀ j, ((‖W j‖ : ℝ) : ℂ) * Complex.exp ((Complex.arg (W j) : ℂ) * Complex.I) = W j := fun j =>
    Complex.norm_mul_exp_arg_mul_I (W j)
  have hWprod : ∏ j ∈ Finset.range m, W j
      = ((∏ j ∈ Finset.range m, ‖W j‖ : ℝ) : ℂ) * Complex.exp (((∑ j ∈ Finset.range m, Complex.arg (W j) : ℝ) : ℂ) * Complex.I) := by
    conv_lhs => rw [Finset.prod_congr rfl (fun j _ => (hW' j).symm)]
    rw [Finset.prod_mul_distrib, ← Complex.exp_sum]
    push_cast
    rw [Finset.sum_mul]
  have hargs : ∀ j, Complex.arg (W j) = wd (u j) (v j) := fun j => rfl
  simp only [hargs] at hWprod
  set S : ℝ := ∑ j ∈ Finset.range m, wd (u j) (v j) with hS
  have hmain : ((∏ j ∈ Finset.range m, c j : ℝ) : ℂ) * (((∏ j ∈ Finset.range m, ‖W j‖ : ℝ) : ℂ) * Complex.exp ((S : ℂ) * Complex.I))
      = ((∏ j ∈ Finset.range m, ‖U j‖ ^ 2 : ℝ) : ℂ) := by
    rw [← hWprod]; push_cast at hprod1 ⊢; exact hprod1
  have hcpos : 0 < ∏ j ∈ Finset.range m, c j := Finset.prod_pos (fun j _ => hc j)
  have hWpos : 0 < ∏ j ∈ Finset.range m, ‖W j‖ := by
    apply Finset.prod_pos
    intro j _
    have : W j ≠ 0 := by
      intro h0
      have h1 := congrArg Complex.re h0
      have h2 := congrArg Complex.im h0
      simp [hW] at h1 h2
      exact hu j (eq_zero_of_crs_dt (hpar j).ne_right h2 h1)
    exact norm_pos_iff.mpr this
  set R1 : ℝ := (∏ j ∈ Finset.range m, c j) * ∏ j ∈ Finset.range m, ‖W j‖ with hR1def
  set R2 : ℝ := ∏ j ∈ Finset.range m, ‖U j‖ ^ 2 with hR2def
  have hR1 : 0 < R1 := mul_pos hcpos hWpos
  have hR2 : 0 ≤ R2 := Finset.prod_nonneg (fun _ _ => by positivity)
  have hmain' : (R1 : ℂ) * Complex.exp ((S : ℂ) * Complex.I) = (R2 : ℂ) := by
    rw [← hmain, hR1def]; push_cast; ring
  have hnorm := congrArg (fun z : ℂ => ‖z‖) hmain'
  simp only [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs] at hnorm
  rw [abs_of_pos hR1, abs_of_nonneg hR2] at hnorm
  have hexp : Complex.exp ((S : ℂ) * Complex.I) = 1 := by
    have h1 : (R1 : ℂ) * Complex.exp ((S : ℂ) * Complex.I) = (R1 : ℂ) * 1 := by
      rw [hmain', ← hnorm]; ring
    exact mul_left_cancel₀ (by exact_mod_cast hR1.ne') h1
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp hexp
  have him := congrArg Complex.im hn
  simp at him
  exact ⟨n, by linarith⟩

section Cycle

variable {ι : Type*} [Fintype ι] (p q : ι → V2)

/-- **The cyclic fan.**  A covering, disjoint family of admissible sectors whose widths add up to `2 pi` can be listed counterclockwise
as `e 0, e 1, .., e (k-1)` (`k` = number of sectors, indices mod `k`) with the ccw ray of `e n` the cw ray of `e (n+1)`. -/
theorem fan_cycle [Nonempty ι] (hok : AllOK p q) (hcov : Covers p q) (hdis : Disjoint' p q)
    (hsum : ∑ s, wd (p s) (q s) = 2 * Real.pi) :
    ∃ e : ℕ → ι, (∀ n, Par (p (e (n + 1))) (q (e n))) ∧ (∀ n, e (n + Fintype.card ι) = e n) ∧
      Set.InjOn e (Set.Iio (Fintype.card ι)) ∧ (∀ s, ∃ j < Fintype.card ι, e j = s) := by
  classical
  obtain ⟨σ, hσ, hb⟩ := succ_map p q hok hcov hdis
  obtain ⟨s0⟩ := ‹Nonempty ι›
  set σe : Equiv.Perm ι := Equiv.ofBijective σ hb with hσe
  have hfix : σ^[orderOf σe] s0 = s0 := by
    have h1 : (σe ^ orderOf σe) s0 = s0 := by rw [pow_orderOf_eq_one]; rfl
    have h2 := congrArg (fun g : ι → ι => g s0) (Equiv.Perm.iterate_eq_pow σe (orderOf σe))
    simp only at h2
    exact h2.trans h1
  have hperiodic : Function.IsPeriodicPt σ (orderOf σe) s0 := hfix
  have hmpos : 0 < Function.minimalPeriod σ s0 :=
    hperiodic.minimalPeriod_pos (orderOf_pos σe)
  set m := Function.minimalPeriod σ s0 with hm
  set e : ℕ → ι := fun j => σ^[j] s0 with he
  have hem : e m = e 0 := Function.isPeriodicPt_minimalPeriod σ s0
  have hstep : ∀ n, e (n + 1) = σ (e n) := fun n => Function.iterate_succ_apply' σ n s0
  have hPar : ∀ n, Par (p (e (n + 1))) (q (e n)) := fun n => by rw [hstep]; exact hσ _
  have hshift : ∀ n, e (n + m) = e n := fun n => by
    show σ^[n + m] s0 = σ^[n] s0
    rw [Function.iterate_add_apply]
    exact congrArg (σ^[n]) (Function.isPeriodicPt_minimalPeriod σ s0)
  have hinj : Set.InjOn e (Set.Iio m) := Function.iterate_injOn_Iio_minimalPeriod
  obtain ⟨k, hk⟩ := cycle_angle_sum m (fun j => p (e j)) (fun j => q (e j)) (fun j => (hok (e j)).ne_p)
    hPar (by show p (e m) = p (e 0); rw [hem])
  have hwpos : ∀ s, 0 < wd (p s) (q s) := fun s => wd_pos (hok s)
  have hSpos : 0 < ∑ j ∈ Finset.range m, wd (p (e j)) (q (e j)) :=
    Finset.sum_pos (fun j _ => hwpos _) ⟨0, Finset.mem_range.mpr hmpos⟩
  rw [hk] at hSpos
  have hk1 : 1 ≤ k := by
    by_contra h
    push_neg at h
    have : (k : ℝ) ≤ 0 := by exact_mod_cast (by omega : k ≤ 0)
    nlinarith [Real.pi_pos]
  have hk1' : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  set O : Finset ι := (Finset.range m).image e with hO
  have hinjR : Set.InjOn e (↑(Finset.range m) : Set ℕ) := by
    intro a ha b hb' h
    exact hinj (by simpa using ha) (by simpa using hb') h
  have hOsum : ∑ s ∈ O, wd (p s) (q s) = ∑ j ∈ Finset.range m, wd (p (e j)) (q (e j)) :=
    Finset.sum_image hinjR
  have hsd := Finset.sum_sdiff (f := fun s => wd (p s) (q s)) (Finset.subset_univ O)
  have hall : ∀ s, s ∈ O := by
    intro s
    by_contra hs
    have hsm : s ∈ Finset.univ \ O := by simp [hs]
    have h1 : wd (p s) (q s) ≤ ∑ x ∈ Finset.univ \ O, wd (p x) (q x) :=
      Finset.single_le_sum (f := fun x => wd (p x) (q x)) (fun x _ => (hwpos x).le) hsm
    have h2 := hwpos s
    rw [hOsum, hk] at hsd
    nlinarith [Real.pi_pos]
  have hcard : Fintype.card ι = m := by
    have : O = Finset.univ := Finset.eq_univ_iff_forall.mpr hall
    rw [← Finset.card_univ, ← this, hO, Finset.card_image_of_injOn hinjR, Finset.card_range]
  refine ⟨e, hPar, ?_, ?_, ?_⟩
  · intro n; rw [hcard]; exact hshift n
  · rw [hcard]; exact hinj
  · intro s
    obtain ⟨j, hj, hjs⟩ := Finset.mem_image.mp (hall s)
    exact ⟨j, by rw [hcard]; exact Finset.mem_range.mp hj, hjs⟩

end Cycle

/-! ## Non-vacuity: the four quadrants, and a negative control -/

/-- The four quadrant sectors `(1,0)->(0,1)`, `(0,1)->(-1,0)`, `(-1,0)->(0,-1)`, `(0,-1)->(1,0)`. -/
def quadP : Fin 4 → V2 := ![(1, 0), (0, 1), (-1, 0), (0, -1)]
def quadQ : Fin 4 → V2 := fun s => quadP (s + 1)

theorem quad_allOK : AllOK quadP quadQ := by
  intro s; fin_cases s <;> simp [SecOK, crs, quadP, quadQ] <;> norm_num [Fin.isValue]

theorem quad_covers : Covers quadP quadQ := by
  intro z
  rcases le_total 0 z.1 with h1 | h1 <;> rcases le_total 0 z.2 with h2 | h2
  · exact ⟨0, by simp [inCone, crs, quadP, quadQ]; constructor <;> linarith⟩
  · exact ⟨3, by simp [inCone, crs, quadP, quadQ]; constructor <;> linarith⟩
  · exact ⟨1, by simp [inCone, crs, quadP, quadQ]; constructor <;> linarith⟩
  · exact ⟨2, by simp [inCone, crs, quadP, quadQ]; constructor <;> linarith⟩

theorem quad_disjoint : Disjoint' quadP quadQ := by
  intro s t hst z hz
  fin_cases s <;> fin_cases t <;> simp [inInt, crs, quadP, quadQ] at hst hz <;> linarith [hz.1, hz.2]

theorem quad_sum : ∑ s, wd (quadP s) (quadQ s) = 2 * Real.pi := by
  have h : ∀ s : Fin 4, wd (quadP s) (quadQ s) = Real.pi / 2 := by
    intro s
    have hI : (⟨0, 1⟩ : ℂ) = Complex.I := Complex.ext (by simp) (by simp)
    fin_cases s <;> simp [wd, dt, crs, quadP, quadQ] <;> first | (rw [hI]; exact Complex.arg_I) | skip
  simp [h, Fin.sum_univ_four]; ring

/-- **Witness**: the four-quadrant family satisfies all hypotheses of `fan_cycle`. -/
theorem fan_cycle_witness : ∃ e : ℕ → Fin 4, (∀ n, Par (quadP (e (n + 1))) (quadQ (e n))) ∧
    (∀ n, e (n + Fintype.card (Fin 4)) = e n) ∧ Set.InjOn e (Set.Iio (Fintype.card (Fin 4))) ∧
    (∀ s, ∃ j < Fintype.card (Fin 4), e j = s) :=
  fan_cycle quadP quadQ quad_allOK quad_covers quad_disjoint quad_sum

/-- **Negative control**: two copies of the same sector are not disjoint (so the hypothesis `Disjoint'` is not automatic). -/
theorem double_not_disjoint : ¬ Disjoint' (fun _ : Fin 2 => ((1, 0) : V2)) (fun _ : Fin 2 => ((0, 1) : V2)) := by
  intro h
  exact h 0 1 (by decide) (1, 1) ⟨by simp [inInt, crs], by simp [inInt, crs]⟩

end Erdos634.Draft.LaczFormal.Graph

#print axioms Erdos634.Draft.LaczFormal.Graph.fan_cycle
#print axioms Erdos634.Draft.LaczFormal.Graph.fan_cycle_witness
#print axioms Erdos634.Draft.LaczFormal.Graph.succ_exists
