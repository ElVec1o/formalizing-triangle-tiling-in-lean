-- Draft/KConjLemmaK.lean — CASE A, node A3: **LEMMA K (K1 ∧ K2) on a real `CongruentDissection`**
-- (PROOF_row0c.md §3.3), with K1, K2 exactly the predicates of the VERIFIED Lemma K*
-- (Draft/CaseALemmaKStar.lean) and f the corner figures of the dissection.
--
-- K2 route (moments, no winding numbers):
--   * normalise (Draft/KConjNormal): corners in K = ℚ(ζ_{4n}) (Lemma 1), |det| = P per tile, N·P target;
--   * for a unit k pick m ≡ ±k (mod n), m ≡ 1 (mod 4), σ(ζ) = ζ^m (Draft/KConjField);
--   * the conjugated triangles form a genuine dissection of the conjugated target
--     (Draft/KConjAe.phiDissection: moment transfer + moment determinacy);
--   * at a target corner the local angles of that dissection add up (`sum_localAngle_eq`); tiles not
--     having the corner as a vertex contribute 0 or ≥ π, impossible below the target angle < π, so
--     Σ_{tile corners at A_j} ∠Φ = ∠ΦT at A_j (`vertex_sum`);
--   * each conjugated angle is π·y or π(1−y) (Draft/KConjAngle); the three angles of a triangle sum to
--     π, which FORCES the choice (`forced`): tile angles π·x′(m), target angle π·x′_{u_j}(m) — the
--     latter using K1 (s_ABC = s_T, `LemmaK1.lemmaK_K1`);
--   * K2(m) ⇒ K2(k): K2 depends on k only modulo n and up to sign (`K2_congr`).
-- Sign issue (the paper's ε_t, ε_ABC): never needed.  The dets enter the moment transfer only through
-- |det Φt| = |σ(P)|, |det ΦT| = N|σ(P)|, which already forces a positive covering; the paper's
-- "ε = ε_ABC" (= K1) is used only to identify the target's conjugated angle.
-- Formalization debt on a paper-level PROVED node; NOT /goal progress.  Imported directly by All.lean (stale "NOT imported" header corrected 2026-10-04).
-- H59: no parameter pair (e, f) is evaluated here.
import Erdos634.Draft.KConjNormal
import Erdos634.CornerAnglePerm
import Erdos634.AngleSumDissection
import Erdos634.Draft.CaseALemmaVWitness

open Complex

namespace Erdos634.KConj

open Erdos634.Geometry Erdos634.Geometry.CaseA.LemmaV Erdos634.Geometry.CaseA.LemmaK1
  Erdos634.LemmaKStar Erdos634.DissectionMap Erdos634.CertCoord

variable {N : ℕ}

/-! ## Vertex sums at a target corner -/

theorem localAngle_nonvertex (T : Tri) (p : Plane) (h : ∀ v, p ≠ T.pts v) :
    T.localAngle p = 0 ∨ Real.pi ≤ T.localAngle p := by
  classical
  unfold Tri.localAngle
  rw [dif_neg (fun ⟨j, hj⟩ => h j hj)]
  split_ifs
  · right; linarith [Real.pi_pos]
  · right; exact le_refl _
  · left; rfl

/-- The vertex contribution of one tile at `p`. -/
noncomputable def vc (T : Tri) (p : Plane) : ℝ := ∑ v, if T.pts v = p then T.angleAt v else 0

theorem vc_of_vertex (T : Tri) (v0 : Fin 3) : vc T (T.pts v0) = T.localAngle (T.pts v0) := by
  rw [vc, Tri.localAngle_vertex]
  have : ∀ v, (T.pts v = T.pts v0) ↔ v = v0 := fun v => T.indep.injective.eq_iff
  simp only [this]
  rw [Finset.sum_ite_eq']; simp; rfl

theorem vc_of_nonvertex (T : Tri) (p : Plane) (h : ∀ v, p ≠ T.pts v) : vc T p = 0 := by
  rw [vc]; exact Finset.sum_eq_zero (fun v _ => if_neg (fun h' => h v h'.symm))

/-- **Vertex sum at a target corner.** -/
theorem vertex_sum (D0 : Dissection N) (j : Fin 3) :
    ∑ i, vc (D0.tile i) (D0.target.pts j) = D0.target.angleAt j := by
  have hsum := D0.sum_localAngle_eq (D0.target.pts j)
  rw [Tri.localAngle_vertex] at hsum
  have hlt : D0.target.angleAt j < Real.pi := angle_lt_pi _ j
  have hnn : ∀ i, 0 ≤ (D0.tile i).localAngle (D0.target.pts j) := fun i => Tri.localAngle_nonneg _ _
  have key : ∀ i, vc (D0.tile i) (D0.target.pts j) = (D0.tile i).localAngle (D0.target.pts j) := by
    intro i
    by_cases hv : ∃ v, D0.target.pts j = (D0.tile i).pts v
    · obtain ⟨v, hv⟩ := hv; rw [hv]; exact vc_of_vertex _ v
    · push Not at hv
      rw [vc_of_nonvertex _ _ hv]
      rcases localAngle_nonvertex _ _ hv with h | h
      · exact h.symm
      · exfalso
        have := Finset.single_le_sum (fun i _ => hnn i) (Finset.mem_univ i)
        rw [hsum] at this
        exact absurd (lt_of_lt_of_le hlt (h.trans this)) (lt_irrefl _)
  rw [Finset.sum_congr rfl (fun i _ => key i), hsum]; rfl

/-! ## Corner figures -/

/-- The corner figure `f_j`, relative to a corner labelling `idx` (tile `i`'s corner `v` is a copy
of model corner `idx i v`). -/
noncomputable def fig (D : CongruentDissection N) (idx : Fin N → Equiv.Perm (Fin 3)) (j l : Fin 3) :
    ℕ :=
  (Finset.univ.filter (fun p : Fin N × Fin 3 =>
    (D.tile p.1).pts p.2 = D.target.pts j ∧ idx p.1 p.2 = l)).card

theorem fiber_sum (D : CongruentDissection N) (idx : Fin N → Equiv.Perm (Fin 3)) (j : Fin 3)
    (g : Fin 3 → ℝ) :
    ∑ i, ∑ v, (if (D.tile i).pts v = D.target.pts j then g (idx i v) else 0)
      = ∑ l, (fig D idx j l : ℝ) * g l := by
  classical
  have h1 : ∀ l, (fig D idx j l : ℝ) * g l = ∑ p : Fin N × Fin 3,
      (if (D.tile p.1).pts p.2 = D.target.pts j ∧ idx p.1 p.2 = l then g l else 0) := by
    intro l
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, fig]
  calc ∑ i, ∑ v, (if (D.tile i).pts v = D.target.pts j then g (idx i v) else 0)
      = ∑ p : Fin N × Fin 3, (if (D.tile p.1).pts p.2 = D.target.pts j then g (idx p.1 p.2) else 0) :=
        by rw [Fintype.sum_prod_type]
    _ = ∑ p : Fin N × Fin 3, ∑ l, (if (D.tile p.1).pts p.2 = D.target.pts j ∧ idx p.1 p.2 = l
          then g l else 0) := by
        refine Finset.sum_congr rfl (fun p _ => ?_)
        by_cases hp : (D.tile p.1).pts p.2 = D.target.pts j
        · simp only [hp, true_and, if_true]
          rw [Finset.sum_ite_eq]; simp
        · simp [hp]
    _ = ∑ l, ∑ p : Fin N × Fin 3, (if (D.tile p.1).pts p.2 = D.target.pts j ∧ idx p.1 p.2 = l
          then g l else 0) := Finset.sum_comm
    _ = ∑ l, (fig D idx j l : ℝ) * g l := by simp_rw [h1]

theorem exists_idx (D : CongruentDissection N) {n : ℕ} (a : Fin 3 → ℕ)
    (ha : ∀ k, D.model.angleAt k = a k * Real.pi / n) :
    ∃ idx : Fin N → Equiv.Perm (Fin 3), ∀ i v, (D.tile i).angleAt v = a (idx i v) * Real.pi / n := by
  choose idx hidx using fun i => Tri.Congruent.cornerAngle_perm (D.tiles_congruent i)
  exact ⟨idx, fun i v => by rw [Tri.angleAt, ← hidx i v]; exact ha (idx i v)⟩

/-- **Target angles from corner figures**: `∠A_j = (f_j · a) π/n`. -/
theorem target_angle_fig (D : CongruentDissection N) {n : ℕ} (a : Fin 3 → ℕ)
    (idx : Fin N → Equiv.Perm (Fin 3))
    (hidx : ∀ i v, (D.tile i).angleAt v = a (idx i v) * Real.pi / n) (j : Fin 3) :
    D.target.angleAt j = (uu a (fig D idx) j : ℕ) * Real.pi / n := by
  have h := vertex_sum D.toDissection j
  simp only [vc] at h
  have e : ∀ i v, (if (D.tile i).pts v = D.target.pts j then (D.tile i).angleAt v else 0)
      = (if (D.tile i).pts v = D.target.pts j then (fun l => (a l : ℝ) * Real.pi / n) (idx i v)
          else 0) := by
    intro i v; split_ifs <;> simp [hidx]
  simp only [e] at h
  have hfs := fiber_sum D idx j (fun l => (a l : ℝ) * Real.pi / n)
  beta_reduce at hfs
  rw [hfs] at h
  rw [← h, uu]; push_cast
  rw [Finset.sum_mul, Finset.sum_div]
  refine Finset.sum_congr rfl (fun l _ => by ring)

/-! ## The forcing lemma -/

theorem forced (y β : Fin 3 → ℝ) (hy : ∀ v, 0 < y v) (hy1 : ∀ v, y v < 1)
    (hβ : ∀ v, β v = y v ∨ β v = 1 - y v) (hβs : β 0 + β 1 + β 2 = 1) {s : ℝ}
    (hs : y 0 + y 1 + y 2 = s) (hs12 : s = 1 ∨ s = 2) (v : Fin 3) :
    β v = if s = 1 then y v else 1 - y v := by
  have h0 := hy 0; have h1 := hy 1; have h2 := hy 2
  have g0 := hy1 0; have g1 := hy1 1; have g2 := hy1 2
  rcases hs12 with rfl | rfl
  · rw [if_pos rfl]
    rcases hβ 0 with a0 | a0 <;> rcases hβ 1 with a1 | a1 <;> rcases hβ 2 with a2 | a2 <;>
      fin_cases v <;> simp <;> linarith
  · rw [if_neg (by norm_num)]
    rcases hβ 0 with a0 | a0 <;> rcases hβ 1 with a1 | a1 <;> rcases hβ 2 with a2 | a2 <;>
      fin_cases v <;> simp <;> linarith

/-! ## K2 depends on k only up to sign mod n -/

theorem K2_congr {n : ℕ} (hn : 0 < n) {a : Fin 3 → ℕ} {f : Fin 3 → Fin 3 → ℕ}
    (hsum : ∑ i, a i = n) (ha1 : ∀ i, 1 ≤ a i) (hsu : ∑ j, uu a f j = n) (hu1 : ∀ j, 1 ≤ uu a f j)
    {k m : ℤ} (hk : Int.gcd k n = 1) (h : (n : ℤ) ∣ m - k ∨ (n : ℤ) ∣ m + k) :
    K2 n a f m ↔ K2 n a f k := by
  have hxp : ∀ i, xp n a m i = xp n a k i ∧ ∀ j, xpu n a f m j = xpu n a f k j := by
    intro i
    rcases h with h | h
    · have hy : ∀ l, yv n a m l = yv n a k l := fun l => yv_congr h hn l
      have hx : ∀ l, xv n a f m l = xv n a f k l := fun l => yv_congr (a := uu a f) h hn l
      have hs : sT n a m = sT n a k := by unfold sT; simp only [hy]
      refine ⟨by unfold xp; rw [hs, hy], fun j => by unfold xpu; rw [hs, hx]⟩
    · have h' : (n : ℤ) ∣ m - (-k) := by simpa using h
      have hy : ∀ l, yv n a m l = 1 - yv n a k l := fun l => by
        rw [yv_congr h' hn l, yv_neg hsum ha1 hk]
      have hx : ∀ l, xv n a f m l = 1 - xv n a f k l := fun l => by
        rw [show xv n a f m l = yv n (uu a f) m l from rfl, yv_congr (a := uu a f) h' hn l,
          yv_neg hsu hu1 hk]; rfl
      have hs : sT n a m = 3 - sT n a k := by
        unfold sT; simp only [hy, Fin.sum_univ_three]; ring
      rcases sT_12 hsum ha1 hk with h1 | h1
      · have hm : sT n a m ≠ 1 := by rw [hs, h1]; norm_num
        refine ⟨by unfold xp; rw [if_neg hm, if_pos h1, hy]; ring,
          fun j => by unfold xpu; rw [if_neg hm, if_pos h1, hx]; ring⟩
      · have hm : sT n a m = 1 := by rw [hs, h1]; norm_num
        have hk1 : sT n a k ≠ 1 := by rw [h1]; norm_num
        exact ⟨by unfold xp; rw [if_pos hm, if_neg hk1, hy],
          fun j => by unfold xpu; rw [if_pos hm, if_neg hk1, hx]⟩
  unfold K2
  constructor
  · intro H j; rw [← (hxp 0).2 j, ← H j]; simp only [fun i => (hxp i).1]
  · intro H j; rw [(hxp 0).2 j, ← H j]; simp only [fun i => (hxp i).1]

/-! ## Incidences survive conjugation -/

theorem phi_pts_eq {n m : ℕ} (hn : 0 < n) (σ : Kf n →ₐ[ℚ] ℂ)
    (hσ : σ (IntermediateField.AdjoinSimple.gen ℚ (zeta n)) = zeta n ^ m) (hm4 : m % 4 = 1)
    (T T' : Tri) (hT : ∀ k, toC (T.pts k) ∈ Kf n) (hT' : ∀ k, toC (T'.pts k) ∈ Kf n) (v w : Fin 3) :
    (phiTri hn σ hσ hm4 T hT).pts v = (phiTri hn σ hσ hm4 T' hT').pts w ↔ T.pts v = T'.pts w := by
  constructor
  · intro h
    have h1 := congrArg toC h
    rw [toC_phiTri, toC_phiTri] at h1
    have h2 : (⟨toC (T.pts v), hT v⟩ : Kf n) = ⟨toC (T'.pts w), hT' w⟩ := σ.toRingHom.injective h1
    exact toC.injective (congrArg Subtype.val h2)
  · intro h
    apply toC.injective
    rw [toC_phiTri, toC_phiTri]
    show σ ⟨toC (T.pts v), hT v⟩ = σ ⟨toC (T'.pts w), hT' w⟩
    congr 2; rw [h]

/-! ## Lemma K -/

/-- **Lemma K (K1 ∧ K2), on a real `CongruentDissection`.**  Model angles `a_i π/n`; `idx` any
labelling of tile corners by model corners (it exists: `exists_idx`); `f = fig D idx` the corner
figures.  Then the target angles are `(f_j · a) π/n`, and for every unit `k` mod `n`,
`K1 n a f k ∧ K2 n a f k` — exactly the hypothesis of the VERIFIED `LemmaKStar.lemmaKStar`. -/
theorem lemmaK (D : CongruentDissection N) {n : ℕ} (hn : 0 < n) (a : Fin 3 → ℕ)
    (ha : ∀ k, D.model.angleAt k = a k * Real.pi / n) (idx : Fin N → Equiv.Perm (Fin 3))
    (hidx : ∀ i v, (D.tile i).angleAt v = a (idx i v) * Real.pi / n) :
    (∀ j, D.target.angleAt j = (uu a (fig D idx) j : ℕ) * Real.pi / n) ∧
    ∀ k : ℤ, Int.gcd k n = 1 → K1 n a (fig D idx) k ∧ K2 n a (fig D idx) k := by
  set f := fig D idx
  have hf := target_angle_fig D a idx hidx
  refine ⟨hf, fun k hk => ⟨lemmaK_K1 D hn a ha f hf hk, ?_⟩⟩
  -- arithmetic facts
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have sum_of : ∀ (T : Tri) (b : Fin 3 → ℕ), (∀ i, T.angleAt i = b i * Real.pi / n) →
      ∑ i, b i = n := by
    intro T b hb
    have hs := T.angleAt_sum
    rw [hb 0, hb 1, hb 2] at hs
    have hnn : (n : ℝ) * (Real.pi / n) = Real.pi := by field_simp
    have key : (((b 0 + b 1 + b 2 : ℕ) : ℝ) - n) * (Real.pi / n) = 0 := by
      push_cast; linear_combination hs - hnn
    have := sub_eq_zero.mp ((mul_eq_zero.mp key).resolve_right (div_ne_zero Real.pi_ne_zero hn'))
    rw [Fin.sum_univ_three]; exact_mod_cast this
  have hsum := sum_of _ a ha
  have hsu := sum_of _ (uu a f) hf
  have ha1 : ∀ i, 1 ≤ a i := fun i => (nat_bounds hn (ha i) (angle_pos _ i) (angle_lt_pi _ i)).1
  have hu1 : ∀ j, 1 ≤ uu a f j := fun j => (nat_bounds hn (hf j) (angle_pos _ j) (angle_lt_pi _ j)).1
  -- the lift m and the embedding σ
  obtain ⟨m, hmc, hm4, hmk⟩ := exists_m hn hk
  obtain ⟨σ, hσ⟩ := exists_sigma hn hmc
  have hmg : Int.gcd (m : ℤ) n = 1 := by
    rw [Int.gcd_natCast_natCast]; exact Nat.Coprime.coprime_mul_left_right hmc
  rw [← K2_congr hn hsum ha1 hsu hu1 hk hmk]
  -- the conjugated dissection
  set Dn' := Dn D
  set E := phiDissection hn σ hσ hm4 Dn' (Dn_hK D hn a ha) (Dn_hKT D hn a ha) (PN D) (Dn_hP D)
    (Dn_hPT D)
  -- conjugated tile angles
  have hy : ∀ l, yf n m (a l) = ((yv n a m l : ℚ) : ℝ) := fun l => rfl
  have hyp : ∀ l, 0 < yv n a m l := fun l =>
    lt_of_le_of_ne (Int.fract_nonneg _) (Ne.symm (yv_ne hsum ha1 hmg l))
  have hyl : ∀ l, yv n a m l < 1 := fun l => Int.fract_lt_one _
  have hs12 : sT n a m = 1 ∨ sT n a m = 2 := sT_12 hsum ha1 hmg
  have tile_ang : ∀ i v, (E.tile i).angleAt v = Real.pi * ((xp n a m (idx i v) : ℚ) : ℝ) := by
    intro i
    have hang : ∀ v, (E.tile i).angleAt v = Real.pi * yf n m (a (idx i v)) ∨
        (E.tile i).angleAt v = Real.pi * (1 - yf n m (a (idx i v))) := by
      intro v
      refine phi_angle hn σ hσ hm4 (Dn'.tile i) (Dn_hK D hn a ha i) v (a (idx i v)) ?_ ?_
      · rw [show Dn'.tile i = mapTri (eN D) (D.tile i) from rfl, angleAt_eN]; exact hidx i v
      · rw [hy]; exact_mod_cast hyp _
    have hsumβ := (E.tile i).angleAt_sum
    set y : Fin 3 → ℝ := fun v => ((yv n a m (idx i v) : ℚ) : ℝ)
    set β : Fin 3 → ℝ := fun v => (E.tile i).angleAt v / Real.pi
    have hpi := Real.pi_pos
    have hsy : y 0 + y 1 + y 2 = ((sT n a m : ℚ) : ℝ) := by
      have : ∑ v, y v = ∑ l, ((yv n a m l : ℚ) : ℝ) :=
        Equiv.sum_comp (idx i) (fun l => ((yv n a m l : ℚ) : ℝ))
      rw [Fin.sum_univ_three, Fin.sum_univ_three] at this
      rw [this, sT, Fin.sum_univ_three]; push_cast; ring
    have hF := forced y β
      (fun v => by show (0 : ℝ) < ((yv n a m (idx i v) : ℚ) : ℝ); exact_mod_cast hyp _)
      (fun v => by show ((yv n a m (idx i v) : ℚ) : ℝ) < 1; exact_mod_cast hyl _)
      (fun v => by
        rcases hang v with h | h
        · left; simp only [β, y, h, ← hy]; field_simp
        · right; simp only [β, y, h, ← hy]; field_simp)
      (by simp only [β]; field_simp; linarith) hsy
      (by rcases hs12 with h | h <;> [left; right] <;> rw [h] <;> norm_num)
    intro v
    have := hF v
    simp only [β] at this
    rw [div_eq_iff hpi.ne'] at this
    rw [this, xp]
    split_ifs with h1 h2 h2
    · simp [y]; ring
    · exact absurd (by exact_mod_cast h1) h2
    · exact absurd (by rw [h2]; norm_num) h1
    · push_cast; simp [y]; ring
  -- conjugated target angle
  have hK1 := lemmaK_K1 D hn a ha f hf hmg
  have hxp : ∀ l, 0 < xv n a f m l := fun l =>
    lt_of_le_of_ne (Int.fract_nonneg _) (Ne.symm (yv_ne (a := uu a f) hsu hu1 hmg l))
  have hxl : ∀ l, xv n a f m l < 1 := fun l => Int.fract_lt_one _
  have targ_ang : ∀ j, E.target.angleAt j = Real.pi * ((xpu n a f m j : ℚ) : ℝ) := by
    have hang : ∀ j, E.target.angleAt j = Real.pi * yf n m (uu a f j) ∨
        E.target.angleAt j = Real.pi * (1 - yf n m (uu a f j)) := by
      intro j
      refine phi_angle hn σ hσ hm4 Dn'.target (Dn_hKT D hn a ha) j (uu a f j) ?_ ?_
      · rw [show Dn'.target = mapTri (eN D) D.target from rfl, angleAt_eN]; exact hf j
      · show 0 < ((xv n a f m j : ℚ) : ℝ); exact_mod_cast hxp j
    have hsumβ := E.target.angleAt_sum
    set y : Fin 3 → ℝ := fun j => ((xv n a f m j : ℚ) : ℝ)
    set β : Fin 3 → ℝ := fun j => E.target.angleAt j / Real.pi
    have hpi := Real.pi_pos
    have hsy : y 0 + y 1 + y 2 = ((sT n a m : ℚ) : ℝ) := by
      rw [show sT n a m = sABC n a f m from hK1, sABC, Fin.sum_univ_three]; push_cast; rfl
    have hF := forced y β
      (fun v => by show (0 : ℝ) < ((xv n a f m v : ℚ) : ℝ); exact_mod_cast hxp _)
      (fun v => by show ((xv n a f m v : ℚ) : ℝ) < 1; exact_mod_cast hxl _)
      (fun v => by
        rcases hang v with h | h
        · left; simp only [β, y, h]; field_simp; rfl
        · right; simp only [β, y, h]; field_simp; rfl)
      (by simp only [β]; field_simp; linarith) hsy
      (by rcases hs12 with h | h <;> [left; right] <;> rw [h] <;> norm_num)
    intro j
    have := hF j
    simp only [β] at this
    rw [div_eq_iff hpi.ne'] at this
    rw [this, xpu]
    split_ifs with h1 h2 h2
    · simp [y]; ring
    · exact absurd (by exact_mod_cast h1) h2
    · exact absurd (by rw [h2]; norm_num) h1
    · push_cast; simp [y]; ring
  -- vertex sum on the conjugated dissection
  intro j
  have hv := vertex_sum E j
  simp only [vc] at hv
  have hpred : ∀ i v, ((E.tile i).pts v = E.target.pts j) ↔ ((D.tile i).pts v = D.target.pts j) := by
    intro i v
    rw [show E.tile i = phiTri hn σ hσ hm4 (Dn'.tile i) (Dn_hK D hn a ha i) from rfl,
      show E.target = phiTri hn σ hσ hm4 Dn'.target (Dn_hKT D hn a ha) from rfl, phi_pts_eq,
      Dn_tile_pts, Dn_target_pts, eN_inj]
  have e : ∀ i v, (if (E.tile i).pts v = E.target.pts j then (E.tile i).angleAt v else 0)
      = (if (D.tile i).pts v = D.target.pts j then
          (fun l => Real.pi * ((xp n a m l : ℚ) : ℝ)) (idx i v) else 0) := by
    intro i v
    by_cases hp : (D.tile i).pts v = D.target.pts j
    · rw [if_pos ((hpred i v).mpr hp), if_pos hp, tile_ang]
    · rw [if_neg (fun h => hp ((hpred i v).mp h)), if_neg hp]
  simp only [e] at hv
  have hfs := fiber_sum D idx j (fun l => Real.pi * ((xp n a m l : ℚ) : ℝ))
  beta_reduce at hfs
  rw [hfs, targ_ang] at hv
  have hv' : ∑ l, (f j l : ℝ) * ((xp n a m l : ℚ) : ℝ) = ((xpu n a f m j : ℚ) : ℝ) := by
    have hpi := Real.pi_pos
    apply mul_left_cancel₀ hpi.ne'
    rw [← hv, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun l _ => by ring)
  exact_mod_cast hv'

/-- **Lemma K + Lemma K\*** : on a real congruent dissection with rational model angles
`a_i π/n` (`n ≥ 3`), the corner figures satisfy `e ∈ R(a)` (the input of Lemma S / A8). -/
theorem lemmaK_rel (D : CongruentDissection N) {n : ℕ} (hn3 : 3 ≤ n) (a : Fin 3 → ℕ)
    (ha : ∀ k, D.model.angleAt k = a k * Real.pi / n) (idx : Fin N → Equiv.Perm (Fin 3))
    (hidx : ∀ i v, (D.tile i).angleAt v = a (idx i v) * Real.pi / n) :
    ev (fig D idx) ∈ Erdos634.LemmaS.relSpace n a := by
  have hn : 0 < n := by omega
  obtain ⟨hf, hK⟩ := lemmaK D hn a ha idx hidx
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have sum_of : ∀ (T : Tri) (b : Fin 3 → ℕ), (∀ i, T.angleAt i = b i * Real.pi / n) →
      ∑ i, b i = n := by
    intro T b hb
    have hs := T.angleAt_sum
    rw [hb 0, hb 1, hb 2] at hs
    have hnn : (n : ℝ) * (Real.pi / n) = Real.pi := by field_simp
    have key : (((b 0 + b 1 + b 2 : ℕ) : ℝ) - n) * (Real.pi / n) = 0 := by
      push_cast; linear_combination hs - hnn
    have := sub_eq_zero.mp ((mul_eq_zero.mp key).resolve_right (div_ne_zero Real.pi_ne_zero hn'))
    rw [Fin.sum_univ_three]; exact_mod_cast this
  have ha1 : ∀ i, 1 ≤ a i := fun i => (nat_bounds hn (ha i) (angle_pos _ i) (angle_lt_pi _ i)).1
  have hu1 : ∀ j, 1 ≤ uu a (fig D idx) j := fun j =>
    (nat_bounds hn (hf j) (angle_pos _ j) (angle_lt_pi _ j)).1
  have hfne : ∀ j, fig D idx j ≠ 0 := by
    intro j h
    have := hu1 j
    rw [uu, h] at this; simp at this
  exact lemmaKStar_toRel hn3 ha1 (sum_of _ a ha) hfne (sum_of _ _ hf) hK

/-! ## Witness: the real `CongruentDissection 2` of CaseALemmaHPiFour (n = 4, a = (1,2,1)) -/

theorem lemmaK_witness :
    ∃ idx : Fin 2 → Equiv.Perm (Fin 3),
      (∀ j, Erdos634.Draft.CaseALemmaHPiFour.dissection.target.angleAt j
        = (uu ![1, 2, 1] (fig Erdos634.Draft.CaseALemmaHPiFour.dissection idx) j : ℕ)
          * Real.pi / (4 : ℕ)) ∧
      ∀ k : ℤ, Int.gcd k 4 = 1 →
        K1 4 ![1, 2, 1] (fig Erdos634.Draft.CaseALemmaHPiFour.dissection idx) k ∧
        K2 4 ![1, 2, 1] (fig Erdos634.Draft.CaseALemmaHPiFour.dissection idx) k := by
  obtain ⟨idx, hidx⟩ := exists_idx Erdos634.Draft.CaseALemmaHPiFour.dissection (n := 4) ![1, 2, 1]
    Erdos634.Draft.CaseALemmaVWitness.model_angles
  exact ⟨idx, lemmaK _ (by norm_num) _ Erdos634.Draft.CaseALemmaVWitness.model_angles idx hidx⟩

end Erdos634.KConj

#print axioms Erdos634.KConj.vertex_sum
#print axioms Erdos634.KConj.K2_congr
#print axioms Erdos634.KConj.lemmaK
#print axioms Erdos634.KConj.lemmaK_rel
#print axioms Erdos634.KConj.lemmaK_witness
