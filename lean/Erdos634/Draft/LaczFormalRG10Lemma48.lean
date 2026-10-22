-- Draft/LaczFormalRG10Lemma48.lean -- **Lemma 4.8 of Laczkovich (DCG 48 (2012))**, polygon version, pairing half: in a regular tiling of a convex polygon by congruent triangles, if `a, b` are commensurable and `c` is not a rational
-- multiple of `a`, then every tile side of length `c` that has a polygon-interior point on its open segment lies on a side of a second tile on the other side of the line: the two tiles share that side.
-- Route: the maximal segment through the side starts at the end of the backward left chain (`exists_maxwalkR` for `-d`), a RIGHT tile also starts there (`ExtFan.right_start`: no T-junction start, no exterior sector,
-- convexity), the forward maximal segment is `exists_maxseg`, and the combinatorial half is `block_pair` (Lemma 4.5 + `Gamma_c` empty (Lemma 4.6) + count of `c`).  NOTE, UNAUDITED.
-- Credit: Laczkovich (DCG 48 (2012), Lemmas 4.5, 4.6, 4.8), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalRG10Block
import Erdos634.Draft.LaczFormalRG10Start

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

variable {N M : ℕ} [NeZero M]

theorem convPoly_convex (P : ConvPoly M) : Convex ℝ P.carrier := by
  have : P.carrier = ⋂ i : Fin M, {z : Plane | 0 ≤ cross2 (P.v (i + 1) - P.v i) (z - P.v i)} := by
    ext z; simp [ConvPoly.carrier]
  rw [this]
  exact convex_iInter fun i => halfplane_convex _ _

theorem vertex_of_crs_pos {T : Tri} {V : Plane} {p q : V2} (hspec : SectorSpec T V p q) (hc : 0 < crs p q) : ∃ k, T.pts k = V := by
  rcases hspec with ⟨k, hk, -⟩ | ⟨-, m, -, -, hq, -⟩
  · exact ⟨k, hk⟩
  · exfalso
    rw [hq] at hc
    unfold crs at hc; simp only at hc; nlinarith

/-- Reversal of a right chain into a left chain. -/
theorem walkR_rev {D : RegionDissection N} {d : V2} {X Y : Plane} {L : List (Fin N × Plane × Plane)} (W : WalkR D d X Y L) :
    ∃ L' : List (Fin N × Plane × Plane), WalkT D (neg2 d) Y X L' := by
  induction W with
  | nil X => exact ⟨[], WalkT.nil X⟩
  | @cons i X X' Y L hS W' ih =>
    obtain ⟨L'', hL''⟩ := ih
    refine ⟨L'' ++ [(i, X', X)], ?_⟩
    apply walkT_of_U
    rw [walkU_append]
    exact ⟨X', walkU_of_T hL'', WalkU.cons (by simpa [StepU] using hS) (WalkU.nil X)⟩

theorem walkT_cons_step {D : RegionDissection N} {d : V2} {X Y : Plane} {e : Fin N × Plane × Plane} {L : List (Fin N × Plane × Plane)}
    (W : WalkT D d X Y (e :: L)) : TriStep (D.tile e.1) d X e.2.2 ∧ e.2.1 = X := by
  obtain ⟨i, A, B⟩ := e
  cases W with
  | cons hS W' => exact ⟨hS, rfl⟩

/-- A left chain from `P` to `U` followed by a step at `U` lies inside every maximal left chain from `P`. -/
theorem walkT_unique_mem (D : RegionDissection N) [HasFansC D] {d : V2} {P U V : Plane} {i : Fin N} {L0 : List (Fin N × Plane × Plane)}
    (W0 : WalkT D d P U L0) (hS : TriStep (D.tile i) d U V) :
    ∀ {Y : Plane} {L1 : List (Fin N × Plane × Plane)}, WalkT D d P Y L1 → (∀ j U', ¬ TriStep (D.tile j) d Y U') → (i, U, V) ∈ L1 := by
  induction W0 with
  | nil X =>
    intro Y L1 W1 hmax
    cases W1 with
    | nil => exact absurd hS (hmax i V)
    | @cons i1 X1 X1' Y1 L1' hS1 W1' =>
      obtain ⟨hii, hVV⟩ := left_step_unique D hS hS1
      subst hii; subst hVV
      simp
  | @cons j X X' Z L hS0 W0' ih =>
    intro Y L1 W1 hmax
    cases W1 with
    | nil => exact absurd hS0 (hmax j X')
    | @cons i1 X1 X1' Y1 L1' hS1 W1' =>
      obtain ⟨hii, hVV⟩ := left_step_unique D hS0 hS1
      subst hii; subst hVV
      exact List.mem_cons_of_mem _ (ih hS W1' hmax)

theorem triStep_not_both {T : Tri} {d : V2} {U V : Plane} (h1 : TriStep T d U V) (h2 : TriStep T (neg2 d) V U) : False := by
  obtain ⟨kk, f, g, hk, hf, hfk, hgk, hgf, hpar, hleft⟩ := h1
  obtain ⟨kk', f', g', hk', hf', hfk', hgk', hgf', hpar', hleft'⟩ := h2
  have e1 : kk' = f := T.indep.injective (hk'.trans hf.symm)
  have e2 : f' = kk := T.indep.injective (hf'.trans hk.symm)
  have hg1 : g' ≠ f := by rw [← e1]; exact hgk'
  have hg2 : g' ≠ kk := by rw [← e2]; exact hgf'
  have hgg : g' = g := fin3_third g kk f g' hgk.symm hgf.symm hfk hg2 hg1
  rw [hgg] at hleft'
  have h0 := hpar.1
  unfold crs at hleft hleft' h0
  simp only [toV2_sub, neg2] at hleft hleft' h0
  nlinarith

/-- **Lemma 4.8 (Laczkovich, DCG 48 (2012)), polygon version, pairing.**  Let `a, b` be commensurable and `c` not a rational multiple of `a`.  If the tile `i` has the side `U V` of length `c` along
`d` (tile on the left) and one point of the open segment `U V` is interior to the polygon, then another tile `j` has the same side, on the other side of the line (`TriStep (tile j) (-d) V U`). -/
theorem lemma48_pair (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (Pg : ConvPoly M) (hreg : D.region = Pg.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (h : CaseC D idx) (hab : Comm (slen D 0) (slen D 1)) (hac : ¬ Comm (slen D 0) (slen D 2))
    {i : Fin N} {d : V2} {U V : Plane} (hS : TriStep (D.tile i) d U V) (hc : dist U V = slen D 2)
    {m : Plane} (hm : m ∈ openSegment ℝ U V) (hmi : m ∈ interior D.region) :
    ∃ j : Fin N, j ≠ i ∧ TriStep (D.tile j) (neg2 d) V U := by
  classical
  have hGc := gc_empty D Pg hreg idx h hab hac
  have hS' := hS
  obtain ⟨kk, f, g, hkk, hf, hfk, hgk, hgf, hpar, hleft⟩ := hS'
  have hd : d ≠ 0 := hpar.ne_right
  have hnd : neg2 d ≠ 0 := by
    intro h0
    apply hd
    have h1 : -d.1 = 0 := congrArg Prod.fst h0
    have h2 : -d.2 = 0 := congrArg Prod.snd h0
    exact Prod.ext (by simp only [Prod.fst_zero]; linarith) (by simp only [Prod.snd_zero]; linarith)
  have hUvert : ∃ j k, (D.tile j).pts k = U := ⟨i, kk, hkk⟩
  -- the backward left chain from `U`
  obtain ⟨P, L0, W0, hmaxP⟩ := exists_maxwalkR D.toRegionDissection hnd hUvert
  obtain ⟨L1, W1⟩ := walkR_rev W0
  rw [neg2_neg2'] at W1
  have WPV : WalkT D.toRegionDissection d P V (L1 ++ [(i, U, V)]) := by
    apply walkT_of_U
    rw [walkU_append]
    exact ⟨U, walkU_of_T W1, WalkU.cons (by simpa [StepU] using hS) (WalkU.nil V)⟩
  obtain ⟨e, rest, hel⟩ : ∃ e rest, L1 ++ [(i, U, V)] = e :: rest := List.exists_cons_of_ne_nil (by simp)
  rw [hel] at WPV
  obtain ⟨hS1, he1⟩ := walkT_cons_step WPV
  have hS1' := hS1
  obtain ⟨kk1, f1, g1, hk1, hf1, -⟩ := hS1'
  have hPv : ∃ j k, (D.tile j).pts k = P := ⟨e.1, kk1, hk1⟩
  obtain ⟨κ, _, ⟨F⟩⟩ := HasFansC.fans (D := D.toRegionDissection) P hPv
  have hmem : P ∈ (D.tile e.1).carrier := hk1 ▸ subset_convexHull ℝ _ ⟨kk1, rfl⟩
  set a : AtV D.toRegionDissection P := ⟨e.1, hmem⟩ with ha
  obtain ⟨kk', fl', hk', hp, hq⟩ := spec_corner_data (F.hspec a) ⟨kk1, hk1⟩
  have hpa : Par (F.p a) d := triStep_start hS1 kk' fl' hk' hp hq (F.hok a)
  have hca : 0 < crs (F.p a) (F.q a) := crs_pos_of_corner (F.hok a) (F.hspec a) ⟨kk', hk'⟩
  have hnoL : ∀ c : AtV D.toRegionDissection P, 0 < crs (F.p c) (F.q c) → ¬ Par (F.q c) (-d.1, -d.2) := by
    intro c hcc hqc
    obtain ⟨kc, hkc⟩ := vertex_of_crs_pos (F.hspec c) hcc
    obtain ⟨kk2, fl2, hk2, hp2, hq2⟩ := spec_corner_data (F.hspec c) ⟨kc, hkc⟩
    exact hmaxP _ _ (triStep_of_end (d := neg2 d) kk2 fl2 hk2 hp2 hq2 hcc hqc)
  -- an interior point ahead of `P` on the ray
  obtain ⟨c0, hc0, hcv⟩ := hpar.smul
  obtain ⟨a1, b1, ha1, hb1, hab1, hmeq⟩ := hm
  have hmU : m - U = b1 • (V - U) := by
    rw [← hmeq]
    have : a1 = 1 - b1 := by linarith
    subst this
    module
  have hmUv : toV2 (m - U) = (b1 * c0 * d.1, b1 * c0 * d.2) := by
    rw [hmU]
    have : toV2 (b1 • (V - U)) = (b1 * (toV2 (V - U)).1, b1 * (toV2 (V - U)).2) := by simp [toV2]
    rw [this, hcv]
    ext <;> simp <;> ring
  obtain ⟨TT, hTT0, hTT, -⟩ := walkT_progress W1
  have hmP : toV2 (m - P) = ((TT + b1 * c0) * d.1, (TT + b1 * c0) * d.2) := by
    rw [toV2_sub3 m U P, hmUv, hTT]
    ext <;> simp <;> ring
  have hPreg : P ∈ D.region := by
    rw [← D.toRegionDissection.covers]
    exact Set.mem_iUnion.mpr ⟨e.1, hmem⟩
  have hconv : Convex ℝ D.region := by rw [hreg]; exact convPoly_convex Pg
  have hint := F.tgt_zminus hconv hPreg (t0 := TT + b1 * c0) (by positivity) hmi hmP
  obtain ⟨s, hcs, hqs⟩ := F.right_start a hca hpa hnoL hint
  obtain ⟨ks, hks⟩ := vertex_of_crs_pos (F.hspec s) hcs
  obtain ⟨kk3, fl3, hk3, hp3, hq3⟩ := spec_corner_data (F.hspec s) ⟨ks, hks⟩
  have hr : ∃ j U', TriStep (D.tile j) (neg2 d) U' P := ⟨s.1, _, triStep_of_end kk3 fl3 hk3 hp3 hq3 hcs hqs⟩
  have hl : ∃ j U', TriStep (D.tile j) d P U' := ⟨e.1, _, hS1⟩
  obtain ⟨Y, LA, LB, wT, wR, -, -, hnoT, -⟩ := exists_maxseg D.toRegionDissection hd hPv hl hr
  -- the step of the tile `i` is in the left division
  have hmemLA : (i, U, V) ∈ LA := walkT_unique_mem D.toRegionDissection W1 hS wT hnoT
  obtain ⟨f', hf', hf1, hf2⟩ := block_pair D idx h hab hac hGc hd (bA := true) _ (X := P) (Y := Y) (LA := LA) (LB := LB) rfl (walkU_of_T wT) (walkU_of_R wR) (i, U, V) hmemLA hc
  have hstep := walkR_mem_step wR f' hf'
  have hstep' : TriStep (D.tile f'.1) (neg2 d) V U := by
    have e1 : f'.2.2 = V := hf2
    have e2 : f'.2.1 = U := hf1
    rw [e1, e2] at hstep
    exact hstep
  refine ⟨f'.1, ?_, hstep'⟩
  intro hji
  rw [hji] at hstep'
  exact triStep_not_both hS hstep'

/-- **Lemma 4.8 for a regular tiling of a convex polygon** (any `γ`). -/
theorem polytiling_lemma48 {N M : ℕ} [NeZero M] (T : PolyTiling N M) (hreg : RegularPQ T.C) (hab : Comm (slen T.C 0) (slen T.C 1))
    (hac : ¬ Comm (slen T.C 0) (slen T.C 2)) {i : Fin N} {d : V2} {U V : Plane} (hS : TriStep (T.C.tile i) d U V) (hc : dist U V = slen T.C 2)
    {m : Plane} (hm : m ∈ openSegment ℝ U V) (hmi : m ∈ interior T.C.region) :
    ∃ j : Fin N, j ≠ i ∧ TriStep (T.C.tile j) (neg2 d) V U := by
  classical
  obtain ⟨idx, hA, hcnt⟩ := hreg
  haveI : HasFansC T.C.toRegionDissection := hasFansC_poly _ T.P T.region_eq
  have hC : CaseC T.C idx := ⟨idx_dist_of_angle T.C idx hA, hA, fun X => hcnt X, notComb_c_of_comm (slen_pos T.C 2) hab hac⟩
  exact lemma48_pair T.C T.P T.region_eq idx hC hab hac hS hc hm hmi

end Erdos634.Draft.LaczFormal.RG
