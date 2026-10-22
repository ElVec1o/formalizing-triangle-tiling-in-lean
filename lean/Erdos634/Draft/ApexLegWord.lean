-- Draft/ApexLegWord.lean — clause (2) of apex placement at m = 1: the outer apex tiles lay `c` on
-- the legs (`lem:sidenob` + the γ-trap on the REAL leg chain), for EVERY coprime member, thin or
-- thick.  Discharges `ApexPlacement.LegFlanksC`, making `ApexPlacement.exists_hframe`
-- hypothesis-free beyond the target/model data (`exists_hframe_m1`).  Imported by All.lean (All.lean line 402: import Erdos634.Draft.ApexLegWord).
--
-- REDISCOVERY / REUSE LEDGER.  `leg_no_b` is `SideWalk.equal_side_no_b_of_gammatrap`'s chain
-- argument (copied: `chain_endpoints` + `ChainWalk.chain_walk` + `congruentDissection_gammatrap`),
-- with its one thin-only step `BaseBetaWalkArith.equal_side_no_b` (needs `2e² < f²`) replaced by
-- `SideNoB.side_no_b_uncond` (VERIFIED, no thinness), and its conclusion read edge by edge through
-- the chain's surjectivity onto `wallList` (so it is NOT the vacuous packed-count form flagged in
-- SideWalk's 2026-09-10 warning).  `dir`/`hker`/`hiso`/`hthird` are `WallDir.dirFun`,
-- `hker_wallFun`, `BaseWalkGeneral.hiso_wallFun'`, `WallThird.hthird_general` (corpus).  The second
-- leg uses `NormalPosition.relabelTarget` (same tiles, target relabelled by a transposition).
--
-- Build (scratch oleans; never .lake): ApexPlacement olean in $S, then
--   lake env bash -c 'LEAN_PATH=$S:$LEAN_PATH lean Erdos634/Draft/ApexLegWord.lean'
import Erdos634.SideWalk
import Erdos634.SideNoB
import Erdos634.WallDir
import Erdos634.WallThird
import Erdos634.BaseWalkGeneral
import Erdos634.NormalPosition
import Erdos634.Draft.ApexPlacement

namespace Erdos634.Draft.ApexLegWord

open Erdos634.Geometry Erdos634.Placement Erdos634.TilePlacement Erdos634.WallEndpoints
  Erdos634.BridgeC Erdos634.BaseBetaWalkArith

variable {N : ℕ}

open Erdos634.SideWall Erdos634.Geometry.Dissection Erdos634.TilePlacement in
/-- **No `b` on a real equal side, edge by edge — PROVED, every coprime member.**  For a real
congruent dissection whose side `k` runs from a `β` corner to the `3α` apex and has length `f³`
(model `(ef, b, f²)`, `b + e² = f²`), no tile edge lying on that side has length `b`. -/
theorem leg_no_b (D : CongruentDissection N) (α β γ : ℝ)
    (hαβ : α ≠ β) (hαγ : α ≠ γ) (hαπ : α ≠ Real.pi) (hα0 : α ≠ 0)
    (hβγ : β ≠ γ) (hβπ : β ≠ Real.pi) (hβ0 : β ≠ 0)
    (hγπ : γ ≠ Real.pi) (hγ0 : γ ≠ 0) (hπ0 : Real.pi ≠ 0)
    (hγdef : γ = 2 * α + β) (hrel : 3 * α + 2 * β = Real.pi)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (hscalenef : ∀ m m' : Fin 3, m ≠ m' → sideOpp D.model m ≠ sideOpp D.model m')
    (hα' : cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = α)
    (hβ' : cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = β)
    (hγ' : cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = γ)
    (k : Fin 3) (dir : Plane →ₗ[ℝ] ℝ)
    (hker : ∀ v : Plane, (wallFun D.target k).linear v = 0 → dir v = 0 → v = 0)
    (hdirab : dir (D.target.pts k) ≤ dir (D.target.pts (k + 1)))
    (hthird : ∀ p ∈ Erdos634.BaseChain.wallList D.toDissection (wallFun D.target k) 0,
      wallFun D.target k ((D.tile p.1).pts (p.2 + 2)) < 0)
    (hcornerbase : cornerAngle (D.target.pts (k + 1)) (D.target.pts k)
      (D.target.pts (k + 2)) = β)
    (hcornerapex : cornerAngle (D.target.pts (k + 1 + 1)) (D.target.pts (k + 1))
      (D.target.pts (k + 1 + 2)) = 3 * α)
    (hiso : ∀ p q : Plane, (wallFun D.target k) p = 0 → (wallFun D.target k) q = 0 →
      dist p q = |dir p - dir q|)
    (hN : 0 < N) (e0 f0 b0 : ℕ) (hef0 : e0 < f0) (hcop : Nat.Coprime e0 f0)
    (hb0 : b0 + e0 * e0 = f0 * f0)
    (hA : sideOpp D.model 0 = (e0 : ℝ) * f0)
    (hB : sideOpp D.model 1 = (b0 : ℝ))
    (hC : sideOpp D.model 2 = (f0 : ℝ) ^ 2)
    (hLen : dist (D.target.pts k) (D.target.pts (k + 1)) = (f0 : ℝ) ^ 3) :
    ∀ q ∈ Erdos634.BaseChain.wallList D.toDissection (wallFun D.target k) 0,
      dist ((D.tile q.1).pts q.2) ((D.tile q.1).pts (q.2 + 1)) ≠ sideOpp D.model 1 := by
  classical
  set g := wallFun D.target k with hgdef
  set a := D.target.pts k with hadef
  set b := D.target.pts (k + 1) with hbdef
  have hab : a ≠ b := by
    have h : ∀ x : Fin 3, x ≠ x + 1 := by decide
    exact Erdos634.TilePlacement.pts_ne D.target (h k)
  have hwall : ∀ y ∈ D.target.carrier, g y ≤ 0 := fun y hy => wallFun_le D.target k hy
  have hbase : segment ℝ a b ⊆ frontier D.target.carrier := by
    intro y hy
    exact edge_subset_frontier D.target k (by rw [Tri.edge]; exact hy)
  have hline : ∀ y ∈ segment ℝ a b, g y = 0 := by
    intro y hy
    exact wallFun_eq_zero D.target k (by rw [Tri.edge]; exact hy)
  have hface : ∀ y ∈ D.target.carrier, g y = 0 → y ∈ segment ℝ a b := by
    intro y hy h0
    have := wallFun_face D.target k hy h0
    rw [Tri.edge] at this
    exact this
  obtain ⟨pc, hpcmem, hpceq⟩ := congruentDissection_gammatrap hN D α β γ hαβ hαγ hαπ hα0 hβγ hβπ
    hβ0 hγπ hγ0 hπ0 hγdef hrel hirr hscalenef hα' hβ' hγ' k dir hker hdirab hthird hcornerbase
    hcornerapex
  obtain ⟨E, n, hneq, hn0, hwest0, heastlast, hjunc, hmem, hinj, hlba, hlbend, hnondeg, hsurj⟩ :=
    chain_endpoints hN D.toDissection g 0 dir hker hwall a b hab hdirab hbase hline hface hthird
  set L : ℕ → ℝ := fun m => Erdos634.OrientBridge.edgePos D.toDissection dir (E m) with hLdef
  set R : ℕ → ℝ := fun m => Erdos634.ChainInstance.edgeEnd D.toDissection dir (E m) with hRdef
  have hRL : ∀ m, m < n → R m - L m = sideOpp D.model 0 ∨ R m - L m = sideOpp D.model 1 ∨
      R m - L m = sideOpp D.model 2 := by
    intro m hm
    have hwm := (Erdos634.BaseChain.mem_wallList D.toDissection g 0 (E m)).mp (hmem m hm)
    obtain ⟨j, hj⟩ := exists_matching_side D (E m).1 (E m).2
    have hdist : dist ((D.tile (E m).1).pts (E m).2) ((D.tile (E m).1).pts ((E m).2 + 1))
        = R m - L m := by
      rw [hiso _ _ hwm.1 hwm.2]
      show |dir ((D.tile (E m).1).pts (E m).2) - dir ((D.tile (E m).1).pts ((E m).2 + 1))|
        = Erdos634.ChainInstance.edgeEnd D.toDissection dir (E m)
          - Erdos634.OrientBridge.edgePos D.toDissection dir (E m)
      rw [show Erdos634.OrientBridge.edgePos D.toDissection dir (E m)
            = min (dir ((D.tile (E m).1).pts (E m).2)) (dir ((D.tile (E m).1).pts ((E m).2 + 1)))
          from rfl,
        show Erdos634.ChainInstance.edgeEnd D.toDissection dir (E m)
            = max (dir ((D.tile (E m).1).pts (E m).2)) (dir ((D.tile (E m).1).pts ((E m).2 + 1)))
          from rfl]
      rcases le_total (dir ((D.tile (E m).1).pts (E m).2))
          (dir ((D.tile (E m).1).pts ((E m).2 + 1))) with h | h
      · rw [min_eq_left h, max_eq_right h, abs_of_nonpos (by linarith)]; ring
      · rw [min_eq_right h, max_eq_left h, abs_of_nonneg (by linarith)]
    rw [← hdist, hj]
    fin_cases j
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
  have hscalene : sideOpp D.model 0 ≠ sideOpp D.model 1 ∧ sideOpp D.model 0 ≠ sideOpp D.model 2 ∧
      sideOpp D.model 1 ≠ sideOpp D.model 2 :=
    ⟨hscalenef 0 1 (by decide), hscalenef 0 2 (by decide), hscalenef 1 2 (by decide)⟩
  have hchain := Erdos634.ChainWalk.chain_walk n hn0 L R (sideOpp D.model 0) (sideOpp D.model 1)
    (sideOpp D.model 2) hscalene.1 hscalene.2.1 hscalene.2.2
    (fun j hj => by
      show Erdos634.ChainInstance.edgeEnd D.toDissection dir (E j)
        = Erdos634.OrientBridge.edgePos D.toDissection dir (E (j + 1))
      rw [← dir_edgeEast, ← dir_edgeWest, hjunc j hj])
    (fun m hm => by
      rw [Finset.mem_range] at hm
      simp only [Finset.mem_insert, Finset.mem_singleton]
      exact hRL m hm)
  set PcL := ((Finset.range n).filter (fun j => R j - L j = sideOpp D.model 0)).card with hPcdef
  set QcL := ((Finset.range n).filter (fun j => R j - L j = sideOpp D.model 1)).card with hQcdef
  set RcL := ((Finset.range n).filter (fun j => R j - L j = sideOpp D.model 2)).card with hRcdef
  have hRb : R (n - 1) = dir b := by
    show Erdos634.ChainInstance.edgeEnd D.toDissection dir (E (n - 1)) = dir b
    rw [← dir_edgeEast, heastlast]
  have hL0 : L 0 = dir a := by
    show Erdos634.OrientBridge.edgePos D.toDissection dir (E 0) = dir a
    rw [← dir_edgeWest, hwest0]
  have heq : dist a b = PcL * sideOpp D.model 0 + QcL * sideOpp D.model 1 + RcL * sideOpp D.model 2 := by
    rw [hiso a b (hline a (left_mem_segment ℝ a b)) (hline b (right_mem_segment ℝ a b))]
    rw [abs_of_nonpos (by linarith)]
    rw [← hchain, hRb, hL0]
    ring

  have hcast : PcL * (e0 * f0) + QcL * b0 + RcL * (f0 * f0) = f0 * f0 * f0 := by
    have hr : ((PcL * (e0 * f0) + QcL * b0 + RcL * (f0 * f0) : ℕ) : ℝ)
        = ((f0 * f0 * f0 : ℕ) : ℝ) := by
      rw [hA, hB, hC, hLen] at heq
      push_cast
      linear_combination -heq
    exact_mod_cast hr
  have hnc1 : 1 ≤ RcL := by
    obtain ⟨ic, hiclt, hiceq⟩ := hsurj pc hpcmem
    subst hiceq
    apply Erdos634.ChainWalk.count_pos n (fun j => R j - L j) (sideOpp D.model 2) ic
      (Finset.mem_range.mpr hiclt)
    have hwm := (Erdos634.BaseChain.mem_wallList D.toDissection g 0 (E ic)).mp hpcmem
    have hdist : dist ((D.tile (E ic).1).pts (E ic).2) ((D.tile (E ic).1).pts ((E ic).2 + 1))
        = R ic - L ic := by
      rw [hiso _ _ hwm.1 hwm.2]
      show |dir ((D.tile (E ic).1).pts (E ic).2) - dir ((D.tile (E ic).1).pts ((E ic).2 + 1))|
        = Erdos634.ChainInstance.edgeEnd D.toDissection dir (E ic)
          - Erdos634.OrientBridge.edgePos D.toDissection dir (E ic)
      rw [show Erdos634.OrientBridge.edgePos D.toDissection dir (E ic)
            = min (dir ((D.tile (E ic).1).pts (E ic).2))
                (dir ((D.tile (E ic).1).pts ((E ic).2 + 1)))
          from rfl,
        show Erdos634.ChainInstance.edgeEnd D.toDissection dir (E ic)
            = max (dir ((D.tile (E ic).1).pts (E ic).2))
                (dir ((D.tile (E ic).1).pts ((E ic).2 + 1)))
          from rfl]
      rcases le_total (dir ((D.tile (E ic).1).pts (E ic).2))
          (dir ((D.tile (E ic).1).pts ((E ic).2 + 1))) with h | h
      · rw [min_eq_left h, max_eq_right h, abs_of_nonpos (by linarith)]; ring
      · rw [min_eq_right h, max_eq_left h, abs_of_nonneg (by linarith)]
    rw [← hdist, hpceq]

  have hQc0 : QcL = 0 := Erdos634.SideNoB.side_no_b_uncond hcop hef0 hb0 hcast hnc1
  intro q hq hqb
  obtain ⟨iq, hiqlt, hiqeq⟩ := hsurj q hq
  subst hiqeq
  have hwm := (Erdos634.BaseChain.mem_wallList D.toDissection g 0 (E iq)).mp hq
  have hdist : dist ((D.tile (E iq).1).pts (E iq).2) ((D.tile (E iq).1).pts ((E iq).2 + 1))
      = R iq - L iq := by
    rw [hiso _ _ hwm.1 hwm.2]
    show |dir ((D.tile (E iq).1).pts (E iq).2) - dir ((D.tile (E iq).1).pts ((E iq).2 + 1))|
      = Erdos634.ChainInstance.edgeEnd D.toDissection dir (E iq)
        - Erdos634.OrientBridge.edgePos D.toDissection dir (E iq)
    rw [show Erdos634.OrientBridge.edgePos D.toDissection dir (E iq)
          = min (dir ((D.tile (E iq).1).pts (E iq).2))
              (dir ((D.tile (E iq).1).pts ((E iq).2 + 1)))
        from rfl,
      show Erdos634.ChainInstance.edgeEnd D.toDissection dir (E iq)
          = max (dir ((D.tile (E iq).1).pts (E iq).2))
              (dir ((D.tile (E iq).1).pts ((E iq).2 + 1)))
        from rfl]
    rcases le_total (dir ((D.tile (E iq).1).pts (E iq).2))
        (dir ((D.tile (E iq).1).pts ((E iq).2 + 1))) with h | h
    · rw [min_eq_left h, max_eq_right h, abs_of_nonpos (by linarith)]; ring
    · rw [min_eq_right h, max_eq_left h, abs_of_nonneg (by linarith)]
  have hmemQ : iq ∈ (Finset.range n).filter (fun j => R j - L j = sideOpp D.model 1) := by
    rw [Finset.mem_filter]; exact ⟨Finset.mem_range.mpr hiqlt, by rw [← hdist]; exact hqb⟩
  have : 0 < QcL := Finset.card_pos.mpr ⟨iq, hmemQ⟩
  omega


/-! ## Clause (2) for a real dissection -/

open Erdos634.SideWall Erdos634.Draft.ApexPlacement Erdos634.Draft.CornerAdjacency

/-- A point on the line through two vertices has zero barycentric coordinate for the third. -/
theorem coord_line_zero (T : Tri) {j a b : Fin 3} (ha : j ≠ a) (hb : j ≠ b) (t : ℝ) :
    T.basis.coord j (T.pts a + t • (T.pts b - T.pts a)) = 0 := by
  have : T.pts a + t • (T.pts b - T.pts a) = AffineMap.lineMap (T.pts a) (T.pts b) t := by
    rw [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, add_comm]
  rw [this, AffineMap.apply_lineMap, Erdos634.Draft.NearBaseVertex.coord_other T ha,
    Erdos634.Draft.NearBaseVertex.coord_other T hb, AffineMap.lineMap_same_apply]

/-- `dirFun` increases along its side (the `hdirab` of the side-walk theorems). -/
theorem hdirab_dirFun (T : Tri) (k : Fin 3) :
    (dirFun T k).linear (T.pts k) ≤ (dirFun T k).linear (T.pts (k + 1)) := by
  have h1 : (dirFun T k).linear (T.pts (k + 1)) - (dirFun T k).linear (T.pts k)
      = dirFun T k (T.pts (k + 1)) - dirFun T k (T.pts k) := by
    rw [← map_sub, ← vsub_eq_sub, AffineMap.linearMap_vsub, vsub_eq_sub]
  have h2 : dirFun T k (T.pts (k + 1)) - dirFun T k (T.pts k) = sideOpp T (k + 2) := by
    show sideOpp T (k + 2) * T.basis.coord (k + 1) (T.pts (k + 1))
      - sideOpp T (k + 2) * T.basis.coord (k + 1) (T.pts k) = sideOpp T (k + 2)
    rw [Erdos634.Draft.NearBaseVertex.coord_self,
      Erdos634.Draft.NearBaseVertex.coord_other T (show k + 1 ≠ k by fin_cases k <;> decide)]
    ring
  have hpos : 0 ≤ sideOpp T (k + 2) := dist_nonneg
  linarith

theorem flank_edge {T : Tri} {m : Fin 3} {x U W : Plane} (hm : T.pts m = x)
    (h : IsFlankPair T m x U W) :
    ∃ j : Fin 3, (T.pts j = x ∧ T.pts (j + 1) = x + U) ∨
      (T.pts j = x + U ∧ T.pts (j + 1) = x) := by
  rcases h with ⟨rfl, -⟩ | ⟨rfl, -⟩
  · exact ⟨m, Or.inl ⟨hm, by abel⟩⟩
  · refine ⟨m + 2, Or.inr ⟨by abel, ?_⟩⟩
    rw [show m + 2 + 1 = m by fin_cases m <;> rfl]; exact hm

/-- **One leg: the apex flank along the side `k' → k'+1` (base corner → apex) is a `c`.** -/
theorem leg_flank_c_side (D : CongruentDissection N) {e f : ℕ} {α β γ : ℝ}
    (hco : Nat.Coprime e f) (he : 2 ≤ e) (hef : e < f)
    (hM : HalfTurnR3R4Glue.ModelDataE D e f α β γ) (hAng : MarchSlots.AngleData α β γ)
    (k' : Fin 3)
    (hcornerbase : cornerAngle (D.target.pts (k' + 1)) (D.target.pts k')
      (D.target.pts (k' + 2)) = β)
    (hcornerapex : cornerAngle (D.target.pts (k' + 1 + 1)) (D.target.pts (k' + 1))
      (D.target.pts (k' + 1 + 2)) = 3 * α)
    (hLen : dist (D.target.pts k') (D.target.pts (k' + 1)) = (f : ℝ) ^ 3)
    {i : Fin N} {m : Fin 3} {U W : Plane} {S : ℝ}
    (hm : (D.tile i).pts m = D.target.pts (k' + 1))
    (hUW : IsFlankPair (D.tile i) m (D.target.pts (k' + 1)) U W)
    (hS : 0 < S) (hU : D.target.pts k' - D.target.pts (k' + 1) = S • U) :
    ‖U‖ = (f : ℝ) ^ 2 := by
  classical
  obtain ⟨hαβ, hαγ, hαπ, hα0, hβγ, hβπ, hβ0, hγπ, hγ0, -, -, -⟩ := angle_facts hAng
  have hN : 0 < N := Fin.pos i
  obtain ⟨hab, hac, hbc⟩ := HalfTurnR3R4Glue.sides_distinct hco he hef
  have h01 : sideOpp D.model 0 ≠ sideOpp D.model 1 := by rw [hM.hs0, hM.hs1]; exact hab
  have h02 : sideOpp D.model 0 ≠ sideOpp D.model 2 := by rw [hM.hs0, hM.hs2]; exact hac
  have h12 : sideOpp D.model 1 ≠ sideOpp D.model 2 := by rw [hM.hs1, hM.hs2]; exact hbc
  have hscalene : ∀ j j' : Fin 3, j ≠ j' → sideOpp D.model j ≠ sideOpp D.model j' := by
    intro j j' hjj'
    fin_cases j <;> fin_cases j' <;> first | exact absurd rfl hjj' | exact h01 | exact h02 | exact h12 | exact h01.symm | exact h02.symm | exact h12.symm
  have hee : e * e ≤ f * f := Nat.mul_le_mul hef.le hef.le
  have hthirdD : ∀ p ∈ Erdos634.BaseChain.wallList D.toDissection (wallFun D.target k') 0,
      wallFun D.target k' ((D.tile p.1).pts (p.2 + 2)) < 0 :=
    hthird_general D.toDissection (wallFun D.target k') 0 (wallFun_linear_ne_zero D.target k')
      (fun y hy => by simpa using wallFun_le D.target k' hy)
  have hnob := leg_no_b D α β γ hαβ hαγ hαπ hα0 hβγ hβπ hβ0 hγπ hγ0 Real.pi_ne_zero hAng.hγdef
    hAng.hrel hAng.hirr hscalene hM.hα' hM.hβ' hM.hγ' k' (dirFun D.target k').linear
    (hker_wallFun D.target k') (hdirab_dirFun D.target k') hthirdD hcornerbase hcornerapex
    (hiso_wallFun' D.target k') hN e f (f * f - e * e) hef hco (Nat.sub_add_cancel hee)
    hM.hs0 (by rw [hM.hs1]; push_cast [Nat.cast_sub hee]; ring) hM.hs2 hLen
  -- the flank edge lies on the side
  set A := D.target.pts (k' + 1) with hAdef
  have hS' : 0 < S⁻¹ := inv_pos.mpr hS
  have hUe : A + U = A + S⁻¹ • (D.target.pts k' - A) := by
    rw [hU, smul_smul, inv_mul_cancel₀ hS.ne', one_smul]
  have hgA : wallFun D.target k' A = 0 := by
    simp only [wallFun, AffineMap.coe_neg, Pi.neg_apply, neg_eq_zero]
    exact Erdos634.Draft.NearBaseVertex.coord_other D.target
      (show k' + 2 ≠ k' + 1 by fin_cases k' <;> decide)
  have hgU : wallFun D.target k' (A + U) = 0 := by
    rw [hUe]
    simp only [wallFun, AffineMap.coe_neg, Pi.neg_apply, neg_eq_zero]
    exact coord_line_zero D.target (show k' + 2 ≠ k' + 1 by fin_cases k' <;> decide)
      (show k' + 2 ≠ k' by fin_cases k' <;> decide) _
  obtain ⟨j, hj⟩ := flank_edge hm hUW
  have hq : ((i, j) : Fin N × Fin 3) ∈
      Erdos634.BaseChain.wallList D.toDissection (wallFun D.target k') 0 := by
    rw [Erdos634.BaseChain.mem_wallList]
    rcases hj with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨by simp only; rw [h1]; exact hgA, by simp only; rw [h2]; exact hgU⟩
    · exact ⟨by simp only; rw [h1]; exact hgU, by simp only; rw [h2]; exact hgA⟩
  have hlen : dist ((D.tile i).pts j) ((D.tile i).pts (j + 1)) = ‖U‖ := by
    rcases hj with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2, dist_comm, dist_eq_norm, add_sub_cancel_left]
    · rw [h1, h2, dist_eq_norm, add_sub_cancel_left]
  have hnb := hnob (i, j) hq
  simp only at hnb
  rw [hlen] at hnb
  -- the flank is `b` or `c`
  obtain ⟨-, -, -, -, -, -, -, hAt⟩ :=
    apex_three_tiles D hAng hM.hα' hM.hβ' hM.hγ' (k' + 1) hcornerapex
  have hAmem : A ∈ (D.tile i).carrier := by
    rw [← hm]; exact subset_convexHull ℝ _ (Set.mem_range_self m)
  have hi := (hAt i hAmem).1
  have he0 : (0 : ℝ) < e := by exact_mod_cast (show 0 < e by omega)
  have hf0 : (0 : ℝ) < f := by exact_mod_cast (show 0 < f by omega)
  have ha0 : (e : ℝ) * f ≠ 0 := mul_ne_zero he0.ne' hf0.ne'
  rcases flank_norms_bc D hM.hs0 hM.hs1 hM.hs2 ha0
      hAng hM.hα' hM.hβ' hM.hγ' (k' + 1) hcornerapex hm hUW hi with ⟨h1, -⟩ | ⟨h1, -⟩
  · exact absurd (h1.trans hM.hs1.symm) hnb
  · exact h1

/-- **Clause (2) at `m = 1` — PROVED for every coprime member `2 ≤ e < f` (thin AND thick).**
In a real congruent dissection of the `m = 1` base-β target (legs `f³`, apex `3α`, base corners
`β`), every apex flank lying along a leg is a `c`. -/
theorem legFlanksC_m1 (D : CongruentDissection N) {e f : ℕ} {α β γ : ℝ}
    (hco : Nat.Coprime e f) (he : 2 ≤ e) (hef : e < f)
    (hM : HalfTurnR3R4Glue.ModelDataE D e f α β γ) (hAng : MarchSlots.AngleData α β γ)
    (k : Fin 3)
    (hcorner : cornerAngle (D.target.pts (k + 1)) (D.target.pts k) (D.target.pts (k + 2))
      = 3 * α)
    (hβ1 : cornerAngle (D.target.pts (k + 2)) (D.target.pts (k + 1)) (D.target.pts k) = β)
    (hβ2 : cornerAngle (D.target.pts k) (D.target.pts (k + 2)) (D.target.pts (k + 1)) = β)
    (hleg1 : dist (D.target.pts k) (D.target.pts (k + 1)) = (f : ℝ) ^ 3)
    (hleg2 : dist (D.target.pts k) (D.target.pts (k + 2)) = (f : ℝ) ^ 3) :
    LegFlanksC D k ((f : ℝ) ^ 2) := by
  classical
  intro i m U W l S hm hUW hl hS hU
  have e1 : k + 2 + 1 = k := by fin_cases k <;> rfl
  have e2 : k + 2 + 2 = k + 1 := by fin_cases k <;> rfl
  have e3 : k + 2 + 1 + 1 = k + 1 := by fin_cases k <;> rfl
  have e4 : k + 2 + 1 + 2 = k + 2 := by fin_cases k <;> rfl
  have e5 : k + 1 + 1 = k + 2 := by fin_cases k <;> rfl
  have e6 : k + 1 + 2 = k := by fin_cases k <;> rfl
  have hl' : l = k + 1 ∨ l = k + 2 := by
    fin_cases k <;> fin_cases l <;> simp_all
  rcases hl' with rfl | rfl
  · -- the leg `k → k+1`: relabel the target by the transposition `(k, k+1)`
    let σ : Equiv.Perm (Fin 3) := Equiv.swap k (k + 1)
    let D' : CongruentDissection N :=
      { toDissection := Erdos634.NormalPosition.relabelTarget D.toDissection σ
        model := D.model
        tiles_congruent := D.tiles_congruent }
    have hp0 : D'.target.pts k = D.target.pts (k + 1) := by
      show D.target.pts (σ k) = _; simp [σ]
    have hp1 : D'.target.pts (k + 1) = D.target.pts k := by
      show D.target.pts (σ (k + 1)) = _; simp [σ]
    have hp2 : D'.target.pts (k + 2) = D.target.pts (k + 2) := by
      show D.target.pts (σ (k + 2)) = _
      rw [Equiv.swap_apply_of_ne_of_ne (by fin_cases k <;> decide) (by fin_cases k <;> decide)]
    have hM' : HalfTurnR3R4Glue.ModelDataE D' e f α β γ :=
      ⟨hM.hs0, hM.hs1, hM.hs2, hM.hα', hM.hβ', hM.hγ'⟩
    have hb' : cornerAngle (D'.target.pts (k + 1)) (D'.target.pts k) (D'.target.pts (k + 2))
        = β := by
      rw [hp0, hp1, hp2, cornerAngle, EuclideanGeometry.angle_comm]; exact hβ1
    have ha' : cornerAngle (D'.target.pts (k + 1 + 1)) (D'.target.pts (k + 1))
        (D'.target.pts (k + 1 + 2)) = 3 * α := by
      rw [e5, e6, hp1, hp2, hp0, cornerAngle, EuclideanGeometry.angle_comm]; exact hcorner
    have hL' : dist (D'.target.pts k) (D'.target.pts (k + 1)) = (f : ℝ) ^ 3 := by
      rw [hp0, hp1, dist_comm]; exact hleg1
    have hm' : (D'.tile i).pts m = D'.target.pts (k + 1) := by rw [hp1]; exact hm
    have hUW' : IsFlankPair (D'.tile i) m (D'.target.pts (k + 1)) U W := by rw [hp1]; exact hUW
    have hU' : D'.target.pts k - D'.target.pts (k + 1) = S • U := by rw [hp0, hp1]; exact hU
    exact leg_flank_c_side D' hco he hef hM' hAng k hb' ha' hL' hm' hUW' hS hU'
  · -- the leg `k+2 → k`
    have hb' : cornerAngle (D.target.pts (k + 2 + 1)) (D.target.pts (k + 2))
        (D.target.pts (k + 2 + 2)) = β := by rw [e1, e2]; exact hβ2
    have ha' : cornerAngle (D.target.pts (k + 2 + 1 + 1)) (D.target.pts (k + 2 + 1))
        (D.target.pts (k + 2 + 1 + 2)) = 3 * α := by rw [e3, e1]; exact hcorner
    have hL' : dist (D.target.pts (k + 2)) (D.target.pts (k + 2 + 1)) = (f : ℝ) ^ 3 := by
      rw [e1, dist_comm]; exact hleg2
    have hm' : (D.tile i).pts m = D.target.pts (k + 2 + 1) := by rw [e1]; exact hm
    have hUW' : IsFlankPair (D.tile i) m (D.target.pts (k + 2 + 1)) U W := by rw [e1]; exact hUW
    have hU' : D.target.pts (k + 2) - D.target.pts (k + 2 + 1) = S • U := by rw [e1]; exact hU
    exact leg_flank_c_side D hco he hef hM hAng (k + 2) hb' ha' hL' hm' hUW' hS hU'

/-- **THE FRAME FROM A REAL `m = 1` DISSECTION, clause (2) discharged — PROVED.**  For every coprime
`2 ≤ e ≤ f − 2` and every congruent dissection of the `m = 1` base-β target by the tile
`(ef, f² − e², f²)` (given as: apex `k` with corner `3α`, base corners `β`, legs `f³`, base
`e(3f² − e²)`; `ModelDataE`, `AngleData`), the frame `HFrame` of branch (H) exists. -/
theorem exists_hframe_m1 (D : CongruentDissection N) {e f : ℕ} {α β γ : ℝ}
    (hco : Nat.Coprime e f) (he : 2 ≤ e) (hef : e + 2 ≤ f)
    (hM : HalfTurnR3R4Glue.ModelDataE D e f α β γ) (hAng : MarchSlots.AngleData α β γ)
    (k : Fin 3)
    (hcorner : cornerAngle (D.target.pts (k + 1)) (D.target.pts k) (D.target.pts (k + 2))
      = 3 * α)
    (hβ1 : cornerAngle (D.target.pts (k + 2)) (D.target.pts (k + 1)) (D.target.pts k) = β)
    (hβ2 : cornerAngle (D.target.pts k) (D.target.pts (k + 2)) (D.target.pts (k + 1)) = β)
    (hleg1 : dist (D.target.pts k) (D.target.pts (k + 1)) = (f : ℝ) ^ 3)
    (hleg2 : dist (D.target.pts k) (D.target.pts (k + 2)) = (f : ℝ) ^ 3)
    (hbase : dist (D.target.pts (k + 1)) (D.target.pts (k + 2))
      = (e : ℝ) * (3 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2)) :
    Nonempty (HalfTurnR3R4Glue.HFrame D e f α β γ) :=
  exists_hframe D hco he hef hM hAng k hcorner hleg1 hleg2 hbase
    (legFlanksC_m1 D hco he (by omega) hM hAng k hcorner hβ1 hβ2 hleg1 hleg2)

/-- `exists_hframe_m1` with the frame's cone coordinates (`ApexPlacement.FrameCoords`). -/
theorem exists_hframe_coords_m1 (D : CongruentDissection N) {e f : ℕ} {α β γ : ℝ}
    (hco : Nat.Coprime e f) (he : 2 ≤ e) (hef : e + 2 ≤ f)
    (hM : HalfTurnR3R4Glue.ModelDataE D e f α β γ) (hAng : MarchSlots.AngleData α β γ)
    (k : Fin 3)
    (hcorner : cornerAngle (D.target.pts (k + 1)) (D.target.pts k) (D.target.pts (k + 2))
      = 3 * α)
    (hβ1 : cornerAngle (D.target.pts (k + 2)) (D.target.pts (k + 1)) (D.target.pts k) = β)
    (hβ2 : cornerAngle (D.target.pts k) (D.target.pts (k + 2)) (D.target.pts (k + 1)) = β)
    (hleg1 : dist (D.target.pts k) (D.target.pts (k + 1)) = (f : ℝ) ^ 3)
    (hleg2 : dist (D.target.pts k) (D.target.pts (k + 2)) = (f : ℝ) ^ 3)
    (hbase : dist (D.target.pts (k + 1)) (D.target.pts (k + 2))
      = (e : ℝ) * (3 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2)) :
    ∃ F : HalfTurnR3R4Glue.HFrame D e f α β γ, FrameCoords F :=
  exists_hframe_coords D hco he hef hM hAng k hcorner hleg1 hleg2 hbase
    (legFlanksC_m1 D hco he (by omega) hM hAng k hcorner hβ1 hβ2 hleg1 hleg2)

end Erdos634.Draft.ApexLegWord

#print axioms Erdos634.Draft.ApexLegWord.leg_no_b
#print axioms Erdos634.Draft.ApexLegWord.leg_flank_c_side
#print axioms Erdos634.Draft.ApexLegWord.legFlanksC_m1
#print axioms Erdos634.Draft.ApexLegWord.exists_hframe_m1
#print axioms Erdos634.Draft.ApexLegWord.exists_hframe_coords_m1
