-- Draft/LaczFormalRG4GkHead.lean -- Case IV (gamma = pi/3): Lemma 8.1(i), the `Gamma_k` part, for a dissection of a convex polygon and arbitrary tile angles with `alpha + beta = 2 gamma = 2 pi/3`.
-- The head `X` of an edge of `Gamma_k` is the tail of an edge of `Gamma_a` or of `Gamma_k`.  Weight-free replacement of `LaczFormalGraphGk.gk_head_out`
-- (which was for the three equilateral-target tiles only): collinearity of rays is decided by the type counts of blocks (`RegFan.colG`, `block_eq`).
-- UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), proof of Lemma 8.1), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalRG4GkFan

open scoped Classical
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

variable {N M : ℕ} [NeZero M]

section CD2
variable (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3)) {X : Plane} {κ : Type} [Fintype κ]
  (F : ExtFan D.toRegionDissection X κ) (hcor : ∀ x : AtV D.toRegionDissection X, 0 < crs (F.p x) (F.q x))

include hcor

/-- **No collinear block ⇒ `NoBack`** (weight-free). -/
theorem noBack_of_nocolG (hidxA : ∀ i v, D.model.angleAt (idx i v) = (D.tile i).angleAt v)
    (hnc : NotComb (slen D 0) (slen D 1) (slen D 2)) (hγ : D.model.angleAt 2 = Real.pi / 3)
    (hαβ : D.model.angleAt 0 + D.model.angleAt 1 = 2 * Real.pi / 3)
    (hprof : (cnt D idx X 0 = 3 ∧ cnt D idx X 1 = 3 ∧ cnt D idx X 2 = 0) ∨ (cnt D idx X 0 = 2 ∧ cnt D idx X 1 = 2 ∧ cnt D idx X 2 = 2))
    (hemp : IsEmpty κ) (b i : ℕ) (hi : i < Fintype.card (AtV D.toRegionDissection X))
    (hcol : RegFan.colG (lst D idx F hcor hemp b) i = false) :
    NoBack D.toRegionDissection (F.q (tl F hemp (b + (i + Fintype.card (AtV D.toRegionDissection X) - 1) % Fintype.card (AtV D.toRegionDissection X)))) X := by
  classical
  apply F.noBack_of_none
  intro s
  have hp : ∀ s' : AtV D.toRegionDissection X, ¬ Par (F.p s') (neg2 (F.q (tl F hemp (b + (i + Fintype.card (AtV D.toRegionDissection X) - 1) % Fintype.card (AtV D.toRegionDissection X))))) := by
    intro s' h
    have := opp_colG D idx F hcor hidxA hnc hγ hαβ hprof hemp b i hi s' h
    rw [hcol] at this
    exact absurd this (by simp)
  refine ⟨hp s, fun h => ?_⟩
  obtain ⟨j0, -, hj0⟩ := tl_surj F hemp s
  have h1 := tl_adj F hemp j0
  rw [hj0] at h1
  exact hp _ (h1.trans h)

end CD2

/-- **Lemma 8.1(i), `Γ_k` part, for a dissection of a convex polygon, weight-free**: the head `X` of an edge of `Γ_k` is the tail of an edge of `Γ_a` or of `Γ_k`
(`γ = π/3`, regular counts, `a` not a nonnegative rational combination of `b, c`). -/
theorem gk_head_out' (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3))
    (hidx : ∀ i k k', dist ((D.tile i).pts k) ((D.tile i).pts k') = dist (D.model.pts (idx i k)) (D.model.pts (idx i k')))
    (hidxA : ∀ i v, D.model.angleAt (idx i v) = (D.tile i).angleAt v)
    (hnc : NotComb (slen D 0) (slen D 1) (slen D 2)) (hab : slen D 0 ≠ slen D 1) (hac : slen D 0 ≠ slen D 2)
    (hγ : D.model.angleAt 2 = Real.pi / 3) (hαβ : D.model.angleAt 0 + D.model.angleAt 1 = 2 * Real.pi / 3)
    {Z X : Plane} (hE : GkEdge D.toRegionDissection idx Z X) (hreg' : cnt D idx X 0 = cnt D idx X 1) :
    (∃ H', GaEdge D.toRegionDissection (slen D 0) X H') ∨ ∃ Z', GkEdge D.toRegionDissection idx X Z' := by
  classical
  obtain ⟨F, hcor, hcard6, hcls⟩ := gk_fan_full' D P hreg idx hidxA hγ hαβ hE hreg'
  have hemp : IsEmpty Empty := inferInstance
  obtain ⟨n, e1, e2, e3, e4⟩ := gk_adj D idx F hcor hemp hE
  set l := lst D idx F hcor hemp n with hl
  have hlen : l.length = 6 := by rw [hl, lst_length, hcard6]
  have hlt := lst_lt D idx F hcor hemp n
  have hc0 : RegFan.cnt l 0 = cnt D idx X 0 := lst_cnt D idx F hcor hemp n 0
  have hc1 : RegFan.cnt l 1 = cnt D idx X 1 := lst_cnt D idx F hcor hemp n 1
  have hc2 : RegFan.cnt l 2 = cnt D idx X 2 := lst_cnt D idx F hcor hemp n 2
  have hL1 : RegFan.Lc l 1 = cdcode D idx F hcor (tl F hemp n) := by
    unfold RegFan.Lc; rw [hlen]
    have := lst_getD D idx F hcor hemp n 0 (by rw [hcard6]; norm_num)
    simpa using this
  have hR1 : RegFan.Rc l 1 = cdcode D idx F hcor (tl F hemp (n + 1)) := by
    unfold RegFan.Rc; rw [hlen]
    have := lst_getD D idx F hcor hemp n 1 (by rw [hcard6]; norm_num)
    simpa using this
  have hany : (List.range 6).any (fun i => RegFan.tT (RegFan.Lc l i) == 1 && RegFan.tT (RegFan.Rc l i) == 1 &&
      RegFan.tW (RegFan.Lc l i) == 2 && RegFan.tU (RegFan.Rc l i) == 2) = true := by
    rw [List.any_eq_true]
    refine ⟨1, by simp, ?_⟩
    obtain ⟨a1, -, a3, -⟩ := cdcode_spec D idx F hcor (tl F hemp n)
    obtain ⟨b1, b2, -, -⟩ := cdcode_spec D idx F hcor (tl F hemp (n + 1))
    simp only [hL1, hR1, a1, a3, b1, b2, e1, e2, e3, e4, Bool.and_eq_true, beq_iff_eq]
    simp
  have hhyp : (RegFan.fullHyp333 l || RegFan.fullHyp222 l) = true := by
    rcases hcls with ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩
    · have : RegFan.fullHyp333 l = true := by
        unfold RegFan.fullHyp333
        rw [hc0, hc1, hc2, h0, h1, h2]
        simpa [RegFan.fullHyp333] using hany
      simp [this]
    · have : RegFan.fullHyp222 l = true := by
        unfold RegFan.fullHyp222
        rw [hc0, hc1, hc2, h0, h1, h2]
        simpa [RegFan.fullHyp222] using hany
      simp [this]
  have hconcl := RegFan.full_fan_gk_headG l hlen hlt hhyp
  unfold RegFan.fullConclG at hconcl
  rw [List.any_eq_true] at hconcl
  obtain ⟨i, hi6, hi⟩ := hconcl
  have hi' : i < Fintype.card (AtV D.toRegionDissection X) := by rw [hcard6]; exact List.mem_range.mp hi6
  set x := tl F hemp (n + (i + Fintype.card (AtV D.toRegionDissection X) - 1) % Fintype.card (AtV D.toRegionDissection X)) with hx
  set y := tl F hemp (n + i) with hy
  have hxy : Par (F.p y) (F.q x) := by
    have h := tl_adj F hemp (n + (i + Fintype.card (AtV D.toRegionDissection X) - 1) % Fintype.card (AtV D.toRegionDissection X))
    rw [tl_ray F hemp n i hi'] at h
    exact h
  have hne : x ≠ y := by
    intro h
    have h1 := tl_ray F hemp n i hi'
    have h2 : tl F hemp (n + (i + Fintype.card (AtV D.toRegionDissection X) - 1) % Fintype.card (AtV D.toRegionDissection X)) =
        tl F hemp (n + (i + Fintype.card (AtV D.toRegionDissection X) - 1) % Fintype.card (AtV D.toRegionDissection X) + 1) := by
      rw [h1]; exact h
    have h3 := tl_inj_mod F hemp h2
    rw [hcard6] at h3
    omega
  have hLc : RegFan.Lc l i = cdcode D idx F hcor x := by
    unfold RegFan.Lc; rw [hlen]
    have hlt' : (i + 6 - 1) % 6 < Fintype.card (AtV D.toRegionDissection X) := by rw [hcard6]; exact Nat.mod_lt _ (by norm_num)
    rw [hl, lst_getD D idx F hcor hemp n _ hlt', hx, hcard6]
  have hRc : RegFan.Rc l i = cdcode D idx F hcor y := by
    unfold RegFan.Rc; rw [hlen]
    have hlt' : i % 6 < Fintype.card (AtV D.toRegionDissection X) := by rw [hcard6]; exact Nat.mod_lt _ (by norm_num)
    rw [hl, lst_getD D idx F hcor hemp n _ hlt']
    have : i % 6 = i := Nat.mod_eq_of_lt (List.mem_range.mp hi6)
    rw [this]
  obtain ⟨hkx, hpx, hqx⟩ := cd_spec D F hcor x
  obtain ⟨hky, hpy, hqy⟩ := cd_spec D F hcor y
  rw [Bool.or_eq_true] at hi
  rcases hi with hi | hi
  · -- Γ_a edge along ray i
    rw [Bool.and_eq_true] at hi
    obtain ⟨hnc', hga⟩ := hi
    left
    have hcolf : RegFan.colG l i = false := by simpa using hnc'
    have hnb := noBack_of_nocolG D idx F hcor hidxA hnc hγ hαβ hcls hemp n i hi' (by rw [← hl]; exact hcolf)
    unfold RegFan.gaEdge at hga
    rw [hLc, hRc] at hga
    exact ga_of_codes D idx hidx hnc hab hac F x y (hcor x) (hcor y) hxy hnb hkx hky hqx hpy hga
  · right
    unfold RegFan.gkEdge at hi
    rw [hLc, hRc] at hi
    exact gk_of_codes D idx hidx hab hac F x y hxy hne hkx hky hpx hqx hpy hqy hi

end Erdos634.Draft.LaczFormal.RG
