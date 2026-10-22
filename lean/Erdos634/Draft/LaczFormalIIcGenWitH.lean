-- Draft/LaczFormalIIcGenWitH.lean -- WITNESS of the GENERIC Case IIc block (alpha != beta), step H: corner counts.  `cntR genDiss idx X l` as a list count of exact corner points;
-- alpha-corners = beta-corners at EVERY point of the plane (`RegularPQ`), and corner counts (1,1,0) at the 8 octagon vertices (`hcor`).
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012)), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIIcGenWitG

set_option linter.constructorNameAsVariable false

namespace Erdos634.Draft.LaczFormal.GenWit

open Classical
open Erdos634.Geometry Erdos634.CertCoord Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Thm21 Erdos634.Draft.LaczFormal.RG Z2

theorem count_ofFn_sum {α : Type} [BEq α] [LawfulBEq α] : ∀ (n : ℕ) (f : Fin n → α) (p : α),
    (List.ofFn f).count p = ∑ i, if f i = p then 1 else 0
  | 0, f, p => by simp
  | n + 1, f, p => by
    rw [List.ofFn_succ, List.count_cons, count_ofFn_sum n, Fin.sum_univ_succ]
    simp [add_comm]

theorem card_filter_count {α : Type} [BEq α] [LawfulBEq α] {n : ℕ} (f : Fin n → α) (p : α) :
    (Finset.univ.filter (fun i => f i = p)).card = (List.ofFn f).count p := by
  rw [count_ofFn_sum, Finset.card_filter]

theorem ptR_inj {p q : Pt} (h : ptR p = ptR q) : p = q := by
  have h0 := congrArg (fun z : Plane => z 0) h
  have h1 := congrArg (fun z : Plane => z 1) h
  simp only [ptR_zero, ptR_one] at h0 h1
  exact Prod.ext (val_inj (by linarith)) (val_inj (by linarith))

def cornerL (l : Fin 3) : List Pt := tileTab.map (fun t => t.pt l)

theorem ofFn_corner (l : Fin 3) : List.ofFn (fun i : Fin 204 => (TT i).pt l) = cornerL l := by
  unfold cornerL
  rw [← ofFn_TT, List.map_ofFn]; rfl

theorem cntR_eq (X : Plane) (l : Fin 3) :
    cntR genDiss idx X l = (Finset.univ.filter (fun i : Fin 204 => ptR ((TT i).pt l) = X)).card := by
  unfold cntR
  apply Finset.card_bij (fun p _ => p.1)
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    obtain ⟨h1, h2⟩ := hp
    have hl : p.2 = l := by simpa [idx] using h2
    rw [← hl, ← triZ_pts (TT_props p.1).1]
    exact h1
  · intro p hp q hq hpq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp hq
    have e1 : p.2 = l := by simpa [idx] using hp.2
    have e2 : q.2 = l := by simpa [idx] using hq.2
    exact Prod.ext hpq (by rw [e1, e2])
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    refine ⟨(i, l), ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨?_, by simp [idx]⟩
    show (triZ (TT i)).pts l = X
    rw [triZ_pts (TT_props i).1]; exact hi

theorem cntR_of_pt (p : Pt) (l : Fin 3) : cntR genDiss idx (ptR p) l = (cornerL l).count p := by
  rw [cntR_eq, ← ofFn_corner, ← card_filter_count]
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun h => ptR_inj h, fun h => by rw [h]⟩

theorem cntR_of_not_pt (X : Plane) (h : ¬ ∃ p, ptR p = X) (l : Fin 3) : cntR genDiss idx X l = 0 := by
  rw [cntR_eq, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro i _ e
  exact h ⟨_, e⟩

theorem alphaL_eq : alphaL = cornerL 0 := rfl
theorem betaL_eq : betaL = cornerL 1 := rfl
theorem gammaL_eq : gammaL = cornerL 2 := rfl

theorem alphaL_length : alphaL.length = 204 := by simp [alphaL, tileTab_length]
theorem betaL_length : betaL.length = 204 := by simp [betaL, tileTab_length]

theorem reg_spec (p : Pt) : alphaL.count p = betaL.count p := by
  by_cases h : p ∈ alphaL ∨ p ∈ betaL
  · have key : ∀ k, k < 204 → fpt (alphaL.getD k (zero, zero)) = true ∧ fpt (betaL.getD k (zero, zero)) = true := by
      intro k hk
      have := regRow_all k hk
      unfold regRow at this
      simpa [Bool.and_eq_true] using this
    have hfp : fpt p = true := by
      rcases h with h | h
      · obtain ⟨k, hk, hkp⟩ := List.mem_iff_getElem.mp h
        have hk' : k < 204 := by rwa [alphaL_length] at hk
        have := (key k hk').1
        rwa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some, hkp] at this
      · obtain ⟨k, hk, hkp⟩ := List.mem_iff_getElem.mp h
        have hk' : k < 204 := by rwa [betaL_length] at hk
        have := (key k hk').2
        rwa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some, hkp] at this
    unfold fpt at hfp
    simpa using hfp
  · push_neg at h
    rw [List.count_eq_zero_of_not_mem h.1, List.count_eq_zero_of_not_mem h.2]

theorem cor_spec (j : Fin 8) : alphaL.count (polyV j) = 1 ∧ betaL.count (polyV j) = 1 ∧ gammaL.count (polyV j) = 0 := by
  have h := cor_ok
  unfold corB at h
  rw [List.all_eq_true] at h
  have := h j (List.mem_finRange j)
  simpa [Bool.and_eq_true, and_assoc] using this

/-- **alpha-corners = beta-corners at every point of the plane.** -/
theorem genDiss_hregR : ∀ X, cntR genDiss idx X 0 = cntR genDiss idx X 1 := by
  intro X
  by_cases h : ∃ p, ptR p = X
  · obtain ⟨p, rfl⟩ := h
    rw [cntR_of_pt, cntR_of_pt, ← alphaL_eq, ← betaL_eq]
    exact reg_spec p
  · rw [cntR_of_not_pt X h, cntR_of_not_pt X h]

theorem cnt_eq_cntR (X : Plane) (l : Fin 3) : RG.cnt genDiss idx X l = cntR genDiss idx X l := by
  unfold cntR RG.cnt; congr

theorem genDiss_hregc : ∀ X, RG.cnt genDiss idx X 0 = RG.cnt genDiss idx X 1 := by
  intro X; rw [cnt_eq_cntR, cnt_eq_cntR]; exact genDiss_hregR X

/-- **hcor: corner counts (1,1,0) at the eight octagon vertices.** -/
theorem genDiss_hcor : ∀ j : Fin 8, RG.cnt genDiss idx (octP.v j) 0 = 1 ∧ RG.cnt genDiss idx (octP.v j) 1 = 1 ∧ RG.cnt genDiss idx (octP.v j) 2 = 0 := by
  intro j
  have e : octP.v j = ptR (polyV j) := rfl
  rw [e, cnt_eq_cntR, cnt_eq_cntR, cnt_eq_cntR, cntR_of_pt, cntR_of_pt, cntR_of_pt, ← alphaL_eq, ← betaL_eq, ← gammaL_eq]
  exact cor_spec j

end Erdos634.Draft.LaczFormal.GenWit
