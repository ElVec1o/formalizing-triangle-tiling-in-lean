import Erdos634.BeesonThm2Hyp

/-!
# BeesonThm2Hyp — Beeson Thm 2 hypotheses discharged: wrapper

Key results:
- `tile_angles_distinct`: tile angles α < β < γ pairwise distinct
- `hyp_i_angles_le_gamma`: target angles ≤ γ when α ≤ β
- `hyp_i_not_similar`: target multiset ≠ tile multiset
- `a_lt_b_e1`: at e=1, f < f²−1 for f ≥ 2
- `hyp_iii`: exactly one tile at base corner presenting β

VERIFIED: 0 sorry, standard axioms.
-/

namespace Erdos634.Draft.BeesonThm2HypWrap

open Erdos634.BeesonThm2Hyp

theorem bh_tile_angles_distinct {α β γ : ℝ} (hα : 0 < α) (hαβ : α < β) (hγ : γ = 2 * α + β) :
    α < β ∧ β < γ ∧ α < γ :=
  tile_angles_distinct hα hαβ hγ

theorem bh_hyp_i_angles_le_gamma {α β γ : ℝ} (hα : 0 < α) (hαβ : α ≤ β) (hγ : γ = 2 * α + β) :
    β ≤ γ ∧ 3 * α ≤ γ :=
  hyp_i_angles_le_gamma hα hαβ hγ

theorem bh_hyp_i_not_similar {α β γ : ℝ} (hα : 0 < α) (hαβ : α < β) (hγ : γ = 2 * α + β) :
    ({β, 3 * α, β} : Multiset ℝ) ≠ {α, β, γ} :=
  hyp_i_not_similar hα hαβ hγ

theorem bh_a_lt_b_e1 {f : ℕ} (hf : 2 ≤ f) : f < f ^ 2 - 1 :=
  a_lt_b_e1 hf

-- Non-vacuity: f=3 → 3 < 8
example : (3 : ℕ) < 3 ^ 2 - 1 := bh_a_lt_b_e1 (by norm_num)

#print axioms bh_tile_angles_distinct
#print axioms bh_a_lt_b_e1

end Erdos634.Draft.BeesonThm2HypWrap
