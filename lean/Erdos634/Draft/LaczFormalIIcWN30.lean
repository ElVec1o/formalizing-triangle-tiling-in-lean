-- Draft/LaczFormalIIcWN30.lean -- axiom check for WN26-WN29 (turning angle at a Gamma_kite vertex, `u = v + N` for a Gamma_kite cycle).
-- NOTE, UNAUDITED.  The hypotheses of `gkite_turn` / `gkite_cycle_count` (Case IIc block + `AngGen` + two consecutive / a closed chain of Gamma_kite edges) are NOT witnessed.
-- Credit: Laczkovich (DCG 48 (2012), Sect. 6.2), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIIcWN29

#print axioms Erdos634.Draft.LaczFormal.Graph.fan_turn
#print axioms Erdos634.Draft.LaczFormal.Graph.fan_par_mod
#print axioms Erdos634.Draft.LaczFormal.RG.gkite_turn
#print axioms Erdos634.Draft.LaczFormal.RG.gkite_ratio
#print axioms Erdos634.Draft.LaczFormal.RG.gkite_cycle_count
