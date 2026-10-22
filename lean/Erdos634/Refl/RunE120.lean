import Erdos634.Refl.DataE120

/-! Refl/RunE120.lean -- kernel checks (`decide +kernel`, no `native_decide`) of the GapE120 certificate:
    the tree of the (3,5,7) tile in the equilateral side-15 target (1860 nodes: 6 in the top tree, 1854 in 22 chunks).
    `topE120`: top tree with stubs, each stub accepted iff its configuration is one of `knownE120`;
    `chunkE120_k`: each chunk subtree on its configuration.  UNAUDITED. -/

set_option maxRecDepth 100000
open Refl

theorem topE120 : instE120.checkAllR knownE120 400 treeE120 = true := by decide +kernel
theorem instE120_ok : instE120.ok = true := by decide +kernel
theorem chunkE120_0 : checkNodeE instE120 400 chunkCfgE0 chunkE0 = true := by decide +kernel
theorem cfgOkE120_0 : chunkCfgE0.all Tri.ok = true := by decide +kernel
theorem chunkE120_1 : checkNodeE instE120 400 chunkCfgE1 chunkE1 = true := by decide +kernel
theorem cfgOkE120_1 : chunkCfgE1.all Tri.ok = true := by decide +kernel
theorem chunkE120_2 : checkNodeE instE120 400 chunkCfgE2 chunkE2 = true := by decide +kernel
theorem cfgOkE120_2 : chunkCfgE2.all Tri.ok = true := by decide +kernel
theorem chunkE120_3 : checkNodeE instE120 400 chunkCfgE3 chunkE3 = true := by decide +kernel
theorem cfgOkE120_3 : chunkCfgE3.all Tri.ok = true := by decide +kernel
theorem chunkE120_4 : checkNodeE instE120 400 chunkCfgE4 chunkE4 = true := by decide +kernel
theorem cfgOkE120_4 : chunkCfgE4.all Tri.ok = true := by decide +kernel
theorem chunkE120_5 : checkNodeE instE120 400 chunkCfgE5 chunkE5 = true := by decide +kernel
theorem cfgOkE120_5 : chunkCfgE5.all Tri.ok = true := by decide +kernel
theorem chunkE120_6 : checkNodeE instE120 400 chunkCfgE6 chunkE6 = true := by decide +kernel
theorem cfgOkE120_6 : chunkCfgE6.all Tri.ok = true := by decide +kernel
theorem chunkE120_7 : checkNodeE instE120 400 chunkCfgE7 chunkE7 = true := by decide +kernel
theorem cfgOkE120_7 : chunkCfgE7.all Tri.ok = true := by decide +kernel
theorem chunkE120_8 : checkNodeE instE120 400 chunkCfgE8 chunkE8 = true := by decide +kernel
theorem cfgOkE120_8 : chunkCfgE8.all Tri.ok = true := by decide +kernel
theorem chunkE120_9 : checkNodeE instE120 400 chunkCfgE9 chunkE9 = true := by decide +kernel
theorem cfgOkE120_9 : chunkCfgE9.all Tri.ok = true := by decide +kernel
theorem chunkE120_10 : checkNodeE instE120 400 chunkCfgE10 chunkE10 = true := by decide +kernel
theorem cfgOkE120_10 : chunkCfgE10.all Tri.ok = true := by decide +kernel
theorem chunkE120_11 : checkNodeE instE120 400 chunkCfgE11 chunkE11 = true := by decide +kernel
theorem cfgOkE120_11 : chunkCfgE11.all Tri.ok = true := by decide +kernel
theorem chunkE120_12 : checkNodeE instE120 400 chunkCfgE12 chunkE12 = true := by decide +kernel
theorem cfgOkE120_12 : chunkCfgE12.all Tri.ok = true := by decide +kernel
theorem chunkE120_13 : checkNodeE instE120 400 chunkCfgE13 chunkE13 = true := by decide +kernel
theorem cfgOkE120_13 : chunkCfgE13.all Tri.ok = true := by decide +kernel
theorem chunkE120_14 : checkNodeE instE120 400 chunkCfgE14 chunkE14 = true := by decide +kernel
theorem cfgOkE120_14 : chunkCfgE14.all Tri.ok = true := by decide +kernel
theorem chunkE120_15 : checkNodeE instE120 400 chunkCfgE15 chunkE15 = true := by decide +kernel
theorem cfgOkE120_15 : chunkCfgE15.all Tri.ok = true := by decide +kernel
theorem chunkE120_16 : checkNodeE instE120 400 chunkCfgE16 chunkE16 = true := by decide +kernel
theorem cfgOkE120_16 : chunkCfgE16.all Tri.ok = true := by decide +kernel
theorem chunkE120_17 : checkNodeE instE120 400 chunkCfgE17 chunkE17 = true := by decide +kernel
theorem cfgOkE120_17 : chunkCfgE17.all Tri.ok = true := by decide +kernel
theorem chunkE120_18 : checkNodeE instE120 400 chunkCfgE18 chunkE18 = true := by decide +kernel
theorem cfgOkE120_18 : chunkCfgE18.all Tri.ok = true := by decide +kernel
theorem chunkE120_19 : checkNodeE instE120 400 chunkCfgE19 chunkE19 = true := by decide +kernel
theorem cfgOkE120_19 : chunkCfgE19.all Tri.ok = true := by decide +kernel
theorem chunkE120_20 : checkNodeE instE120 400 chunkCfgE20 chunkE20 = true := by decide +kernel
theorem cfgOkE120_20 : chunkCfgE20.all Tri.ok = true := by decide +kernel
theorem chunkE120_21 : checkNodeE instE120 400 chunkCfgE21 chunkE21 = true := by decide +kernel
theorem cfgOkE120_21 : chunkCfgE21.all Tri.ok = true := by decide +kernel
