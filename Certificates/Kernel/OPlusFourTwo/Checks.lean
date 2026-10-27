module

public import Certificates.Data.Kernel.OPlusFourTwoK

public section

namespace CFSG.KP.OPlusFourTwo

open CFSG.OPlusFourTwo CFSG.KC.OPlusFourTwo

theorem vecs_ok : ∀ v : Fin 4 → ZMod 2, v ∈ vecs := by decide +kernel

theorem tree_ok : treeB o4List = true := by decide +kernel

theorem sound_ok : soundB o4List = true := by decide +kernel

theorem distinct_ok : DistinctP o4List := by decide +kernel

theorem pow12_ok : pow12B o4List = true := by decide +kernel

theorem three_ok : (o4List.filter fun M => eqE (cubeE M) 1).length = 9 := by decide +kernel

end CFSG.KP.OPlusFourTwo
