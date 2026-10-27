module

public import Certificates.Kernel.HN1408.TableIDefs
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.HaradaModel27.LiftCheck
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Spor.BindList

public section

set_option maxRecDepth 400000
set_option maxHeartbeats 0

namespace CFSG.KD.HN1408.Lift

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.Blk CFSG.KD.HN1408
open CFSG.EvenSporadicStandard.HNRecog CFSG.EvenSporadicStandard.HNRecog.HaradaModel27

@[expose] noncomputable def UK : Nat := WK HaradaModel27.uWord

@[expose] noncomputable def VK : Nat := WK HaradaModel27.vWord

@[expose] noncomputable def ZK : Nat := WK wordZ

@[expose] def LU : Nat := 271105

@[expose] def LV : Nat := 266290

@[expose] noncomputable def sqZK (X : Nat) : Bool := Nat.beq (pc X X) idK || Nat.beq (pc X X) ZK

@[expose] noncomputable def commZK (X Y : Nat) : Bool :=
  Nat.beq (pc X Y) (pc Y X) || Nat.beq (pc X Y) (pc ZK (pc Y X))

@[expose] noncomputable def liftK : Bool :=
  allN 256 fun i => !sqZK (pc UK (TI1.T i)) || allN 256 fun j =>
    !sqZK (pc VK (TI1.T j)) || !commZK (pc UK (TI1.T i)) (pc VK (TI1.T j))

theorem base_ok : bAnd(canonK 1408 11 (mask 11) (1408 * 11) UK,
    bAnd(canonK 1408 11 (mask 11) (1408 * 11) VK, bAnd(canonK 1408 11 (mask 11) (1408 * 11) ZK,
    bAnd(commP UK ZK, bAnd(commP VK ZK, bAnd(canonK 5 4 (mask 4) (5 * 4) LU,
    bAnd(canonK 5 4 (mask 4) (5 * 4) LV, bAnd(blkMapK 1408 11 4 (TB.F 0) 5 UK LU,
    blkMapK 1408 11 4 (TB.F 0) 5 VK LV)))))))) = true := by
  quickRfl

theorem lift_ok : liftK = true := by
  quickRfl

end CFSG.KD.HN1408.Lift

end
