module

public import Certificates.Data.Kernel.IdxFourFuseK
public import Certificates.Kernel.IdxFour.SkData
public import Certificates.Kernel.IdxFour.E0Data
public import Certificates.Kernel.IdxFour.M0Data
public import CFSG.GF2Type.Smith1979.IdxFourModelData
import CFSG.Certificates.Kernel.Common.EachTrue
import CFSG.Certificates.Kernel.Common.ForallChunks

set_option maxRecDepth 100000

public section

namespace CFSG.KD.IF4K

open CFSG.KC.IF4C CFSG.KC.IF4R CFSG.KC.IF4F CFSG.GF2Type.Smith1979.IdxFour

@[expose] noncomputable def fuse (c : Nat) : Bool :=
  fuseBlk T O CFSG.KD.IF4E.T CFSG.KD.IF4E.O CFSG.KD.IF4M.Q (lbarGens.map packR) W c

end CFSG.KD.IF4K

#kc_each CFSG.KD.IF4K cf17612w (fun c => CFSG.KD.IF4K.fuse c) 0 8

namespace CFSG.KD.IF4K

open CFSG.KC.IF4C CFSG.KC.IF4R CFSG.GF2Type.Smith1979.IdxFour

#kc_forall_chunks cf17612wall (fun c => fuse c = true) 8 CFSG.KD.IF4K.cf17612w 1

theorem cf17612sk : (List.range 4).all (fun j => Nat.beq (look SP j) (packR (skGens.getD j #[]))) =
    true := by
  decide +kernel

end CFSG.KD.IF4K

end
