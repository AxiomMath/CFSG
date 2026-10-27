module

public import Certificates.Data.Kernel.Misc.YamakiA6N
public import Certificates.Kernel.Misc.YamakiRep.Rec
public import Certificates.Kernel.Misc.YamakiCE.RecA6
public import Certificates.Kernel.Misc.YamakiCE.RecA6V
import CFSG.Certificates.Kernel.Common.Harness
public meta import Certificates.Kernel.Co1B.GenTri2045
public import Certificates.Kernel.Co1B.GenTri2045

public section

namespace CFSG.KD.YamakiA6

open CFSG.KD.YamakiRep

@[expose] noncomputable def ce550823bC (q : Nat) : Bool := a6ChunkN RE RP RV 11520 512 q

theorem ce550823bV : a6VK RE RP RV PVE = true := by quickRfl

theorem ce550823nC : (!a6ChunkN RE RP RH 11520 512 0) = true := by quickRfl

theorem ce550823nD : (!a6ChunkN RE (fun t => RP (Nat.add t 1)) RV 11520 512 3) = true := by
  quickRfl

theorem ce550823nE : (!a6VK RE (fun t => RP (Nat.add t 1)) RV PVE) = true := by quickRfl

theorem ce550823nF : (!a6VK RE RP RV (fun v => PVE (Nat.add v 1))) = true := by quickRfl

end CFSG.KD.YamakiA6

#kc_slices CFSG.KD.YamakiA6.ce550823bK CFSG.KD.YamakiA6.ce550823bC 23

end
