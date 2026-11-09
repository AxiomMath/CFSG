module

public import Certificates.Kernel.StdOdd.C5.Data
public import Certificates.Kernel.StdOdd.C5.OrbData
public import Certificates.Kernel.StdOdd.CentOrbBlk
public import Certificates.Kernel.StdOdd.RootOrbit
public meta import Certificates.Kernel.Co1B.GenTri2045
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.Co1B.GenTri2045

set_option Elab.async false
set_option maxRecDepth 100000

public section

namespace CFSG.KD.StdOdd.Cent

open CFSG.KC.StdOdd.Orbit CFSG.KC.StdOdd.Chain CFSG.KD.StdOdd.Orbit

namespace C5

theorem nxOK : stagesOK RO.DS NX = true := by quickRfl

theorem nxFull : Nat.beq (net RO.DS NX (full 3968055)) (full 3968055) = true := by quickRfl

@[expose] noncomputable def nbF (s : ℕ) : Bool :=
  orbNetOK RO.DS NX RO.PL (D5.xB AM BM) UR 793590 5 12 s

#kc_slices CFSG.KD.StdOdd.Cent.C5.NBX CFSG.KD.StdOdd.Cent.C5.nbF 13

@[expose] noncomputable def crF (q : ℕ) : Bool := D5.orbChunkB 18 UR AM BM 793590 cr q

#kc_slices CFSG.KD.StdOdd.Cent.C5.CRX CFSG.KD.StdOdd.Cent.C5.crF 4

theorem orbFix : D5.orbFixB UR AM BM 793590 105 = true := by quickRfl

end C5

end CFSG.KD.StdOdd.Cent

end
