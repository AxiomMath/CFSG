module

public import Certificates.Kernel.StdOdd.C7A.Data
public import Certificates.Kernel.StdOdd.C7A.OrbData
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

namespace C7A

theorem nxOK : stagesOK RO.DS NX = true := by quickRfl

theorem nxFull : Nat.beq (net RO.DS NX (full 3968055)) (full 3968055) = true := by quickRfl

@[expose] noncomputable def nbF (s : ℕ) : Bool :=
  orbNetOK RO.DS NX RO.PL (D7A.xB AM BM) UR 566865 7 12 s

#kc_slices CFSG.KD.StdOdd.Cent.C7A.NBX CFSG.KD.StdOdd.Cent.C7A.nbF 13

@[expose] noncomputable def crF (q : ℕ) : Bool := D7A.orbChunkB 18 UR AM BM 566865 cr q

#kc_slices CFSG.KD.StdOdd.Cent.C7A.CRX CFSG.KD.StdOdd.Cent.C7A.crF 3

theorem orbFix : D7A.orbFixB UR AM BM 566865 0 = true := by quickRfl

end C7A

end CFSG.KD.StdOdd.Cent

end
