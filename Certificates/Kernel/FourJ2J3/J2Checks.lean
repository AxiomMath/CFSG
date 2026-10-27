module

public import Certificates.Kernel.FourJ2J3.J2Data
public import Certificates.Data.Kernel.FourJoinedK
public import Certificates.Kernel.SporSch.Pair.J2Chain
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelFourJ.J2

open CFSG.KC.Enum CFSG.KS CFSG.KC.BfsPin CFSG.KC.FourJ CertificateChecks.KernelFourJ
open CertificateChecks.KernelSporSch

@[expose] noncomputable def SK : List Nat := (List.range 128).map J2D.SKT

theorem nums : (Nat.beq J2D.N 128 && Nat.beq J2D.m 73) = true := by quickRfl

theorem gens : fjGensK 315 9 (PJ2.S 0) (PJ2.S 1) (PJ2.SI 0) (PJ2.SI 1) J2D.ng J2D.G J2D.SO
    J2D.SL = true := by quickRfl

theorem bfs : bfsK 315 9 J2D.ng J2D.G J2D.N J2D.T J2D.E J2D.S = true := by quickRfl

theorem keys : keysSK 315 9 [164] J2D.N J2D.T SK = true := by quickRfl

theorem klein : fjKleinK 315 9 [164] J2D.N J2D.T J2D.m J2D.PX J2D.PY J2D.PXY = true := by quickRfl

theorem tree : fjTreeK 315 9 [164] J2D.T J2D.m J2D.nBig J2D.PX J2D.PY J2D.PAR = true := by quickRfl

theorem iso : fjIsoK 315 9 (PJ2.S 0) (PJ2.S 1) (PJ2.SI 0) (PJ2.SI 1) J2D.T J2D.m J2D.nBig J2D.PX
    J2D.PY J2D.IJ J2D.IO J2D.IL = true := by quickRfl

theorem norm : fjNormK 315 9 (PJ2.S 0) (PJ2.S 1) (PJ2.SI 0) (PJ2.SI 1) J2D.T J2D.nBig J2D.nX
    J2D.PX J2D.PY J2D.NJ J2D.NCX J2D.NCY J2D.Z J2D.ZI J2D.NO J2D.NL = true := by quickRfl

theorem gen : fjGenK 315 9 (PJ2.S 0) (PJ2.S 1) J2D.nX J2D.Z J2D.ZI J2D.UO J2D.UL = true := by
  quickRfl

theorem comp : fjCompK 315 9 [164] J2D.N J2D.T J2D.m J2D.PX J2D.PY J2D.PXY J2D.INV J2D.FM =
    true := by quickRfl

end CertificateChecks.KernelFourJ.J2

end
