module

public import Certificates.Kernel.FourJ2J3.J3Data
public import Certificates.Data.Kernel.FourJoinedK
public import Certificates.Kernel.SporSch.PairJ3.Chain
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelFourJ.J3

open CFSG.KC.Enum CFSG.KS CFSG.KC.BfsPin CFSG.KC.FourJ CertificateChecks.KernelFourJ
open CertificateChecks.KernelSporSch

@[expose] noncomputable def SK : List Nat := (List.range 128).map J3D.SKT

theorem nums : (Nat.beq J3D.N 128 && Nat.beq J3D.m 73) = true := by quickRfl

theorem gens : fjGensK 6156 13 (PJ3.S 0) (PJ3.S 1) (PJ3.SI 0) (PJ3.SI 1) J3D.ng J3D.G J3D.SO
    J3D.SL = true := by quickRfl

theorem bfs : bfsK 6156 13 J3D.ng J3D.G J3D.N J3D.T J3D.E J3D.S = true := by quickRfl

theorem keys : keysSK 6156 13 [5766] J3D.N J3D.T SK = true := by quickRfl

theorem klein : fjKleinK 6156 13 [5766] J3D.N J3D.T J3D.m J3D.PX J3D.PY J3D.PXY = true := by
  quickRfl

theorem tree : fjTreeK 6156 13 [5766] J3D.T J3D.m J3D.nBig J3D.PX J3D.PY J3D.PAR = true := by
  quickRfl

theorem iso : fjIsoK 6156 13 (PJ3.S 0) (PJ3.S 1) (PJ3.SI 0) (PJ3.SI 1) J3D.T J3D.m J3D.nBig
    J3D.PX J3D.PY J3D.IJ J3D.IO J3D.IL = true := by quickRfl

theorem norm : fjNormK 6156 13 (PJ3.S 0) (PJ3.S 1) (PJ3.SI 0) (PJ3.SI 1) J3D.T J3D.nBig J3D.nX
    J3D.PX J3D.PY J3D.NJ J3D.NCX J3D.NCY J3D.Z J3D.ZI J3D.NO J3D.NL = true := by quickRfl

theorem gen : fjGenK 6156 13 (PJ3.S 0) (PJ3.S 1) J3D.nX J3D.Z J3D.ZI J3D.UO J3D.UL = true := by
  quickRfl

theorem comp : fjCompK 6156 13 [5766] J3D.N J3D.T J3D.m J3D.PX J3D.PY J3D.PXY J3D.INV J3D.FM =
    true := by quickRfl

end CertificateChecks.KernelFourJ.J3

end
