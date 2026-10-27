module

public import Certificates.Data.Kernel.RouteP.TextLinesJoin
public import Certificates.Data.RouteP.Bridge
public import Certificates.Kernel.RouteP.Text.Data
public meta import CFSG.Certificates.Kernel.Common.StrChunks
public import CFSG.Certificates.Kernel.Common.StrChunks

public section

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

#str_chunks CertificateChecks.KernelRouteP.PCG
  CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model.Native.coverGensText 140000 100000000 8192

namespace CertificateChecks.KernelRouteP

open CFSG.KC CFSG.KC.RouteP CFSG.KD.RouteP

@[expose] noncomputable def pcgCs : List (List Char) :=
  [PCG.c0, PCG.c1, PCG.c2, PCG.c3, PCG.c4, PCG.c5, PCG.c6, PCG.c7, PCG.c8, PCG.c9, PCG.c10,
    PCG.c11, PCG.c12, PCG.c13, PCG.c14, PCG.c15, PCG.c16, PCG.c17, PCG.c18, PCG.c19, PCG.c20,
    PCG.c21, PCG.c22, PCG.c23, PCG.c24, PCG.c25, PCG.c26, PCG.c27, PCG.c28, PCG.c29, PCG.c30,
    PCG.c31, PCG.c32, PCG.c33, PCG.c34, PCG.c35, PCG.c36, PCG.c37]

@[expose] noncomputable def pcgStL : List (List Nat) :=
  [[0, 0, 0, 0, 0, 1], [0, 21018, 59, 1, 0, 0], [0, 42102, 0, 0, 0, 0], [0, 63234, 0, 0, 0, 0],
    [0, 84327, 14, 1, 0, 0], [0, 105426, 245, 1, 0, 0], [0, 126511, 0, 0, 0, 0],
    [0, 147599, 56844, 1, 0, 0], [0, 168694, 29, 1, 0, 0], [0, 189783, 294, 1, 0, 0],
    [0, 210870, 0, 0, 0, 0], [0, 231952, 166, 1, 0, 0], [0, 253022, 2886, 1, 0, 0],
    [0, 274097, 122983, 1, 0, 0], [0, 295187, 24047, 1, 0, 0], [1, 31078, 0, 0, 0, 0],
    [1, 101078, 0, 0, 0, 0], [1, 171078, 0, 0, 0, 0], [1, 241078, 0, 0, 0, 0],
    [2, 1244, 15411, 1, 0, 0], [2, 22366, 186, 1, 0, 0], [2, 43458, 0, 0, 0, 0],
    [2, 64547, 25, 1, 0, 0], [2, 85623, 227806, 1, 0, 0], [2, 106710, 120176, 1, 0, 0],
    [2, 127802, 2278, 1, 0, 0], [2, 148892, 1, 1, 0, 0], [2, 170003, 0, 0, 0, 0],
    [2, 191104, 0, 0, 0, 0], [2, 212194, 116546, 1, 0, 0], [2, 233240, 131224, 1, 0, 0],
    [2, 254366, 1589, 1, 0, 0], [2, 275439, 421, 1, 0, 0], [2, 296533, 494, 1, 0, 0],
    [3, 35418, 2, 1, 0, 0], [3, 105418, 0, 1, 0, 0], [3, 175418, 2, 1, 0, 0],
    [3, 245418, 1, 1, 0, 0], [4, 0, 0, 0, 0, 1]]

@[expose] noncomputable def pcgSt (j : Nat) : List Nat := lnth [] pcgStL j

@[expose] noncomputable def pcgPc (j : Nat) : Bool :=
  nlChkAt CGD (fun _ => 306936) ((lnth [] pcgCs j).map Char.toNat) (pcgSt j) (pcgSt (Nat.succ j))

end CertificateChecks.KernelRouteP
