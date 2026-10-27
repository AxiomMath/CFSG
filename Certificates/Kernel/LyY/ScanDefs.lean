module

public import Certificates.Kernel.LyY.ChainData
public import Certificates.Kernel.LyY.ScanData
public import Certificates.Data.Kernel.LyY.Scan
public import Certificates.Kernel.LocalComp.BlockGen
public import CFSG.Sporadic.Recognition.LyonsAmalgamYData

public section

namespace CertificateChecks.KernelLyY

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.LyY CFSG.KC.Co3Bfs
open CFSG.Sporadic.Recognition.LyonsSims

@[expose] noncomputable def fE (a : Nat) : Bool :=
  Nat.beq (blkY 1080 11 YC.LR YC.TR YC.TRI YC.BP (YC.S 0) (YC.SI 0) Ly1080.autRelators
    Ly1080.autWitnesses a) (lget E a)

@[expose] noncomputable def fC (k : Nat) : Bool :=
  allFrom (20 * k) 20 (guardF 1080 fE)

end CertificateChecks.KernelLyY

end
