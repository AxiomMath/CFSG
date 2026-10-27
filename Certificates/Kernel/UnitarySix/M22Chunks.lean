module

public import Certificates.Kernel.UnitarySix.M22C
public import Certificates.Kernel.UnitarySix.M22ChunkData
public import Certificates.Kernel.LocalComp.BlockGen
public import Certificates.Data.Kernel.U6.HuntK
public import Certificates.Data.Kernel.U6.M22CntL
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.HuntRankData
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelU6

open CFSG.KC.U6 CFSG.KLie.CT CFSG.KS.Raw CFSG.EvenSmallLie.UnitarySix.Hunt

@[expose] noncomputable def R8 : Nat := unkey key8
@[expose] noncomputable def R0 : Nat := unkey key0
@[expose] noncomputable def RY : Nat := unkey keyY

@[expose] noncomputable def oM : Nat :=
  sumN 5 fun i => Nat.shiftLeft (roff 22 (22 * 5) (M22C.LR i)) (Nat.mul 32 i)

@[expose] noncomputable def cK (a : Nat) : Nat := chunkL R8 R0 RY keys8 keys0 keysY M22C.TR oM a

@[expose] noncomputable def chunkF (a : Nat) : Bool := Nat.beq (cK a) (VN.getD a 0)

end CertificateChecks.KernelU6

#lc_blocks CertificateChecks.KernelU6.CB CertificateChecks.KernelU6.chunkF 22 1

end
