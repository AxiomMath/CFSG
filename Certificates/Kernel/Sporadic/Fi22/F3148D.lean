
module

public import Certificates.Kernel.SporSch.GenSetReplay
public import Certificates.Kernel.Sporadic.Fi22.T2068
public import Certificates.Kernel.Sporadic.Fi22.L3150M
public import CFSG.Monster.B.Fischer.Fi22CentralizerCheckInputs
public meta import CFSG.Monster.B.Fischer.Fi22CentralizerCheckInputs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.Fi22F3148

open CFSG.KC.Enum CFSG.KS CertificateChecks.KernelSpor

@[expose] noncomputable def fixL (P : Nat) : List Nat :=
  (List.range 3510).filter fun p => Nat.beq (pg 12 (mask 12) P p) p

meta def st0 : List Nat :=
  CFSG.Certificates.Native.fixedList 3510 (CFSG.Monster.B.Fischer.fi22OuterStrong3510 6)[0]!

meta def st1 : List Nat :=
  CFSG.Certificates.Native.fixedList 3510 (CFSG.Monster.B.Fischer.fi22OuterStrong3510 6)[1]!

meta def stZ : List Nat :=
  CFSG.Certificates.Native.fixedList 3510 (CFSG.Monster.B.Fischer.fi22OuterStrong3510 1)[0]!

theorem zFix : bAnd(Nat.beq (pg 12 (mask 12) Fi22E2073.E 0) 0, bAnd(Fi22X.cn Fi22E2073.E,
    allN 3 fun k => bAnd(Fi22X.cn (Fi22M3.MS k),
      Nat.beq (Fi22X.c Fi22E2073.E (Fi22M3.MS k)) (Fi22X.c (Fi22M3.MS k) Fi22E2073.E)))) = true := by
  quickRfl

end CertificateChecks.KernelSpor.Fi22F3148

end
