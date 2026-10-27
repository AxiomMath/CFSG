module

public import Certificates.Kernel.Sporadic.OddCore.PEnumCmd
public import Certificates.Data.Th687.DModel
meta import Certificates.Data.Th687.DModel

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelTh.DModelG

open CFSG.PSL3Four.Native CFSG.Sporadic.Th.Recog

meta def letM : Array (Array Nat) := letArr

meta def letIM : Array (Array Nat) := letInv ()

meta def repM (k : Nat) : Array Nat := wTab letArr (letInv ()) (primeReps.getD k [])

meta def r0 : Array Nat := repM 0
meta def r1 : Array Nat := repM 1
meta def r2 : Array Nat := repM 2
meta def r3 : Array Nat := repM 3
meta def r4 : Array Nat := repM 4
meta def r5 : Array Nat := repM 5
meta def r6 : Array Nat := repM 6
meta def r7 : Array Nat := repM 7
meta def r8 : Array Nat := repM 8
meta def r9 : Array Nat := repM 9
meta def r10 : Array Nat := repM 10
meta def r11 : Array Nat := repM 11

end CertificateChecks.KernelTh.DModelG

#kpenum CertificateChecks.KernelTh.DPO0 51 6 true CertificateChecks.KernelTh.DModelG.letM
  CertificateChecks.KernelTh.DModelG.letIM CertificateChecks.KernelTh.DModelG.r0 3456
#kpenum CertificateChecks.KernelTh.DPO1 51 6 true CertificateChecks.KernelTh.DModelG.letM
  CertificateChecks.KernelTh.DModelG.letIM CertificateChecks.KernelTh.DModelG.r1 3456
#kpenum CertificateChecks.KernelTh.DPO2 51 6 true CertificateChecks.KernelTh.DModelG.letM
  CertificateChecks.KernelTh.DModelG.letIM CertificateChecks.KernelTh.DModelG.r2 3456
#kpenum CertificateChecks.KernelTh.DPO3 51 6 true CertificateChecks.KernelTh.DModelG.letM
  CertificateChecks.KernelTh.DModelG.letIM CertificateChecks.KernelTh.DModelG.r3 3456
#kpenum CertificateChecks.KernelTh.DPO4 51 6 true CertificateChecks.KernelTh.DModelG.letM
  CertificateChecks.KernelTh.DModelG.letIM CertificateChecks.KernelTh.DModelG.r4 3456
#kpenum CertificateChecks.KernelTh.DPO5 51 6 true CertificateChecks.KernelTh.DModelG.letM
  CertificateChecks.KernelTh.DModelG.letIM CertificateChecks.KernelTh.DModelG.r5 3456
#kpenum CertificateChecks.KernelTh.DPO6 51 6 true CertificateChecks.KernelTh.DModelG.letM
  CertificateChecks.KernelTh.DModelG.letIM CertificateChecks.KernelTh.DModelG.r6 3456
#kpenum CertificateChecks.KernelTh.DPO7 51 6 true CertificateChecks.KernelTh.DModelG.letM
  CertificateChecks.KernelTh.DModelG.letIM CertificateChecks.KernelTh.DModelG.r7 3456
#kpenum CertificateChecks.KernelTh.DPO8 51 6 true CertificateChecks.KernelTh.DModelG.letM
  CertificateChecks.KernelTh.DModelG.letIM CertificateChecks.KernelTh.DModelG.r8 3456
#kpenum CertificateChecks.KernelTh.DPO9 51 6 true CertificateChecks.KernelTh.DModelG.letM
  CertificateChecks.KernelTh.DModelG.letIM CertificateChecks.KernelTh.DModelG.r9 3456
#kpenum CertificateChecks.KernelTh.DPO10 51 6 true CertificateChecks.KernelTh.DModelG.letM
  CertificateChecks.KernelTh.DModelG.letIM CertificateChecks.KernelTh.DModelG.r10 3456
#kpenum CertificateChecks.KernelTh.DPO11 51 6 true CertificateChecks.KernelTh.DModelG.letM
  CertificateChecks.KernelTh.DModelG.letIM CertificateChecks.KernelTh.DModelG.r11 3456

end
