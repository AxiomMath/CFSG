module

public import Certificates.Data.Kernel.EvenSporU42.Defs
public import Certificates.Kernel.Sporadic.PSp45.Data

public section

namespace CertificateChecks.KernelEvenSporU42

open CFSG.KC.EvenSporU42 CertificateChecks.KernelSpor

@[expose] noncomputable def zK : Nat :=
  wordH (P45Q.S 0) (P45Q.S 1) [1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0]

@[expose] noncomputable def paK : Nat :=
  wordH (P45Q.S 0) (P45Q.S 1) [1, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1]

@[expose] noncomputable def pbK : Nat :=
  wordH (P45Q.S 0) (P45Q.S 1) [1, 1, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1]

@[expose] noncomputable def jK : List Nat :=
  (List.range 25920).filter fun j => commH (elemH P45Q.LR P45Q.TR j) zK

@[expose] noncomputable def blK : List Nat := jK.map (elemH P45Q.LR P45Q.TR)

theorem ordK_eq : CFSG.KS.SporSch.MOC.ordK P45Q.LR 4 = 25920 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem allK_true : allH blK (closureListH [paK, pbK] 30 [oneH]) zK = true := by
  decide +kernel

end CertificateChecks.KernelEvenSporU42

end
