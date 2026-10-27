module

public import Certificates.Kernel.He589208.D
public import Certificates.Kernel.SporSch.HeT.Tab
public import Certificates.Data.Kernel.SporSch.PairHeCnt
public import Certificates.Data.Kernel.Misc.PermClos
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000
set_option maxHeartbeats 0
set_option Elab.async false

public section

namespace CFSG.KD.He589208.Mem

open CFSG.KC.Enum CFSG.KS CFSG.KS.SporSch CertificateChecks.KernelSpor CertificateChecks.KernelSporSch
open CFSG.KC.Misc.Clos (allR)

@[expose] noncomputable def F (j : Nat) : Nat := NF.getD j 0

@[expose] noncomputable def bindAt (x : Nat) : Bool :=
  bind5At 8330 14 HeTb.NR HeTb.NR HeTb.LT HeTb.PT (F 0) (S.TF 0) x &&
    bind5At 8330 14 HeTb.NR HeTb.NR HeTb.LT HeTb.PT (F 1) (S.TF 1) x

@[expose] noncomputable def bindB (c : Nat) : Bool := allR (Nat.mul 833 c) 833 bindAt

theorem kNF : (nfValidK 5 HeC.LR (F 0) && nfValidK 5 HeC.LR (F 1)) = true := by quickRfl

theorem kB0 : bindB 0 = true := by quickRfl
theorem kB1 : bindB 1 = true := by quickRfl
theorem kB2 : bindB 2 = true := by quickRfl
theorem kB3 : bindB 3 = true := by quickRfl
theorem kB4 : bindB 4 = true := by quickRfl
theorem kB5 : bindB 5 = true := by quickRfl
theorem kB6 : bindB 6 = true := by quickRfl
theorem kB7 : bindB 7 = true := by quickRfl
theorem kB8 : bindB 8 = true := by quickRfl
theorem kB9 : bindB 9 = true := by quickRfl

end CFSG.KD.He589208.Mem

end
