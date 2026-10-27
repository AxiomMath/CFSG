module

public import Certificates.Kernel.Sporadic.Fi22.X2069Final
public import Certificates.Kernel.Sporadic.Fi22.E2067T
public import Certificates.Data.Kernel.Spor.Pc2Base
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#kc_repo #kc_json_gz CertificateChecks.KernelSpor.Fi22Sq26560D
  "Certificates/Kernel/Sporadic/Fi22/data/pc26560.json.gz" 204945 15131081500276749447
  (X : List Nat) (R : List (List Nat)) (SEP : List (Nat × Nat × List Nat)) (CO : List (Nat × Nat))
  (WIT : Nat)

namespace CertificateChecks.KernelSpor.Fi22Sq26560

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw

@[expose] noncomputable def T : Nat := Fi22ExtT.L 23

@[expose] noncomputable def L (k : Nat) : Nat := Fi22Sq26560D.X.getD k 0

@[expose] noncomputable def Bs : List Nat := [0, 1, 2, 3, 6, 4]

@[expose] noncomputable def letterOK (k : Nat) : Bool :=
  bAnd(Fi22X.cn (L k), bAnd(Fi22X.siftP (L k), Nat.beq (Fi22X.c (L k) T) (Fi22X.c T (L k))))

theorem lettersAll : bAnd(allN 16 letterOK, Nat.beq (L 15) T) = true := by quickRfl

theorem pcAll : CFSG.KC.Pc2Base.pc2OK 3510 12 (mask 12) L Bs 16 6 15 14 Fi22Sq26560D.R
    Fi22Sq26560D.SEP Fi22Sq26560D.CO Fi22Sq26560D.WIT = true := by quickRfl

end CertificateChecks.KernelSpor.Fi22Sq26560

end
