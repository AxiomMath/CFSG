module

public import Certificates.Data.Kernel.Sp6Insp443.Cent
public import Certificates.Kernel.LocalComp.Sp6J.Data
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

public section

set_option maxRecDepth 400000

#kc_repo #kc_json_gz CertificateChecks.KernelS6I.D
  "Certificates/Kernel/Sp6Insp443/data/cent.json.gz" 54883 15703681507973203373
  (cls : List Nat) (cw : List (List Nat)) (cP : List Nat) (cI : List Nat) (nU : List Nat)
  (nW : List Nat) (uP : List Nat) (uM : List Nat) (wP : List Nat) (sP : List Nat)
  (wIdx : List Nat) (uT : List Nat) (wT : List Nat)

namespace CertificateChecks.KernelS6I

open CFSG.KC.Enum CFSG.KS CFSG.KS.Sp6I CertificateChecks.KernelLC.Sp6J

@[expose] noncomputable def ch725106q2_ (k : Nat) : Bool :=
  Nat.beq (centCntK 36 6 (mask 6) (36 * 6) C2Q.LR C2Q.TR 4 One36 (D.uP.getD k 0) (D.nU.getD k 0)
    (D.sP.getD k 0) (D.nW.getD k 0)) 0

@[expose] noncomputable def ch725106q3_ (k : Nat) : Bool :=
  Nat.beq (centCntK 36 6 (mask 6) (36 * 6) C3Q.LR C3Q.TR 4 One36 (D.uP.getD k 0) (D.nU.getD k 0)
    (D.sP.getD k 0) (D.nW.getD k 0)) 0

@[expose] noncomputable def ch725106q4_ (k : Nat) : Bool :=
  Nat.beq (centCntK 36 6 (mask 6) (36 * 6) C4Q.LR C4Q.TR 4 One36 (D.uP.getD k 0) (D.nU.getD k 0)
    (D.sP.getD k 0) (D.nW.getD k 0)) 0

end CertificateChecks.KernelS6I

end
