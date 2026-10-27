module

public import Certificates.Kernel.LocalComp.Sp6J.ClsX
public import Certificates.Data.Kernel.Sp6Insp443.Orb
public import Certificates.Data.Sp6Insp443
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#kc_repo #kc_json_gz CertificateChecks.KernelS6I.O
  "Certificates/Kernel/Sp6Insp443/data/orb.json.gz" 3542 9772778147944615757
  (X5 : Nat) (X7 : Nat) (C5 : List (List Nat)) (C7 : List (List Nat))

namespace CertificateChecks.KernelS6I

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Sp6I CFSG.KC.KGC31P CertificateChecks.KernelLC.Sp6J
  CFSG.SectionRank.QTK.Insp443.Sp6

theorem ch725105x : bAnd(gridOK 36 6 O.C5 cands5, bAnd(gridOK 36 6 O.C7 cands7,
    bAnd(cellOK 36 6 O.X5 x5T, bAnd(cellOK 36 6 O.X7 x7T,
    bAnd(pord 36 6 5 O.X5, pord 36 6 7 O.X7))))) = true := by quickRfl

@[expose] noncomputable def ch725105t (j : Nat) : Bool :=
  strictB (RX.E j) (fun t => bAnd(permOK 36 6 (mask 6) (36 * 6) t t,
    bAnd(porbOne 36 6 5 O.X5 O.C5 t, porbOne 36 6 7 O.X7 O.C7 t)))

@[expose] noncomputable def ch725105o (k : Nat) : Bool :=
  allBlk (Nat.mul 243 k) ch725105t 243

#kc_each ch725105o 0 21

theorem ch725105n : porbOne 36 6 5 O.X5 [] ((O.C5.getD 0 []).getD 0 0) = false := by
  decide +kernel

end CertificateChecks.KernelS6I

end
