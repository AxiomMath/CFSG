module

public import Certificates.Data.Kernel.Sp6Insp443.Sub
public import Certificates.Data.Sp6Insp443
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Common.Lce

public section

set_option maxRecDepth 400000

#kc_repo #kc_json_gz CertificateChecks.KernelS6I.IR
  "Certificates/Kernel/Sp6Insp443/data/irr.json.gz" 4219 11979823240951389576
  (R : List (List (List Nat)))

namespace CertificateChecks.KernelS6I

open CFSG.KC CFSG.KC.Enum CFSG.KS CFSG.KS.Sp6I CFSG.KC.KGC31P CFSG.SectionRank.QTK.Insp443.Sp6

noncomputable abbrev pT7 (Ts : List CFSG.Sporadic.Th.Native.Table) : List Nat :=
  Ts.map (packT 6)

theorem ch725107k : (cands7.all fun Ts => tabsK 36 6 Ts) = true ∧ tabsK 36 6 [x7T] = true :=
  ⟨by quickRfl, by quickRfl⟩

theorem ch725107b :
    psubOK 36 6 (pT7 (cands7.getD 0 [])) (pT7 (cands7.getD 2 [])) = true ∧
    psubOK 36 6 (pT7 (cands7.getD 1 [])) (pT7 (cands7.getD 4 [])) = true ∧
    psubOK 36 6 (pT7 (cands7.getD 2 [])) (pT7 (cands7.getD 2 [])) = true ∧
    psubOK 36 6 (pT7 (cands7.getD 3 [])) (pT7 (cands7.getD 2 [])) = true ∧
    psubOK 36 6 (pT7 (cands7.getD 4 [])) (pT7 (cands7.getD 4 [])) = true ∧
    psubOK 36 6 (pT7 (cands7.getD 5 [])) (pT7 (cands7.getD 4 [])) = true :=
  ⟨by quickRfl, by quickRfl, by quickRfl, by quickRfl, by quickRfl, by quickRfl⟩

theorem ch725107r :
    pirrW 36 6 7 (packT 6 x7T) (pinv 36 6 (packT 6 x7T)) (pT7 (cands7.getD 0 []))
      (pT7 (cands7.getD 2 [])) (IR.R.getD 0 []) = true ∧
    pirrW 36 6 7 (packT 6 x7T) (pinv 36 6 (packT 6 x7T)) (pT7 (cands7.getD 1 []))
      (pT7 (cands7.getD 4 [])) (IR.R.getD 1 []) = true ∧
    pirrW 36 6 7 (packT 6 x7T) (pinv 36 6 (packT 6 x7T)) (pT7 (cands7.getD 3 []))
      (pT7 (cands7.getD 2 [])) (IR.R.getD 2 []) = true ∧
    pirrW 36 6 7 (packT 6 x7T) (pinv 36 6 (packT 6 x7T)) (pT7 (cands7.getD 5 []))
      (pT7 (cands7.getD 4 [])) (IR.R.getD 3 []) = true :=
  ⟨by quickRfl, by quickRfl, by quickRfl, by quickRfl⟩

theorem ch725107n_b : notB (psubOK 36 6 (pT7 (cands7.getD 2 [])) (pT7 (cands7.getD 0 []))) =
    true := by quickRfl

theorem ch725107n_r : notB (pirrW 36 6 7 (packT 6 x7T) (pinv 36 6 (packT 6 x7T))
    (pT7 (cands7.getD 0 [])) (pT7 (cands7.getD 2 [])) (IR.R.getD 1 [])) = true := by quickRfl

end CertificateChecks.KernelS6I

end
