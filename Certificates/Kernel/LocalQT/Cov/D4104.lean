module

public import Certificates.Data.Kernel.LocalQT.CovT
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

#kc_repo #kc_json CFSG.KD.LQT.C4104 "Certificates/Kernel/LocalQT/Cov/data/d4104.json" 44353 15007436734783613093
  (P : List Nat) (H : List (List Nat))

#kc_repo #kc_json CFSG.KD.LQT.C4104 "Certificates/Kernel/LocalQT/Cov/data/p4104.json" 82288 16976404925996667739
  (CXW : List (List Nat)) (CVN : Nat) (CWD : List (List Nat)) (CTG : List Nat) (CBK : List Nat)
  (CBG : List (List Nat)) (CBR : List (List Nat × List Nat × List (List (Nat × Bool))))

public section

namespace CFSG.KD.LQT.C4104

open CFSG.KC.LQT.Cov

@[expose] noncomputable def CTD : CT :=
  ⟨List.map (List.map zOfK) CXW, CVN, CWD, CTG, CBK,
    List.zipWith (fun g r => (List.map zOfK g, r)) CBG CBR⟩

end CFSG.KD.LQT.C4104

end
