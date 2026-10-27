module

public import Certificates.Data.Kernel.Fi22F.Walks
public import Certificates.Kernel.Fi22F.TabSData
public import Certificates.Kernel.Fi22F.TabHData
public import CFSG.Certificates.Kernel.Fi22.Bound2.Data.M
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Harness

public section

#kc_repo #kc_json_gz CFSG.KD.FiFW "Certificates/Kernel/Fi22F/data/walks.json.gz" 19309 5233489210237734752
  (cs : List (List Nat)) (pairs : List (Nat × List Nat × Nat × Nat × Nat))
  (hg : List (List Nat × Nat × List Nat × Nat))

namespace CertificateChecks.KernelFi22F

open CFSG.KC.LceJson CFSG.KC.Fi22F.Walks CFSG.Sporadic.Presentation.Fi22Exact

theorem relsS_bind : relsBind (sel1 CFSG.KD.FiFS.RT) wsF 0 = true := by quickRfl

theorem relsH_bind : relsBind (sel1 CFSG.KD.FiFH.RT) wsF 0 = true := by quickRfl

theorem stS_bind : posBind (sel1 CFSG.KD.FiFS.ST) sWords 0 = true := by quickRfl

theorem stH_bind : posBind (sel1 CFSG.KD.FiFH.ST) (CFSG.KD.FiFW.hg.map fun h => Ew h.1) 0 = true := by
  quickRfl

theorem pairs_ok :
    pairsOK (sel2 CFSG.KD.FiFS.B) CFSG.KD.FiFS.nf CFSG.KD.FiFW.cs CFSG.KD.Fi22KM.XRs CFSG.KD.FiFW.pairs 0 =
      true := by
  quickRfl

theorem hg_ok : hgOK (sel2 CFSG.KD.FiFS.B) CFSG.KD.FiFS.nf CFSG.KD.FiFW.cs CFSG.KD.FiFW.hg = true := by
  quickRfl

theorem neg_pairs :
    CFSG.KC.notB (pairsOK (sel2 CFSG.KD.FiFS.B) CFSG.KD.FiFS.nf CFSG.KD.FiFW.cs CFSG.KD.Fi22KM.XRs
      CFSG.KD.FiFW.pairs 1) = true := by
  quickRfl

theorem cs_ok : csOK CFSG.KD.FiFW.cs = true := by quickRfl

theorem sWords_lt : wordsLt sWords = true := by quickRfl

theorem hWords_lt : wordsLt (CFSG.KD.FiFW.hg.map fun h => Ew h.1) = true := by quickRfl

theorem rels_lt : relsLt wsF = true := by quickRfl

theorem lens : wsF.length = 204 ∧ sWords.length = 73 ∧ CFSG.KD.FiFW.hg.length = 8 ∧
    CFSG.KD.FiFW.pairs.length = 27 ∧ CFSG.KD.FiFW.cs.length = 6 := by
  decide +kernel

end CertificateChecks.KernelFi22F

end
