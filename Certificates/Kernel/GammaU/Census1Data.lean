module

public import Certificates.Data.Kernel.GammaUCensusK
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

public section

#kc_repo #kc_json_gz CFSG.KD.GUC1 "Certificates/Kernel/GammaU/data/cen1.json.gz" 398068
  16685595675979074475 (S0 : Nat) (TH : Nat) (CS : Nat) (CSI : Nat) (NC : Nat)
  (CN : List (List Nat)) (FT : Nat) (FTi : Nat) (FC : Nat) (CG : Nat) (CGI : Nat)
  (ED : List (List Nat)) (LB : Nat) (DP : Nat) (OR : List Nat) (OG : List Nat) (OV : List Nat)
  (OP : List Nat) (OE : List (List (List Nat))) (AR : Nat) (AG : Nat) (KB : List Nat)
  (KO : List Nat) (KSP : Nat) (KSI : Nat) (KWD : List (List Nat)) (KTL : List (List Nat))
  (KT : List Nat) (KPS : List Nat) (KTR : List (List (List Nat))) (KR : List (List (List Nat)))
  (KN : Nat)

namespace CFSG.KD.GUC1

open CFSG.KC.IF4C CFSG.KC.GUC

@[expose] noncomputable def kblk (i c : Nat) : Bool := blkOK KSP KT KO KTL KR i c

@[expose] noncomputable def klvl (i : Nat) : Bool :=
  cntOK KO KTL KR i && treeOK KSP KT KO KTL KTR i && posOK KT KO KPS KB i

@[expose] noncomputable def kgens : Bool :=
  allBelow 5 (fun i => tlOK KSP KB KTL KN (Nat.succ i)) && invOK KSP KSI KN &&
    wordsOK KSP KSI KN KWD 11 && allBelow 11 (fun l => Nat.beq (look KSP l) (look AG l)) &&
    candOK CG FT FTi FC TH 1 AR AG

@[expose] noncomputable def blk (c : Nat) : Bool :=
  entsOK CS CSI FT FTi FC CG LB DP NC 384 (takeN 16 (dropN (Nat.mul 16 c) ED)) (Nat.mul 16 c)

@[expose] noncomputable def orb (q : Nat) : Bool :=
  candOK CG FT FTi FC TH 1 (nthD 0 OR q) (nthD 0 OG q) &&
    orbOK (nthD 0 OG q) 11 (nthD 0 OV q) (nthD 0 OP q) 768 18 (nthD [] OE q)

end CFSG.KD.GUC1

end
