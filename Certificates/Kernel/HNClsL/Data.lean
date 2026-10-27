module

public import Certificates.Data.Kernel.HNClsL
public import Certificates.Kernel.SporSch.HN.PtR
public import Certificates.Kernel.SporSch.HN.PtC
public import CFSG.Certificates.Kernel.Local.HN.Lib
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo
public import CFSG.Certificates.Kernel.Local.LargeCore.Grp2

#kc_repo #kc_json_gz CFSG.KD.HNClsL "Certificates/Kernel/HNClsL/data/hncls.json.gz" 16602 870290615336731402
    (poolA : List (List Nat)) (gensA : List Nat) (nQA : Nat) (linesA : List (List (Nat × Nat)))
    (fuseA : List (Nat × (List (Nat × Nat) × Nat))) (wlA : List (List (Nat × Nat)))
    (witsA : List (List (List (Nat × Nat)) × Nat)) (trA : List Nat)
    (poolB : List (List Nat)) (gensB : List Nat) (nQB : Nat) (linesB : List (List (Nat × Nat)))
    (fuseB : List (Nat × (List (Nat × Nat) × Nat))) (wlB : List (List (Nat × Nat)))
    (witsB : List (List (List (Nat × Nat)) × Nat)) (trB : List Nat)
    (poolC : List (List Nat)) (gensC : List Nat) (nQC : Nat) (linesC : List (List (Nat × Nat)))
    (fuseC : List (Nat × (List (Nat × Nat) × Nat))) (wlC : List (List (Nat × Nat)))
    (witsC : List (List (List (Nat × Nat)) × Nat)) (trC : List Nat)

public section

namespace CFSG.KD.HNClsL

@[expose] noncomputable def lt (c : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (CFSG.KD.HNPtC.GT 10) (CFSG.KD.HNPt.R c) (Nat.blt c 36)

@[expose] noncomputable def chkL (pool : List (List Nat)) (gens : List Nat) (nQ : Nat)
    (lines : List (List (Nat × Nat))) (fuse : List (Nat × (List (Nat × Nat) × Nat)))
    (wl : List (List (Nat × Nat))) (wits : List (List (List (Nat × Nat)) × Nat)) (tr : List Nat) :
    Bool :=
  CFSG.KC.HNClsL.chk CFSG.KC.LL.HN.mm CFSG.KD.OrdHN.ONE lt pool gens nQ lines fuse wl wits tr

end CFSG.KD.HNClsL

end
