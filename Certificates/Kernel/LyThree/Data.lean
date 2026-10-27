module

public import Certificates.Data.Kernel.SlpCls
public import Certificates.Data.Kernel.LyS0.Check
public import Certificates.Kernel.SporSch.Ly.BSData
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

#kc_repo #kc_json_gz CFSG.KD.LyThree "Certificates/Kernel/LyThree/data/classes.json.gz" 9387 673612190874577139
    (prgA : List (Nat × Nat)) (rxA : Nat) (sgA : List Nat) (tbA : List Nat)
    (clA : List (List Nat)) (cbA : List Nat) (entA : List (Nat × (List Nat × List Nat)))
    (lpA : List (Nat × Nat)) (abA : List Nat)
    (prgB : List (Nat × Nat)) (rxB : Nat) (sgB : List Nat) (tbB : List Nat)
    (clB : List (List Nat)) (cbB : List Nat) (entB : List (Nat × (List Nat × List Nat)))
    (lpB : List (Nat × Nat)) (abB : List Nat)

public section

namespace CFSG.KD.LyThree

@[expose] noncomputable def clsW (k t : Nat) (prg : List (Nat × Nat)) (rx : Nat) (sg tb : List Nat)
    (cl : List (List Nat)) (cb : List Nat) (ent : List (Nat × (List Nat × List Nat)))
    (lp : List (Nat × Nat)) (ab : List Nat) : Bool :=
  CFSG.KC.SlpPc.clsL CFSG.KD.LyS0.mul CFSG.KD.OrdLy.ONE CertificateChecks.KernelSporSch.LyBS.A
    CertificateChecks.KernelSporSch.LyBS.B 3 5 k t 12 1332 111 prg rx sg tb cl cb ent lp ab

end CFSG.KD.LyThree

end
