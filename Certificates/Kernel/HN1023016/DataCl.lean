module

public import Certificates.Kernel.HN1023016.Data
public import Certificates.Data.Kernel.SlpPcCl
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

#kc_repo #kc_json CFSG.KD.HN1023016 "Certificates/Kernel/HN1023016/data/m5.json" 7158 8951341654334376733
    (px : List (Nat × Nat)) (ce : List (List (List Nat))) (lp : List (List (Nat × Nat)))
    (lab : List (List Nat))

public section

namespace CFSG.KD.HN1023016

@[expose] noncomputable def chkJClW (prg px : List (Nat × Nat)) (wg wr : List Nat)
    (hw rel fus : List (List Nat)) (bw : Nat) (hwm : List Nat) (ce : List (List (List Nat)))
    (lp : List (List (Nat × Nat))) (lab : List (List Nat)) : Bool :=
  CFSG.KC.SlpPc.chkJCl mul vec (CFSG.KD.FamHNSeed.RW 1) (CFSG.KD.FamHNSeed.RW 2)
    CFSG.KD.FamHNSeed.ONE CFSG.KD.FamHNSeed.L CFSG.KD.FamHNSeed.LV CFSG.KD.FamHNSeed.HV
    CFSG.KD.FamHNSeed.RM L9 H9 prg px wg wr hw rel fus bw hwm ce lp lab

end CFSG.KD.HN1023016

end
