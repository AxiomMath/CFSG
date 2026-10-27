module

public import Certificates.Data.Kernel.SlpPc
public import CFSG.Certificates.Kernel.Fam.HNSeed.Data.Sel
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

#kc_repo #kc_json_gz CFSG.KD.HN1023016 "Certificates/Kernel/HN1023016/data/checks.json.gz" 141041 15584882839294882372
    (prg : List (Nat × Nat)) (wg : List Nat) (wr : List Nat) (hw : List (List Nat))
    (rel : List (List Nat)) (fus : List (List Nat)) (oth : List (List Nat)) (bw : Nat)
    (hwm : List Nat) (c0 : Nat) (keyc : List Nat) (dep : Nat) (jb : Nat)

public section

namespace CFSG.KD.HN1023016

open CFSG.KC.Ord

noncomputable abbrev mul : Nat → Nat → Nat :=
  mulR 5 13 1729 133 9 CFSG.KD.FamHNSeed.L CFSG.KD.FamHNSeed.H CFSG.KD.FamHNSeed.CM
    CFSG.KD.FamHNSeed.RM

noncomputable abbrev vec : Nat → Nat → Nat :=
  vecR 5 13 1729 133 9 CFSG.KD.FamHNSeed.LV CFSG.KD.FamHNSeed.HV CFSG.KD.FamHNSeed.RM

@[expose] noncomputable def L9 : Nat := rep1 13 81
@[expose] noncomputable def H9 : Nat := Nat.shiftLeft L9 12
@[expose] noncomputable def CM9 : Nat := Nat.mul 8191 (rep1 117 9)
@[expose] noncomputable def RM9 : Nat := Nat.sub (Nat.shiftLeft 1 117) 1
@[expose] noncomputable def ONE9 : Nat := rep1 130 9
@[expose] noncomputable def LV9 : Nat := rep1 13 9
@[expose] noncomputable def HV9 : Nat := Nat.shiftLeft LV9 12

noncomputable abbrev vec9 : Nat → Nat → Nat := vecR 5 13 117 9 9 LV9 HV9 RM9

@[expose] noncomputable def chkJW (prg : List (Nat × Nat)) (wg wr : List Nat)
    (hw rel fus : List (List Nat)) (bw : Nat) (hwm : List Nat) : Bool :=
  CFSG.KC.SlpPc.chkJ mul vec (CFSG.KD.FamHNSeed.RW 1) (CFSG.KD.FamHNSeed.RW 2)
    CFSG.KD.FamHNSeed.ONE CFSG.KD.FamHNSeed.L CFSG.KD.FamHNSeed.LV CFSG.KD.FamHNSeed.HV
    CFSG.KD.FamHNSeed.RM L9 H9 prg wg wr hw rel fus bw hwm

@[expose] noncomputable def chkWW (hwm : List Nat) (c0 : Nat) (keyc : List Nat) (dep jb : Nat)
    (fus oth : List (List Nat)) : Bool :=
  CFSG.KC.SlpPc.chkW vec9 L9 H9 CM9 RM9 ONE9 LV9 HV9 hwm c0 keyc dep jb fus oth

end CFSG.KD.HN1023016

end
