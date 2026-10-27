module

public import Certificates.Kernel.Co2.Join
public import Certificates.Data.Kernel.Multipliers.LabZ
public import CFSG.Certificates.Kernel.Bounds.U43Alt.Data.C_Sel
public import CFSG.Certificates.Kernel.Bounds.U43Alt.Checks.C_H
public import CFSG.Certificates.Kernel.Bounds.U43Alt.Checks.C_W
public import CFSG.Certificates.Kernel.Bounds.U43Alt.Checks.C_L

public section

namespace CertificateChecks.KernelU43

open CFSG.KC CFSG.KC.Loop CFSG.KC.LceS CertificateChecks.KernelCo2

theorem runLabZ_append (WT LB TG : Nat → Nat) (BIAS Q HIGH TOP : Nat) :
    ∀ l1 l2 x, LabZ.runLabZ WT LB TG BIAS Q HIGH TOP (List.append l1 l2) x =
      LabZ.runLabZ WT LB TG BIAS Q HIGH TOP l2 (LabZ.runLabZ WT LB TG BIAS Q HIGH TOP l1 x)
  | [], _, _ => rfl
  | C :: l1, l2, x => by
    change strictN (LabZ.labChunk WT LB TG BIAS Q HIGH TOP C x)
        (LabZ.runLabZ WT LB TG BIAS Q HIGH TOP (List.append l1 l2)) =
      LabZ.runLabZ WT LB TG BIAS Q HIGH TOP l2
        (strictN (LabZ.labChunk WT LB TG BIAS Q HIGH TOP C x) (LabZ.runLabZ WT LB TG BIAS Q HIGH TOP l1))
    rw [strictN_eq, strictN_eq, runLabZ_append WT LB TG BIAS Q HIGH TOP l1 l2]

theorem runIds_append (WT : Nat → Nat) (m : Nat) :
    ∀ l1 l2 x, LceSR.runIds WT m (List.append l1 l2) x =
      LceSR.runIds WT m l2 (LceSR.runIds WT m l1 x)
  | [], _, _ => rfl
  | C :: l1, l2, x => by
    change strictN (LceSR.idsChunk WT m C x) (LceSR.runIds WT m (List.append l1 l2)) =
      LceSR.runIds WT m l2 (strictN (LceSR.idsChunk WT m C x) (LceSR.runIds WT m l1))
    rw [strictN_eq, strictN_eq, runIds_append WT m l1 l2]

#kc_join_range Cfacts CertificateChecks.KernelCo2.runFacts_append CFSG.KD.U43C "sW" 0 13
#kc_join_range Clab CertificateChecks.KernelU43.runLabZ_append CFSG.KD.U43C "sL" 0 13
#kc_join_range Cids CertificateChecks.KernelU43.runIds_append CFSG.KD.U43C "sI" 0 13

theorem coneOk_intro {blk WT RT ST LB TG : Nat → Nat}
    {INV INV8 L nC nf m Hs K nR D BIAS Q HIGH TOP S0 S1 T0 T1 : Nat} {Cs : List Nat}
    (h1 : wordsOK WT RT ST INV INV8 m Hs = true) (h2 : invOK INV INV8 L = true)
    (h3 : Nat.ble nC (nat_lit 1048576) = true) (h4 : Nat.blt nf (nat_lit 4294967296) = true)
    (h5 : Nat.beq S0 (mkS (nat_lit 0) (nat_lit 1)) = true) (h6 : Nat.beq S1 (mkS nf nC) = true)
    (h7 : Nat.beq T0 (nat_lit 1) = true) (h8 : Nat.beq T1 (Nat.succ nf) = true)
    (h9 : HSK.hintsLt WT m K Hs = true)
    (h10 : Nat.beq (LceSR.runIds WT m Cs (nat_lit 1)) (nat_lit 1) = true)
    (h11 : LabZ.constsOK D BIAS Q HIGH TOP = true)
    (h12 : LabZ.tgOK WT TG INV8 m Hs nR K D BIAS = true)
    (h13 : Nat.beq (runFacts blk WT INV nC L Cs S0) S1 = true)
    (h14 : Nat.beq (LabZ.runLabZ WT LB TG BIAS Q HIGH TOP Cs T0) T1 = true) :
    LabZ.coneOk blk WT RT ST LB TG INV INV8 L nC nf m Hs K nR D BIAS Q HIGH TOP S0 S1 T0 T1 Cs =
      true := by
  unfold LabZ.coneOk
  rw [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]
  rfl

end CertificateChecks.KernelU43

end
