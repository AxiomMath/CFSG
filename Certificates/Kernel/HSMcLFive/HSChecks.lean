module

public import Certificates.Kernel.HSMcLFive.HSData
public import Certificates.Kernel.HS100.FiveData
public import Certificates.Kernel.HS100.ChainData
public import Certificates.Kernel.Misc.Perm.HSMcL
public import Certificates.Data.Kernel.FiveLocK
public import Certificates.Data.Kernel.Misc.PermWit
public import CFSG.Certificates.Kernel.Common.ForallChunks
public import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelHSMcLFive

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Misc.ArrEnum CFSG.KC.Misc.ChainTail
open CFSG.KC.B3S3K CFSG.KC.K426K CFSG.KC.FiveLocK CFSG.RankThree.Native
open CertificateChecks.KernelHS100

@[expose] noncomputable def F (j : Nat) : Nat := FV.F j

theorem hsz : szOK 100 7 = true := by quickRfl

theorem permF : allN 82 (fun j => permB 100 7 (F j)) = true := by quickRfl

theorem hnums : Nat.beq EQ.N 125 = true ∧ Nat.beq EQ.ng 2 = true ∧ Nat.beq EA0.N 25 = true ∧
    Nat.beq EA0.ng 2 = true ∧ Nat.beq EA23.N 125 = true ∧ Nat.beq EA23.ng 3 = true ∧
    Nat.beq ED.N 60 = true ∧ Nat.beq ED.ng 2 = true :=
  ⟨by quickRfl, by quickRfl, by quickRfl, by quickRfl, by quickRfl, by quickRfl, by quickRfl,
    by quickRfl⟩

theorem pHPall : allN 16 (fun j => permB 100 7 (HP.F j)) = true := by quickRfl

theorem hgens : allN 2 (fun j => Nat.beq (EQ.G j) (F (0 + j))) = true ∧
    allN 2 (fun j => Nat.beq (EA0.G j) (F (75 + j))) = true ∧
    allN 3 (fun j => Nat.beq (EA23.G j) (F (77 + j))) = true ∧
    Nat.beq (ED.G 0) (cmt 100 7 (F 68) (F 69)) = true ∧ Nat.beq (ED.G 1) (F 69) = true :=
  ⟨by quickRfl, by quickRfl, by quickRfl, by quickRfl, by quickRfl⟩

theorem hchains : allN 15 (fun j => Nat.beq (H0.S j) (H0X.F j)) = true ∧
    allN 15 (fun j => Nat.beq (H2.S j) (H2X.F j)) = true ∧
    allN 13 (fun j => Nat.beq (H23.S j) (H23X.F j)) = true :=
  ⟨by quickRfl, by quickRfl, by quickRfl⟩

theorem hheads : (Nat.beq (H0.S 0) (HP.F 0) && Nat.beq (H0.S 1) (HP.F 1) &&
      Nat.beq (H0.S 2) (HP.F 15)) = true ∧
    (Nat.beq (H2.S 0) (HP.F 0) && Nat.beq (H2.S 1) (HP.F 1) && Nat.beq (H2.S 2) (HP.F 15)) =
      true ∧
    (Nat.beq (H23.S 0) (HP.F 0) && Nat.beq (H23.S 1) (HP.F 1) && Nat.beq (H23.S 2) (HP.F 15)) =
      true :=
  ⟨by quickRfl, by quickRfl, by quickRfl⟩

theorem hperm0 : allN 15 (fun j => permOK 100 7 (mask 7) (100 * 7) (H0.S j) (H0.SI j)) = true := by
  quickRfl

theorem hperm2 : allN 15 (fun j => permOK 100 7 (mask 7) (100 * 7) (H2.S j) (H2.SI j)) = true := by
  quickRfl

theorem hperm23 : allN 13 (fun j => permOK 100 7 (mask 7) (100 * 7) (H23.S j) (H23.SI j)) =
    true := by quickRfl

theorem bget0 : ∀ t < 8, hs100Case0BaseArr[t]! = pg 7 (mask 7) H0.BP t := by decide +kernel

theorem bget2 : ∀ t < 10, hs100Case2BaseArr[t]! = pg 7 (mask 7) H2.BP t := by decide +kernel

theorem bget23 : ∀ t < 9, hs100Case23BaseArr[t]! = pg 7 (mask 7) H23.BP t := by decide +kernel

theorem lines : lines5K 100 7 125 31 EQ.T EQ.S (fun j => F (2 + j)) = true := by quickRfl

theorem siftQ : allN 2 (fun k => siftOK 100 7 5 HC.LR HC.TRI HC.BP (F k)) = true := by quickRfl

theorem trans : transFK 100 7 31 (fun j => F (33 + j)) (fun j => F (2 + j)) hs100FiveRec = true := by
  quickRfl

theorem siftH : allN 31 (fun k => siftOK 100 7 6 KernelMisc.HSMcL.C2.LR KernelMisc.HSMcL.C2.TRI
    KernelMisc.HSMcL.C2.BP (F (33 + k))) = true := by quickRfl

theorem rels0 : relsK 100 7 5 H0.BP (F 2) 8 hs100Case0Rels = true := by quickRfl

theorem comm0 : CFSG.KC.B3S3K.commK 100 7 3 (F 2) (fun j => F (64 + j)) = true := by quickRfl

theorem siftC0 : allN 3 (fun k => siftOK 100 7 8 H0.LR H0.TRI H0.BP (F (64 + k))) = true := by
  quickRfl

theorem rc : Nat.beq (rcnt (H0.LR 0)) 100 = true ∧ Nat.beq (rcnt (H2.LR 0)) 100 = true ∧
    Nat.beq (rcnt (H23.LR 0)) 100 = true := ⟨by quickRfl, by quickRfl, by quickRfl⟩

@[expose] noncomputable def tailX (s : Nat) : Bool :=
  allN 25 fun j => ptailBranchIdxK 100 7 H0.LR H0.TR H0.BP (F 2) (pw 100 7 (F 2)) hs100Case0Rels
    C0.N C0.T C0.S 8 (Nat.add (Nat.mul 25 s) j)

theorem normal0 : normalK 100 7 5 C0.N EA0.N 3 2 C0.T C0.S EA0.T EA0.S (fun j => F (64 + j))
    (fun j => F (75 + j)) = true := by quickRfl

theorem siftA0 : allN 2 (fun k => siftOK 100 7 5 HC.LR HC.TRI HC.BP (F (75 + k))) = true := by
  quickRfl

theorem self0 : selfCentK 100 7 2 C0.N EA0.N (fun j => F (75 + j)) C0.T EA0.T EA0.S = true := by
  quickRfl

theorem eq0 : Nat.beq (F 64) (F 2) = true := by quickRfl

theorem rels2 : relsK 100 7 5 H2.BP (F 4) 10 hs100Case2Rels = true := by quickRfl

theorem comm2 : CFSG.KC.B3S3K.commK 100 7 4 (F 4) (fun j => F (67 + j)) = true := by quickRfl

theorem siftC2 : allN 4 (fun k => siftOK 100 7 10 H2.LR H2.TRI H2.BP (F (67 + k))) = true := by
  quickRfl

@[expose] noncomputable def tailY (s : Nat) : Bool :=
  allN 25 fun j => ptailBranchIdxK 100 7 H2.LR H2.TR H2.BP (F 4) (pw 100 7 (F 4)) hs100Case2Rels
    C2.N C2.T C2.S 10 (Nat.add (Nat.mul 25 s) j)

theorem derivedLe : derivedLeK 100 7 ED.N 4 2 ED.T ED.S (fun j => F (67 + j)) ED.G = true := by
  quickRfl

theorem cdMem : memIdxK C2.N C2.T C2.S (F 80) = true ∧ memIdxK C2.N C2.T C2.S (F 81) = true :=
  ⟨by quickRfl, by quickRfl⟩

theorem cdComm : Nat.beq (F 69) (cmt 100 7 (F 80) (F 81)) = true := by quickRfl

theorem dNC : (!CFSG.KC.FiveLocK.commK 100 7 (ED.G 0) (ED.G 1)) = true := by quickRfl

theorem dT0 : Nat.beq (ED.T 0) (pidn 100 7) = true := by quickRfl

theorem ctree : allN ED.N (fun k => Nat.beq (ED.T k) (pidn 100 7) ||
    allN ED.N (CFSG.KC.PermWit.ctreePt 100 7 ED.N k ED.T (WT k))) = true := by quickRfl

theorem zD : zPartK 100 7 C2.N 2 (F 4) C2.T ED.G = true := by quickRfl

theorem siftD : allN 2 (fun k => siftOK 100 7 5 HC.LR HC.TRI HC.BP (ED.G k)) = true := by quickRfl

theorem eq2 : Nat.beq (F 67) (F 4) = true := by quickRfl

theorem rels23 : relsK 100 7 5 H23.BP (F 25) 9 hs100Case23Rels = true := by quickRfl

theorem comm23 : CFSG.KC.B3S3K.commK 100 7 4 (F 25) (fun j => F (71 + j)) = true := by quickRfl

theorem siftC23 : allN 4 (fun k => siftOK 100 7 9 H23.LR H23.TRI H23.BP (F (71 + k))) = true := by
  quickRfl

@[expose] noncomputable def tailZ (s : Nat) : Bool :=
  allN 25 fun j => ptailBranchIdxK 100 7 H23.LR H23.TR H23.BP (F 25) (pw 100 7 (F 25))
    hs100Case23Rels C23.N C23.T C23.S 9 (Nat.add (Nat.mul 25 s) j)

theorem normal23 : normalK 100 7 5 C23.N EA23.N 4 3 C23.T C23.S EA23.T EA23.S
    (fun j => F (71 + j)) (fun j => F (77 + j)) = true := by quickRfl

theorem siftA23 : allN 3 (fun k => siftOK 100 7 5 HC.LR HC.TRI HC.BP (F (77 + k))) = true := by
  quickRfl

theorem z23 : memIdxK EA23.N EA23.T EA23.S (F 25) = true ∧
    zPartK 100 7 C23.N 3 (F 25) C23.T (fun j => F (77 + j)) = true := ⟨by quickRfl, by quickRfl⟩

theorem eq23 : Nat.beq (F 71) (F 25) = true := by quickRfl

set_option maxHeartbeats 0 in
#kc_each CertificateChecks.KernelHSMcLFive.tailX 0 4
set_option maxHeartbeats 0 in
#kc_each CertificateChecks.KernelHSMcLFive.tailY 0 4
set_option maxHeartbeats 0 in
#kc_each CertificateChecks.KernelHSMcLFive.tailZ 0 4

#kc_forall_chunks tailX_all (fun s => tailX s = true) 4 CertificateChecks.KernelHSMcLFive.tailX 1
#kc_forall_chunks tailY_all (fun s => tailY s = true) 4 CertificateChecks.KernelHSMcLFive.tailY 1
#kc_forall_chunks tailZ_all (fun s => tailZ s = true) 4 CertificateChecks.KernelHSMcLFive.tailZ 1

end CertificateChecks.KernelHSMcLFive

end
