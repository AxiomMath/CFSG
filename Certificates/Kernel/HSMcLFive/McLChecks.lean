module

public import Certificates.Kernel.HSMcLFive.McLData
public import Certificates.Kernel.Census.McLChain
public import Certificates.Kernel.Misc.Perm.HSMcL
public import Certificates.Data.Kernel.FiveLocK
public import CFSG.Certificates.Kernel.Common.ForallChunks
public import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelHSMcLFive

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Misc.ArrEnum CFSG.KC.Misc.ChainTail
open CFSG.KC.B3S3K CFSG.KC.K426K CFSG.KC.FiveLocK CFSG.RankThree.Native
open CertificateChecks.KernelCensus

@[expose] noncomputable def G (j : Nat) : Nat := MF.F j

theorem msz : szOK 275 9 = true := by quickRfl

theorem permG : allN 76 (fun j => permB 275 9 (G j)) = true := by quickRfl

theorem mnums : Nat.beq NQ.N 125 = true ∧ Nat.beq NQ.ng 2 = true ∧ Nat.beq NC0.N 50 = true ∧
    Nat.beq NC0.ng 3 = true ∧ Nat.beq NC1.N 1500 = true ∧ Nat.beq NC1.ng 4 = true ∧
    Nat.beq NA0.N 25 = true ∧ Nat.beq NA0.ng 2 = true ∧ Nat.beq NA1.N 125 = true ∧
    Nat.beq NA1.ng 3 = true :=
  ⟨by quickRfl, by quickRfl, by quickRfl, by quickRfl, by quickRfl, by quickRfl, by quickRfl,
    by quickRfl, by quickRfl, by quickRfl⟩

theorem mgens : allN 2 (fun j => Nat.beq (NQ.G j) (G j)) = true ∧
    allN 3 (fun j => Nat.beq (NC0.G j) (G (64 + j))) = true ∧
    allN 4 (fun j => Nat.beq (NC1.G j) (G (67 + j))) = true ∧
    allN 2 (fun j => Nat.beq (NA0.G j) (G (71 + j))) = true ∧
    allN 3 (fun j => Nat.beq (NA1.G j) (G (73 + j))) = true :=
  ⟨by quickRfl, by quickRfl, by quickRfl, by quickRfl, by quickRfl⟩

theorem mchains : allN 14 (fun j => Nat.beq (M0.S j) (M0X.F j)) = true ∧
    allN 16 (fun j => Nat.beq (M1.S j) (M1X.F j)) = true := ⟨by quickRfl, by quickRfl⟩

theorem mheads : (Nat.beq (M0.S 0) (McLS.F 0) && Nat.beq (M0.S 1) (McLS.F 1) &&
      Nat.beq (M0.S 2) (KernelMisc.HSMcL.MC.F 0)) = true ∧
    (Nat.beq (M1.S 0) (McLS.F 0) && Nat.beq (M1.S 1) (McLS.F 1) &&
      Nat.beq (M1.S 2) (KernelMisc.HSMcL.MC.F 0)) = true := ⟨by quickRfl, by quickRfl⟩

theorem mperm0 : allN 14 (fun j => permOK 275 9 (mask 9) (275 * 9) (M0.S j) (M0.SI j)) = true := by
  quickRfl

theorem mperm1 : allN 16 (fun j => permOK 275 9 (mask 9) (275 * 9) (M1.S j) (M1.SI j)) = true := by
  quickRfl

theorem mbget0 : ∀ t < 8, mcl275Case0BaseArr[t]! = pg 9 (mask 9) M0.BP t := by decide +kernel

theorem mbget1 : ∀ t < 8, mcl275Case1BaseArr[t]! = pg 9 (mask 9) M1.BP t := by decide +kernel

theorem mlines : lines5K 275 9 125 31 NQ.T NQ.S (fun j => G (2 + j)) = true := by quickRfl

theorem msiftQ : allN 2 (fun k => siftOK 275 9 5 McLC.LR McLC.TRI McLC.BP (G k)) = true := by
  quickRfl

theorem mtrans : transFK 275 9 31 (fun j => G (33 + j)) (fun j => G (2 + j)) mcl275FiveRec =
    true := by quickRfl

theorem msiftH : allN 31 (fun k => siftOK 275 9 5 KernelMisc.HSMcL.C3.LR KernelMisc.HSMcL.C3.TRI
    KernelMisc.HSMcL.C3.BP (G (33 + k))) = true := by quickRfl

theorem mrels0 : relsK 275 9 5 M0.BP (G 2) 8 mcl275Case0Rels = true := by quickRfl

theorem mcomm0 : CFSG.KC.B3S3K.commK 275 9 3 (G 2) (fun j => G (64 + j)) = true := by quickRfl

theorem msiftC0 : allN 3 (fun k => siftOK 275 9 8 M0.LR M0.TRI M0.BP (G (64 + k))) = true := by
  quickRfl

theorem mrc : Nat.beq (rcnt (M0.LR 0)) 275 = true ∧ Nat.beq (rcnt (M1.LR 0)) 275 = true :=
  ⟨by quickRfl, by quickRfl⟩

@[expose] noncomputable def tailU (s : Nat) : Bool :=
  allN 25 fun j => ptailBranchIdxK 275 9 M0.LR M0.TR M0.BP (G 2) (pw 275 9 (G 2)) mcl275Case0Rels
    NC0.N NC0.T NC0.S 8 (Nat.add (Nat.mul 25 s) j)

theorem mnormal0 : normalK 275 9 5 NC0.N NA0.N 3 2 NC0.T NC0.S NA0.T NA0.S (fun j => G (64 + j))
    (fun j => G (71 + j)) = true := by quickRfl

theorem msiftA0 : allN 2 (fun k => siftOK 275 9 5 McLC.LR McLC.TRI McLC.BP (G (71 + k))) = true := by
  quickRfl

theorem mself0 : selfCentK 275 9 2 NC0.N NA0.N (fun j => G (71 + j)) NC0.T NA0.T NA0.S = true := by
  quickRfl

theorem meq0 : Nat.beq (G 64) (G 2) = true := by quickRfl

theorem mrels1 : relsK 275 9 5 M1.BP (G 3) 8 mcl275Case1Rels = true := by quickRfl

theorem mcomm1 : CFSG.KC.B3S3K.commK 275 9 4 (G 3) (fun j => G (67 + j)) = true := by quickRfl

theorem msiftC1 : allN 4 (fun k => siftOK 275 9 8 M1.LR M1.TRI M1.BP (G (67 + k))) = true := by
  quickRfl

@[expose] noncomputable def tailV (s : Nat) : Bool :=
  allN 25 fun j => ptailBranchIdxK 275 9 M1.LR M1.TR M1.BP (G 3) (pw 275 9 (G 3)) mcl275Case1Rels
    NC1.N NC1.T NC1.S 8 (Nat.add (Nat.mul 25 s) j)

theorem mnormal1 : normalK 275 9 5 NC1.N NA1.N 4 3 NC1.T NC1.S NA1.T NA1.S (fun j => G (67 + j))
    (fun j => G (73 + j)) = true := by quickRfl

theorem msiftA1 : allN 3 (fun k => siftOK 275 9 5 McLC.LR McLC.TRI McLC.BP (G (73 + k))) = true := by
  quickRfl

theorem mz1 : memIdxK NA1.N NA1.T NA1.S (G 3) = true ∧
    zPartK 275 9 NC1.N 3 (G 3) NC1.T (fun j => G (73 + j)) = true := ⟨by quickRfl, by quickRfl⟩

theorem meq1 : Nat.beq (G 67) (G 3) = true := by quickRfl

set_option maxHeartbeats 0 in
#kc_each CertificateChecks.KernelHSMcLFive.tailU 0 11
set_option maxHeartbeats 0 in
#kc_each CertificateChecks.KernelHSMcLFive.tailV 0 11

#kc_forall_chunks tailU_all (fun s => tailU s = true) 11 CertificateChecks.KernelHSMcLFive.tailU 1
#kc_forall_chunks tailV_all (fun s => tailV s = true) 11 CertificateChecks.KernelHSMcLFive.tailV 1

end CertificateChecks.KernelHSMcLFive

end
