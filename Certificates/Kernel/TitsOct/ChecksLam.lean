module

public import Certificates.Kernel.TitsOct.Checks
public import Certificates.Kernel.TitsOct.DataLam
public import Certificates.Data.Kernel.TitsOctLamK
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelTitsOct

open CFSG.KC.Enum CFSG.KS CFSG.KC.TwoF4LieK CFSG.KC.TitsOctK CFSG.KC.TitsOctLamK CFSG.KD.TitsOct
  CFSG.KD.TitsOctLam

@[expose] noncomputable def FX (j : Nat) : Nat := nIf(Nat.blt j 5, FP j, GX 0)

theorem layA : layK lpD PL 1 1024 LAYA PARA = true := by quickRfl

theorem layB : layK lpD PL 2 1024 LAYB PARB = true := by quickRfl

theorem layC : layK lpD PL 6 1024 LAYC PARC = true := by quickRfl

theorem layD : layK lpD PL 24 1024 LAYD PARD = true := by quickRfl

theorem bindX : bindK F GI GX [wX] = true := by quickRfl

theorem fixX : Nat.beq (gp (GX 0) 0) 0 = true := by quickRfl

theorem recA : recPK FX 6 1 10 LAY0 2 ORA PRA LBA PSA = true := by quickRfl

theorem recC : recPK FX 6 6 80 LAY0 4 ORC PRC LBC PSC = true := by quickRfl

theorem recD : recPK FX 6 24 640 LAY0 6 ORD PRD LBD PSD = true := by quickRfl

theorem cnt2 : Nat.beq (layCnt LAY0 2) 10 = true := by quickRfl

theorem cnt4 : Nat.beq (layCnt LAY0 4) 80 = true := by quickRfl

theorem cnt6 : Nat.beq (layCnt LAY0 6) 640 = true := by quickRfl

theorem cnt8 : Nat.beq (layCnt LAY0 8) 1024 = true := by quickRfl

theorem lamA : Nat.beq (lamCnt LAY0 LAYA) 512 = true := by quickRfl

theorem lamC : Nat.beq (lamCnt LAY0 LAYC) 384 = true := by quickRfl

theorem lamD : Nat.beq (lamCnt LAY0 LAYD) 448 = true := by quickRfl

theorem line12 : allN 5 (fun k => strictB (plK PL 0 k) (fun v => bIf(onLine lpD 1 v,
    allN 3 (fun m => strictB (lpD (Nat.add (Nat.mul 3 v) m)) (fun x =>
      bIf(Nat.beq x 0, true, bIf(Nat.beq x 1, true, Nat.beq x 2)))), true))) = true := by
  quickRfl

theorem cmpAB : cmpK LAY0 LAYA LAYB = true := by quickRfl

theorem walks : allL (fun _ P => walkK lpD LAY0 LAYA P) W 0 = true := by quickRfl

theorem startW : starts LAY0 2 W = true := by quickRfl

end CertificateChecks.KernelTitsOct

end
