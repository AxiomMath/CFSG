module

public import Certificates.Kernel.SporSch.Mathieu.M23FourData
public import Certificates.Kernel.SporSch.Mathieu.M23Cls
public import Certificates.Data.Kernel.SporSch.FourK
public import Certificates.Data.Kernel.Spor.MulH
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.M23FourK

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH
open CFSG.KS.SporSch.MOC CFSG.KS.SporSch.FourK CertificateChecks.KernelSporSch

theorem sz : szOK 23 5 = true := by quickRfl

theorem idc : canonK 23 5 (mask 5) (23 * 5) (pidn 23 5) = true := by quickRfl

theorem kid : CFSG.KS.Prim.idK 23 5 (mask 5) = true := by quickRfl

theorem cnt : Nat.beq M23F.cnt 2688 = true := by quickRfl

theorem head : penumHdK (pidn 23 5) M23F.cnt 3000 M23F.T M23F.PL = true := by quickRfl

theorem rc : canonK 23 5 (mask 5) (23 * 5) (M23CK.getD 0 clsD0).R = true := by quickRfl

theorem gens : allN 4 (fun j => bAnd(Nat.beq (M23F.GI j) (M23C1.S j),
    bAnd(Nat.beq (M23F.G j) (pidn 23 5), canonK 23 5 (mask 5) (23 * 5) (M23C1.S j)))) = true := by
  quickRfl

theorem pe : penumSlK 23 5 (mask 5) (23 * 5) true M23F.G M23F.GI 4 M23F.cnt M23F.T M23F.PL
    M23F.POS M23F.SRT M23F.SRI 0 2688 = true := by quickRfl

theorem hs : slK M23F.cnt (hsortPtK 23 5 (mask 5) M23F.cnt M23F.T M23F.HS M23F.HSI) 0 2688 =
    true := by quickRfl

@[expose] noncomputable def blk (lo : Nat) : Bool :=
  allBlk lo (fourAt 23 5 M23F.cnt M23F.T (M23CK.getD 0 clsD0).R (2 ^ 30 * 3 ^ 30)) 448

theorem b0 : blk 0 = true := by quickRfl

theorem b1 : blk 448 = true := by quickRfl

theorem b2 : blk 896 = true := by quickRfl

theorem b3 : blk 1344 = true := by quickRfl

theorem b4 : blk 1792 = true := by quickRfl

theorem b5 : blk 2240 = true := by quickRfl

end CertificateChecks.KernelSporSch.M23FourK

end
