module

public import Certificates.Kernel.Sporadic.OddCore.Co3Fus
public import Certificates.Data.Kernel.Spor.PEnumC
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.Co3Fus

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH

open CFSG.KS.PEnumC in
theorem eE0 : penumSlC 8 16 Co3E.cnt Co3E.T Co3E.PL Co3E.POS Co3ECl Co3E.SRT Co3E.SRI 0 512 =
    true := by quickRfl
open CFSG.KS.PEnumC in
theorem eE1 : penumSlC 8 16 Co3E.cnt Co3E.T Co3E.PL Co3E.POS Co3ECl Co3E.SRT Co3E.SRI 512 512 =
    true := by quickRfl

@[expose] noncomputable def hsGo (n w m cnt : Nat) (T HS HSI : Nat → Nat) : Nat → Nat → Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → Bool) (fun _ _ => true)
    (fun _ ih i a => strictB (r32 HS i) (fun s => bAnd(Nat.blt s cnt,
      bAnd(Nat.beq (r32 HSI s) i, bIf(Nat.blt (Nat.succ i) cnt,
        strictB (hkeyK n w m (T (r32 HS (Nat.succ i))))
          (fun b => bAnd(Nat.blt a b, ih (Nat.succ i) b)), true)))))

theorem eH0 : hsGo 276 9 (mask 9) Co3E.cnt Co3E.T Co3E.HS Co3E.HSI 512 0
    (hkeyK 276 9 (mask 9) (Co3E.T (r32 Co3E.HS 0))) = true := by quickRfl
theorem eH1 : hsGo 276 9 (mask 9) Co3E.cnt Co3E.T Co3E.HS Co3E.HSI 512 512
    (hkeyK 276 9 (mask 9) (Co3E.T (r32 Co3E.HS 512))) = true := by quickRfl

@[expose] noncomputable def clChkK (c : Nat) : Bool :=
  bIf(Nat.blt (Nat.mod c 16) 8,
    findPtK Co3E.cnt Co3E.T (prodQK 276 9 (mask 9) 16 Co3E.T (bothK 8 Co3T.S Co3T.SI)) Co3ECl c,
    Nat.beq (r32 Co3ECl c) (r32 Co3ECl (Nat.add (Nat.mul (r32 Co3ECl (Nat.add (Nat.mul
      (r32 Co3ECl (Nat.sub c 8)) 16) (Nat.sub (Nat.mod c 16) 8))) 16)
      (Nat.sub (Nat.mod c 16) 8))))

theorem eCg : allN 8 (fun j => Nat.beq (pc (pc (Co3T.S j) (Co3T.S j)) (Co3T.S j)) (Co3T.SI j)) =
    true := by quickRfl

theorem eCl0 : slK (Nat.mul Co3E.cnt 16) clChkK 0 4096 = true := by quickRfl
theorem eCl1 : slK (Nat.mul Co3E.cnt 16) clChkK 4096 4096 = true := by quickRfl
theorem eCl2 : slK (Nat.mul Co3E.cnt 16) clChkK 8192 4096 = true := by quickRfl
theorem eCl3 : slK (Nat.mul Co3E.cnt 16) clChkK 12288 4096 = true := by quickRfl

end CertificateChecks.KernelSpor.Co3Fus

end
