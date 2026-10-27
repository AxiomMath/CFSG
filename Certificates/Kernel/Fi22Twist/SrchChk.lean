module

public import Certificates.Data.Kernel.Fi22Twist.Lv
public import Certificates.Kernel.Fi22Twist.Data
public import Certificates.Kernel.Fi22Twist.LData
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelFi22Twist

open CFSG.KC.Enum CFSG.KC.Fi22Twist CFSG.KD.Fi22Twist

@[expose] noncomputable def boK (BF OF : Nat → Nat) : Bool :=
  allN (nat_lit 720) (fun k => Nat.beq (fld(BF k, nat_lit 0, nat_lit 4095)) (ap (OF (nat_lit 3)) k))

@[expose] noncomputable def kfK (KF : Nat → Nat) : Bool :=
  allN (nat_lit 2997) (fun n => strictB (KF n) fun r =>
    bAnd(Nat.blt (fld(r, nat_lit 0, nat_lit 65535)) (nat_lit 865),
      bAnd(Nat.blt (fld(r, nat_lit 16, nat_lit 65535)) (nat_lit 865),
        Nat.blt (fld(r, nat_lit 32, nat_lit 65535)) (nat_lit 865))))

@[expose] noncomputable def lcK (LF : Nat → Nat) : Bool :=
  allN (nat_lit 212) (fun n => strictB (LF n) fun r =>
    bIf(Nat.blt (fld(r, nat_lit 48, nat_lit 255)) (nat_lit 2),
      Nat.ble (Nat.add (fld(r, nat_lit 64, nat_lit 65535)) (fld(r, nat_lit 80, nat_lit 255)))
        (nat_lit 212),
      true))

theorem ch431009bo : boK BF OF = true := by quickRfl

theorem ch431009kf : kfK KF = true := by quickRfl

theorem ch431009lc : lcK LF = true := by quickRfl

theorem neg431009bo : Bool.not (boK (fun k => nIf(Nat.beq k 7, Nat.xor (BF k) 1, BF k)) OF) = true := by
  quickRfl

theorem neg431009kf :
    Bool.not (kfK (fun n => nIf(Nat.beq n 9, Nat.lor (KF n) (Nat.shiftLeft 1023 16), KF n))) = true := by
  quickRfl

theorem neg431009lc :
    Bool.not (lcK (fun n => nIf(Nat.beq n 0, Nat.lor (LF n) (Nat.shiftLeft 255 80), LF n))) = true := by
  quickRfl

end CertificateChecks.KernelFi22Twist

end
