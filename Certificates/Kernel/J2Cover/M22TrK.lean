module

public import Certificates.Kernel.J2Cover.M22Lk
public import Certificates.Kernel.Misc.Perm.HexCmd
meta import Certificates.Kernel.J2Cover.M22TrAux
public import CFSG.Certificates.Kernel.J2ModelsGen
public import Certificates.Kernel.J2Cover.M22Blocks

public section

set_option maxRecDepth 400000

#kmisc_packarrs CertificateChecks.KernelJ2Cover.R7P CertificateChecks.KernelJ2Cover.r7Src 8

namespace CertificateChecks.KernelJ2Cover

open CFSG.KC.Enum CFSG.KS CFSG.KC.J2Models
open CFSG.Monster.B.Co2.Native
open CFSG.ComponentClassification.J2Cover.Models

@[expose] noncomputable def xorRN (p : Nat → Nat) (lo len : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0) (fun l ih => Nat.xor ih (p (Nat.add lo l))) len

@[expose] noncomputable def xrN (p : Nat → Nat) : Nat :=
  Nat.xor (xorRN (fun k => xorRN p (Nat.mul (nat_lit 64) k) (nat_lit 64)) (nat_lit 0) (nat_lit 73))
    (xorRN p (nat_lit 4672) (nat_lit 53))

@[expose] noncomputable def t7 (R x y : Nat) : Nat :=
  fld(R, Nat.add (Nat.shiftLeft x (nat_lit 10)) (Nat.shiftLeft y (nat_lit 3)), nat_lit 127)

@[expose] noncomputable def stR (R PA IA PD i : Nat) : Nat :=
  t7 R fld(PA, Nat.mul (nat_lit 7) i, nat_lit 127)
    fld(PD, Nat.mul (nat_lit 7) fld(IA, Nat.mul (nat_lit 13) i, nat_lit 8191), nat_lit 127)

@[expose] noncomputable def trN (R a d : Nat) : Nat := xrN (stR R (DP a) (DI a) (DP d))

@[expose] noncomputable def hOK (v a d j : Nat) : Bool :=
  v.testBit j == ((eBit j && bitR fRK a d) ^^ cobBitG mtK (bMask j) a d)

@[expose] noncomputable def fOK (v a d : Nat) : Bool :=
  v.testBit 6 == (bitR fRK a d ^^ cobBitG mtK muMask a d)

@[expose] noncomputable def fT7 (R m : Nat) : Bool :=
  (fun a d => strictB (trN R a d) fun v =>
    hOK v a d 0 && hOK v a d 1 && hOK v a d 2 && hOK v a d 3 && hOK v a d 4 && hOK v a d 5 &&
      fOK v a d)
    (m / 128 + 1) (m % 128)

@[expose] noncomputable def fR7 (R m : Nat) : Bool :=
  (fun x y => R.testBit (1024 * x + 8 * y) == bitR (hRK 0) x y &&
    R.testBit (1024 * x + 8 * y + 1) == bitR (hRK 1) x y &&
    R.testBit (1024 * x + 8 * y + 2) == bitR (hRK 2) x y &&
    R.testBit (1024 * x + 8 * y + 3) == bitR (hRK 3) x y &&
    R.testBit (1024 * x + 8 * y + 4) == bitR (hRK 4) x y &&
    R.testBit (1024 * x + 8 * y + 5) == bitR (hRK 5) x y &&
    R.testBit (1024 * x + 8 * y + 6) == bitR fRK x y) (m / 128) (m % 128)

end CertificateChecks.KernelJ2Cover

end
