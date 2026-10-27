module

public import Certificates.Kernel.J2Cover.M22TrK
public import Certificates.Kernel.Misc.Perm.HexCmd
meta import Certificates.Kernel.J2Cover.M22LamAux

public section

set_option maxRecDepth 400000

#kmisc_packarrs CertificateChecks.KernelJ2Cover.LTP CertificateChecks.KernelJ2Cover.lamSrc 8

namespace CertificateChecks.KernelJ2Cover

open CFSG.KC.Enum CFSG.KS CFSG.KC.J2Models
open CFSG.Monster.B.Co2.Native
open CFSG.ComponentClassification.J2Cover.Models

@[expose] noncomputable def stL (T S F A i p q : Nat) : Nat :=
  strictN fld(S, Nat.shiftLeft i (nat_lit 3), nat_lit 255) fun u =>
  strictN fld(T, Nat.add (Nat.shiftLeft (Nat.land u (nat_lit 127)) (nat_lit 10))
      (Nat.shiftLeft p (nat_lit 3)), nat_lit 255) fun t =>
    Nat.xor (Nat.shiftRight u (nat_lit 7)) (Nat.xor (Nat.shiftRight t (nat_lit 7))
      fld(F, Nat.add (Nat.shiftLeft (Nat.land t (nat_lit 127)) (nat_lit 7)) (pg 13 (mask 13) A q),
        nat_lit 1))

@[expose] noncomputable def lamN (T S PA IA : Nat) : Nat :=
  xrN fun i => stL T S FRP ACP i (pg 7 (mask 7) PA i) (pg 13 (mask 13) IA i)

@[expose] noncomputable def fLY (T S a : Nat) : Bool :=
  ((lamN T S (DP a) (DI a)).testBit 0 ^^ muBit a ^^ muBit (btK a)) == lamBit a

@[expose] noncomputable def fusN (T S : Nat) : Nat :=
  xrN fun i => stL T S FRP ACP i (pg 13 (mask 13) FPP i) (pg 13 (mask 13) FIP i)

@[expose] noncomputable def fLT (T B m : Nat) : Bool :=
  (fun x y => strictB fld(B, Nat.shiftLeft y (nat_lit 3), nat_lit 255) fun b =>
    Nat.beq fld(T, Nat.shiftLeft m (nat_lit 3), nat_lit 255)
      (Nat.add (mtK x b) (nIf(Bool.xor (lamBit y) ((fRK x).testBit b), nat_lit 128, nat_lit 0))))
    (Nat.shiftRight m (nat_lit 7)) (Nat.land m (nat_lit 127))

@[expose] noncomputable def fBI (B I a : Nat) : Bool :=
  bAnd(Nat.beq fld(B, Nat.shiftLeft a (nat_lit 3), nat_lit 255) (btK a),
    bAnd(Nat.beq fld(I, Nat.shiftLeft a (nat_lit 3), nat_lit 255) (itK a),
      Nat.blt fld(I, Nat.shiftLeft a (nat_lit 3), nat_lit 255) (nat_lit 128)))

@[expose] noncomputable def fSI (S I i : Nat) : Bool :=
  strictB (pg 13 (mask 13) ACP i) fun s => strictB fld(I, Nat.shiftLeft s (nat_lit 3), nat_lit 255)
    fun si => bAnd(Nat.blt s (nat_lit 128), Nat.beq fld(S, Nat.shiftLeft i (nat_lit 3), nat_lit 255)
      (Nat.add si (nIf((fRK si).testBit s, nat_lit 128, nat_lit 0))))

@[expose] noncomputable def fLTP (m : Nat) : Bool := fLT (LTP 0) (LTP 2) m

@[expose] noncomputable def fBIP (a : Nat) : Bool := fBI (LTP 2) (LTP 3) a

@[expose] noncomputable def fSIP (i : Nat) : Bool := fSI (LTP 1) (LTP 3) i

@[expose] noncomputable def fLYP (a : Nat) : Bool := fLY (LTP 0) (LTP 1) a

end CertificateChecks.KernelJ2Cover

end
