module

public import Certificates.Kernel.LocalComp.L34Un.Data
public import Certificates.Kernel.LocalComp.L34RData
public import Certificates.Kernel.LocalComp.L34SData
public import Certificates.Data.Kernel.L34Scan
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CertificateChecks.KernelLC.L34Un

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.L34K CFSG.KC.L34Scan
open CFSG.KS.PEnum CertificateChecks.KernelLC.L34X
open CFSG.KLie.CT (andB orB notB)

@[expose] noncomputable def R0 : Nat := L34R.T 86182

@[expose] noncomputable def ck0 (s : Nat) : Bool :=
  penumSlK 42 6 (mask 6) (42 * 6) false UP0.G UP0.GI UP0.k UP0.cnt UP0.T UP0.PL UP0.POS UP0.SRT
    UP0.SRI (Nat.mul s 630) 630

@[expose] noncomputable def ck1 (s : Nat) : Bool :=
  penumSlK 42 6 (mask 6) (42 * 6) false UP1.G UP1.GI UP1.k UP1.cnt UP1.T UP1.PL UP1.POS UP1.SRT
    UP1.SRI (Nat.mul s 630) 630

@[expose] noncomputable def ck2 (s : Nat) : Bool :=
  penumSlK 42 6 (mask 6) (42 * 6) false UP2.G UP2.GI UP2.k UP2.cnt UP2.T UP2.PL UP2.POS UP2.SRT
    UP2.SRI (Nat.mul s 630) 630

@[expose] noncomputable def ck3 (s : Nat) : Bool :=
  penumSlK 42 6 (mask 6) (42 * 6) false UP3.G UP3.GI UP3.k UP3.cnt UP3.T UP3.PL UP3.POS UP3.SRT
    UP3.SRI (Nat.mul s 630) 630

@[expose] noncomputable def ck4 (s : Nat) : Bool :=
  penumSlK 42 6 (mask 6) (42 * 6) false UP4.G UP4.GI UP4.k UP4.cnt UP4.T UP4.PL UP4.POS UP4.SRT
    UP4.SRI (Nat.mul s 630) 630

@[expose] noncomputable def ck5 (s : Nat) : Bool :=
  penumSlK 42 6 (mask 6) (42 * 6) false UP5.G UP5.GI UP5.k UP5.cnt UP5.T UP5.PL UP5.POS UP5.SRT
    UP5.SRI (Nat.mul s 630) 630

@[expose] noncomputable def unK (e r x : Nat) : Bool :=
  orB (Nat.beq x e) (orB (notB (invPt 42 6 x)) (orB (notB (commPt 42 6 x (UE0.G 0)))
    (orB (notB (commPt 42 6 x (UE0.G 1))) (Nat.beq x r))))

@[expose] noncomputable def un (s : Nat) : Bool :=
  strictB (pidn 42 6) fun e => strictB R0 fun r => scanSl (unK e r) L34R.T 1344 s

end CertificateChecks.KernelLC.L34Un

end
