module

import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.HarnessGz
import CFSG.Certificates.Kernel.Common.HarnessGzTree
import CFSG.Certificates.Kernel.Common.JsonFamilyGz
import CFSG.Certificates.Kernel.Common.Repo
public import Certificates.Kernel.Sporadic.Fi24Br.Data
public import Certificates.Kernel.Sporadic.Fi23Br.Data
public import Certificates.Kernel.Sporadic.Fi24Fix.Data
public import Certificates.Data.Kernel.Spor.Fi24Ext
public import Certificates.Data.Kernel.Spor.Fi24Fix

#kc_repo #kc_ktree_gz CFSG.KD.Fi24Ext MX "Certificates/Kernel/Sporadic/Fi24Ext/data/mats.bin.gz" 152491 4 14334154 16922523253043304296
#kc_repo #kc_ktree_gz CFSG.KD.Fi24Ext M3 "Certificates/Kernel/Sporadic/Fi24Ext/data/s253.bin.gz" 16003 4 32006 7033818493439680831
#kc_repo #kc_ktree_gz CFSG.KD.Fi24Ext CFT "Certificates/Kernel/Sporadic/Fi24Ext/data/digF.bin.gz" 512 4 152491 3673358099226235069
#kc_repo #kc_ktree_gz CFSG.KD.Fi24Ext CQT "Certificates/Kernel/Sporadic/Fi24Ext/data/digQ.bin.gz" 512 4 16003 14115846266573629579
#kc_repo #kc_json_family_gz CFSG.KD.Fi24Ext "Certificates/Kernel/Sporadic/Fi24Ext/data/regs.json.gz" 9273 15590466030930604455
  (WC : List Nat) (WL : List Nat)
#kc_repo #kc_json_gz CFSG.KD.Fi24Ext "Certificates/Kernel/Sporadic/Fi24Ext/data/regs.json.gz" 9273 15590466030930604455
  (FSM : Nat) (OJ : List Nat) (MJ : List Nat) (SI : List Nat)
#kc_listDispatch CFSG.KD.Fi24Ext WC WC 55
#kc_listDispatch CFSG.KD.Fi24Ext WL WL 19

public section

namespace CFSG.KD.Fi24Ext

@[expose] noncomputable def REG (r : Nat) : Nat :=
  @Bool.rec (fun _ => Nat) (MX (Nat.sub r (nat_lit 3)))
    ([CFSG.KD.BrFi24.RB (nat_lit 23), CFSG.KD.BrFi24.RB (nat_lit 24), MX (nat_lit 26)].getD r
      (nat_lit 0))
    (Nat.blt r (nat_lit 3))

@[expose] noncomputable def ST (g : Nat) : Nat := MX (SI.getD g (nat_lit 0))

@[expose] noncomputable def FS (g : Nat) : Bool :=
  Nat.beq (Nat.land (Nat.shiftRight FSM g) (nat_lit 1)) (nat_lit 1)

@[expose] noncomputable def CTF (t : Nat) : Nat :=
  fld(CFT (Nat.shiftRight t (nat_lit 9)), Nat.mul (Nat.land t (nat_lit 511)) (nat_lit 8), nat_lit 255)

@[expose] noncomputable def CTQ (t : Nat) : Nat :=
  fld(CQT (Nat.shiftRight t (nat_lit 9)), Nat.mul (Nat.land t (nat_lit 511)) (nat_lit 8), nat_lit 255)

@[expose] noncomputable def G (j : Nat) : Nat := MX j

@[expose] noncomputable def Gi (j : Nat) : Nat := MX (Nat.add (nat_lit 13) j)

@[expose] noncomputable def B2 : Nat := MX 26
@[expose] noncomputable def F : Nat := MX 27
@[expose] noncomputable def Rr : Nat := MX 28
@[expose] noncomputable def RF : Nat := MX 29
@[expose] noncomputable def K : Nat := MX 30
@[expose] noncomputable def S : Nat := MX 31
@[expose] noncomputable def E253 : Nat := MX 32
@[expose] noncomputable def SRF : Nat := MX 33
@[expose] noncomputable def E : Nat := MX 34
@[expose] noncomputable def T : Nat := MX 35
@[expose] noncomputable def W0 : Nat := MX 36
@[expose] noncomputable def W1 : Nat := MX 37
@[expose] noncomputable def P1 : Nat := MX 38
@[expose] noncomputable def P2 : Nat := MX 39
@[expose] noncomputable def U : Nat := MX 40
@[expose] noncomputable def U2 : Nat := MX 41
@[expose] noncomputable def U4 : Nat := MX 42
@[expose] noncomputable def U8 : Nat := MX 43
@[expose] noncomputable def U16 : Nat := MX 44
@[expose] noncomputable def H0 : Nat := MX 45
@[expose] noncomputable def Xw : Nat := MX 46
@[expose] noncomputable def Yw : Nat := MX 47
@[expose] noncomputable def Y2 : Nat := MX 48
@[expose] noncomputable def Y4 : Nat := MX 49
@[expose] noncomputable def X2w : Nat := MX 50
@[expose] noncomputable def H1 : Nat := MX 51
@[expose] noncomputable def X0 : Nat := MX 52
@[expose] noncomputable def X1 : Nat := MX 53
@[expose] noncomputable def Q : Nat := MX 54
@[expose] noncomputable def Qi : Nat := MX 55
@[expose] noncomputable def Y0 : Nat := MX 56
@[expose] noncomputable def Y1 : Nat := MX 57

@[expose] noncomputable def LO3 : Nat := Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 64009)) (nat_lit 1)

@[expose] noncomputable def RM3 : Nat := Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 253)) (nat_lit 1)

@[expose] noncomputable def CI3 : Nat := CFSG.KC.Ord.rep1 253 253

@[expose] noncomputable def ONE3 : Nat := CFSG.KC.Ord.rep1 254 253

@[expose] noncomputable def UP3 : Nat :=
  Nat.rec (motive := fun _ => Nat) 0
    (fun i acc => Nat.lor acc (Nat.shiftLeft (Nat.sub (Nat.shiftLeft 1 (Nat.sub (Nat.sub 253 i) 1)) 1)
      (Nat.succ (Nat.mul (Nat.succ 253) i)))) 253

end CFSG.KD.Fi24Ext

end
