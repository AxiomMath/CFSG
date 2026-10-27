module

public import Certificates.Data.Kernel.Fi23Nt.PosDefs
public import Certificates.Data.Kernel.Fi23Nt.TabDefs
public import Certificates.Kernel.Fi23Nt.ChkDefs
public import Certificates.Kernel.Fi23Nt.DataB
public import Certificates.Kernel.Fi23Nt.DataDD
public import Certificates.Kernel.Fi23Nt.DataE
public import Certificates.Kernel.Fi23Nt.DataM

public section

namespace CFSG.KD.Fi23Nt

open CFSG.KC.Enum CFSG.KC.Fi23Nt CFSG.KD.Fi23K CFSG.KS.PEnum

@[expose] noncomputable def PTS0 (k : Nat) : Nat := r32 (TT (nat_lit 0) (nat_lit 0)) k

@[expose] noncomputable def posSl (s : Nat) : Bool :=
  posSlK G POS0 PTS0 PAR0 LAB0 (Nat.mul s (nat_lit 1024)) (slLen s)

@[expose] noncomputable def passV0 : Bool := passK POS0 PAR0 LAB0 G st v0

@[expose] noncomputable def wordsOK : Bool :=
  bAnd(wsokK eBW, bAnd(wsokK eCW, bAnd(wsokK ePW, bAnd(wsokK fixW, bAnd(wsokK (fstK st),
    bAnd(wsokK ddW, bAnd(wokK hW, bAnd(wsokK yW, wsokK bW))))))))

@[expose] noncomputable def ddWOK : Bool :=
  bAnd(eqLK (List.getD ddW (nat_lit 0) []) (List.getD eBW (nat_lit 0) []),
    bAnd(eqLK (List.getD ddW (nat_lit 1) []) (List.getD eBW (nat_lit 1) []),
      bAnd(eqLK (List.getD ddW (nat_lit 2) [])
          (appK (List.getD eBW (nat_lit 2) []) (List.getD eBW (nat_lit 0) [])),
        eqLK (List.getD ddW (nat_lit 3) [])
          (appK (List.getD eBW (nat_lit 2) []) (List.getD eBW (nat_lit 2) [])))))

@[expose] noncomputable def negPos : Bool :=
  Bool.not (posSlK G POS0 PTS0 PAR0 (fun k => Nat.succ (LAB0 k)) (nat_lit 0) (nat_lit 1024))

@[expose] noncomputable def negRoot : Bool :=
  Bool.not (allBlk (nat_lit 0) (rootK PAR0 (nat_lit 2)) (nat_lit 1024))

@[expose] noncomputable def negPassV0 : Bool :=
  Bool.not (passK POS0 PAR0 LAB0 G (List.map (fun s => (s.1, Bool.not s.2)) st) v0)

@[expose] noncomputable def negDdW : Bool :=
  Bool.not (eqLK (List.getD ddW (nat_lit 0) []) (List.getD eBW (nat_lit 1) []))

end CFSG.KD.Fi23Nt
