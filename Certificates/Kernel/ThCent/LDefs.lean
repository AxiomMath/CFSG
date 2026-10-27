module

public import Certificates.Data.Kernel.ThCent.List
public import Certificates.Kernel.ThCent.DataL
public import Certificates.Kernel.ThCent.Data
public import CFSG.Certificates.Kernel.Th.S.Data.Sm_Sel
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSevenData
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThFiveData

public section

namespace CFSG.KD.ThCent.L

open CFSG.KC.Th CFSG.KC.Th.BigS CFSG.KC.ThCent
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSevenNative
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThFiveNative

@[expose] noncomputable def V7 (r : Nat) : Nat := L7.V.getD r 0

@[expose] noncomputable def V5 (r : Nat) : Nat := L5.V.getD r 0

@[expose] noncomputable def pin7 (r : Nat) : Bool :=
  Nat.beq (runPk ThS.c ThS.rm ThS.ONE prog7 (initPk (ThS.RBf 1) (ThS.RBf 2) ThS.ONE) r) (V7 r)

@[expose] noncomputable def pin5 (r : Nat) : Bool :=
  Nat.beq (runPk ThS.c ThS.rm ThS.ONE prog5 (initPk (ThS.RBf 1) (ThS.RBf 2) ThS.ONE) r) (V5 r)

@[expose] noncomputable def pair7 : Bool := pairOK7 ThS.c ThS.rm ThS.ONE (V7 24) (V7 25)

@[expose] noncomputable def conj7F (a : Nat) : Bool :=
  (List.range 7).all fun b => Bool.or (Nat.beq (a + b) 0)
    (conjOK7 ThS.c ThS.rm ThS.ONE V7 (V7 24) (V7 25) W.Z7 a b (conj7[7 * a + b]!))

@[expose] noncomputable def ch7 (k : Nat) : Bool :=
  chunkOK (eltRec ThS.c ThS.rm ThS.ONE V7 W.Z7 24) L7.E (k * 49) 49

@[expose] noncomputable def dist7 : Bool := distinctL (L7.E.map fun e => e.2.2)

@[expose] noncomputable def C5 : Nat :=
  mulB ThS.c ThS.rm (mulB ThS.c ThS.rm (mulB ThS.c ThS.rm (V5 94) (V5 105))
    (powB ThS.c ThS.rm ThS.ONE (V5 94) 4 (nat_lit 3))) (powB ThS.c ThS.rm ThS.ONE (V5 105) 4 (nat_lit 3))

@[expose] noncomputable def cube5 : Bool := strictF C5 fun C => cubeOK5 ThS.c ThS.rm ThS.ONE (V5 94) (V5 105) C

@[expose] noncomputable def conj5F (i : Nat) : Bool := strictF C5 fun C =>
  (List.range 25).all fun jk => Bool.or (Nat.beq (i + jk) 0)
    (conjOK5 ThS.c ThS.rm ThS.ONE V5 (V5 94) (V5 105) C i (jk / 5) (jk % 5) (conj5[25 * i + jk]!))

@[expose] noncomputable def row5F (i : Nat) : Bool := strictF C5 fun C =>
  (List.range 25).all fun jk =>
    cubeRowOK ThS.c ThS.rm ThS.ONE (V5 94) (V5 105) C i (jk / 5) (jk % 5) (L5.RC.getD (25 * i + jk) 0)

@[expose] noncomputable def ch5 (k : Nat) : Bool := strictF C5 fun C =>
  chunkOK (eltRec ThS.c ThS.rm ThS.ONE V5 C 24) L5.E (k * 50) 50

@[expose] noncomputable def dist5 : Bool := distinctL (L5.E.map fun e => e.2.2)

@[expose] noncomputable def distC : Bool := distinctL L5.RC

end CFSG.KD.ThCent.L

end
