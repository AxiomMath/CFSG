module

public import Certificates.Data.Kernel.RuIdx2.Data
public import Certificates.Data.Kernel.RuIdx2K
public import Certificates.Kernel.Ru4120.T
import CFSG.Certificates.Kernel.Common.Harness

public section

#kc_select CFSG.KD.RuIdx2 PSr PS_ 256
#kc_select CFSG.KD.RuIdx2 XW XW_ 839
#kc_select CFSG.KD.RuIdx2 R0 R0_ 1684
#kc_select CFSG.KD.RuIdx2 R1 R1_ 1612
#kc_select CFSG.KD.RuIdx2 R2 R2_ 1633
#kc_select CFSG.KD.RuIdx2 R3 R3_ 1555
#kc_select CFSG.KD.RuIdx2 R4 R4_ 1535
#kc_select CFSG.KD.RuIdx2 R5 R5_ 1499
#kc_select CFSG.KD.RuIdx2 R6 R6_ 1471
#kc_listDispatch CFSG.KD.RuIdx2 E0 E0_ 27
#kc_listDispatch CFSG.KD.RuIdx2 E1 E1_ 26
#kc_listDispatch CFSG.KD.RuIdx2 E2 E2_ 26
#kc_listDispatch CFSG.KD.RuIdx2 E3 E3_ 25
#kc_listDispatch CFSG.KD.RuIdx2 E4 E4_ 24
#kc_listDispatch CFSG.KD.RuIdx2 E5 E5_ 24
#kc_listDispatch CFSG.KD.RuIdx2 E6 E6_ 23
#kc_listDispatch CFSG.KD.RuIdx2 M0 M0_ 27
#kc_listDispatch CFSG.KD.RuIdx2 M1 M1_ 27
#kc_listDispatch CFSG.KD.RuIdx2 M2 M2_ 27
#kc_listDispatch CFSG.KD.RuIdx2 M3 M3_ 27
#kc_listDispatch CFSG.KD.RuIdx2 M4 M4_ 27
#kc_listDispatch CFSG.KD.RuIdx2 M5 M5_ 27
#kc_listDispatch CFSG.KD.RuIdx2 M6 M6_ 27

namespace CFSG.KD.RuIdx2

open CFSG.KC.RuIdx2 CFSG.KC.Enum

@[expose] noncomputable def LC (c : Nat) : Nat :=
  nIf(Nat.beq c (nat_lit 0), Ru4120.TF (nat_lit 0), nIf(Nat.beq c (nat_lit 1), Ru4120.TF (nat_lit 1),
  nIf(Nat.beq c (nat_lit 2), Ru4120.TF (nat_lit 163), nIf(Nat.beq c (nat_lit 3), Ru4120.TF (nat_lit 172),
  nIf(Nat.beq c (nat_lit 4), Ru4120.TF (nat_lit 185), nIf(Nat.beq c (nat_lit 5), Ru4120.TF (nat_lit 198),
  nIf(Nat.beq c (nat_lit 6), Ru4120.TF (nat_lit 203), nIf(Nat.beq c (nat_lit 7), Ru4120.TF (nat_lit 207),
  nIf(Nat.beq c (nat_lit 8), Ru4120.TF (nat_lit 0), Ru4120.TF (nat_lit 76))))))))))

@[expose] noncomputable def IL (c : Nat) : Nat :=
  fld(nat_lit 69846132120, Nat.shiftLeft c (nat_lit 2), nat_lit 15)

@[expose] noncomputable def IdL (c : Nat) : Nat := c

@[expose] noncomputable def psi (k : Nat) : Nat :=
  fld(PSr (Nat.shiftRight k (nat_lit 6)), Nat.mul (nat_lit 3) (Nat.land k (nat_lit 63)), nat_lit 7)

@[expose] def Bs : List Nat := [0, 1, 2, 3, 4]

@[expose] noncomputable def sel7 {α : Type} (u : Nat) (x0 x1 x2 x3 x4 x5 x6 : α) : α :=
  Bool.rec (motive := fun _ => α) (Bool.rec (motive := fun _ => α)
    (Bool.rec (motive := fun _ => α) (Bool.rec (motive := fun _ => α)
      (Bool.rec (motive := fun _ => α) (Bool.rec (motive := fun _ => α) x6 x5 (Nat.beq u (nat_lit 5)))
        x4 (Nat.beq u (nat_lit 4))) x3 (Nat.beq u (nat_lit 3))) x2 (Nat.beq u (nat_lit 2)))
      x1 (Nat.beq u (nat_lit 1))) x0 (Nat.beq u (nat_lit 0))

@[expose] noncomputable def vm (u : Nat) : Nat := sel7 u 1 2 4 3 5 6 7

@[expose] noncomputable def tau (u : Nat) : Nat := sel7 u 2 3 4 2 2 3 2

@[expose] noncomputable def nr (u : Nat) : Nat := sel7 u 4 4 4 3 3 3 2

@[expose] noncomputable def nR (u : Nat) : Nat := sel7 u 1684 1612 1633 1555 1535 1499 1471

@[expose] noncomputable def RG (u l : Nat) : Nat :=
  List.getD (sel7 u [769, 143875, 1025, 147971] [513, 205571, 1025, 213763]
    [513, 271363, 769, 275459] [8962, 1025, 147971] [769, 143875, 9218] [513, 205571, 13314]
    [8962, 9218]) l 0

@[expose] noncomputable def RW (u i : Nat) : Nat := sel7 u (R0 i) (R1 i) (R2 i) (R3 i) (R4 i) (R5 i) (R6 i)

@[expose] noncomputable def E (u c : Nat) : List Nat := sel7 u (E0 c) (E1 c) (E2 c) (E3 c) (E4 c) (E5 c) (E6 c)

@[expose] noncomputable def M (u c : Nat) : List Nat := sel7 u (M0 c) (M1 c) (M2 c) (M3 c) (M4 c) (M5 c) (M6 c)

@[expose] noncomputable def ex (u : Nat) : List Nat := sel7 u [] [] [1640, 1648] [] [] [] []

@[expose] noncomputable def WX (u : Nat) : Nat := sel7 u WX0 WX1 WX2 WX3 WX4 WX5 WX6

@[expose] noncomputable def WE (u : Nat) : Nat := sel7 u WE0 WE1 WE2 WE3 WE4 WE5 WE6

@[expose] noncomputable def WK (u : Nat) : Nat := sel7 u WK0 WK1 WK2 WK3 WK4 WK5 WK6

@[expose] noncomputable def famE (u c : Nat) : Bool :=
  (fun L => bAnd(Nat.beq (List.length L)
      (Nat.min (nat_lit 64) (Nat.sub (Nat.sub (nR u) (nat_lit 1)) (Nat.shiftLeft c (nat_lit 6)))),
    allIdx (fun n it => edgeK LC IL (RG u) (RW u) Bs (nr u) n it)
      (Nat.add (nat_lit 1) (Nat.shiftLeft c (nat_lit 6))) L)) (E u c)

@[expose] noncomputable def famM (u c : Nat) : Bool :=
  (fun L => bAnd(Nat.beq (List.length L)
      (Nat.min (nat_lit 64) (Nat.sub (nat_lit 1678) (Nat.shiftLeft c (nat_lit 6)))),
    allIdx (fun p it => bIf(memN p (ex u), true,
        matchK LC (RW u) XW psi Ru4120.TF Ru4120.eu Ru4120.ev Bs (nR u) (vm u) (tau u) p it))
      (Nat.shiftLeft c (nat_lit 6)) L)) (M u c)

@[expose] noncomputable def famW (u : Nat) : Bool :=
  witK LC IL (RG u) (RW u) psi Ru4120.TF Ru4120.eu Ru4120.ev Bs (nr u) (vm u) (WX u) (WE u) (WK u)

@[expose] noncomputable def famL (c : Nat) : Bool :=
  (List.range 512).all fun t => labK psi Ru4120.tg (Nat.add (Nat.mul c (nat_lit 512)) t)

@[expose] noncomputable def famI (c : Nat) : Bool := letK LC IL (nat_lit 4060) c

@[expose] noncomputable def famQ (c : Nat) : Bool :=
  letK LC IdL (nat_lit 4060) (List.getD [0, 2, 3, 4] c 0)

end CFSG.KD.RuIdx2

end
