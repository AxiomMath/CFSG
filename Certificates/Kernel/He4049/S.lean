module

public import Certificates.Kernel.He4049.Fam
public import Certificates.Data.Kernel.Kc3DfsKB
import Certificates.Kernel.SporSch.Ru.RowsGen

set_option maxHeartbeats 0

public section

namespace CFSG.KD.He4049

open CFSG.KC.Kc3K

@[expose] noncomputable def famSB (c : Nat) : Bool :=
  dfsKRB 191 pr NB NM (leafKB pr ct) (Nat.mul c 16) (min 16 (191 - Nat.mul c 16))

theorem famS_eq (c : Nat) : famS c = famSB c :=
  dfsKR_eq 191 pr ct NB NM (Nat.mul c 16) (min 16 (191 - Nat.mul c 16))

end CFSG.KD.He4049

#kss_each CFSG.KD.He4049.SB CFSG.KD.He4049.famSB 12

namespace CFSG.KD.He4049.S

theorem c0 : famS (nat_lit 0) = true := (famS_eq (nat_lit 0)).trans SB.c0

theorem c1 : famS (nat_lit 1) = true := (famS_eq (nat_lit 1)).trans SB.c1

theorem c2 : famS (nat_lit 2) = true := (famS_eq (nat_lit 2)).trans SB.c2

theorem c3 : famS (nat_lit 3) = true := (famS_eq (nat_lit 3)).trans SB.c3

theorem c4 : famS (nat_lit 4) = true := (famS_eq (nat_lit 4)).trans SB.c4

theorem c5 : famS (nat_lit 5) = true := (famS_eq (nat_lit 5)).trans SB.c5

theorem c6 : famS (nat_lit 6) = true := (famS_eq (nat_lit 6)).trans SB.c6

theorem c7 : famS (nat_lit 7) = true := (famS_eq (nat_lit 7)).trans SB.c7

theorem c8 : famS (nat_lit 8) = true := (famS_eq (nat_lit 8)).trans SB.c8

theorem c9 : famS (nat_lit 9) = true := (famS_eq (nat_lit 9)).trans SB.c9

theorem c10 : famS (nat_lit 10) = true := (famS_eq (nat_lit 10)).trans SB.c10

theorem c11 : famS (nat_lit 11) = true := (famS_eq (nat_lit 11)).trans SB.c11

theorem all : ∀ (i : Nat), i < nat_lit 12 → famS i = true := fun i hi =>
  (famS_eq i).trans (SB.all i hi)

end CFSG.KD.He4049.S

end
