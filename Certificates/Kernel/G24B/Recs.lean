module

public import Certificates.Data.Kernel.Misc.F2BfsRec2
public import Certificates.Data.G24IdentModel
public import Certificates.Kernel.Misc.G24Data
import CFSG.Certificates.Kernel.Common.F2Bfs

public section

set_option maxRecDepth 100000

namespace CFSG.KD.G24B

open CFSG.KC.Misc.G24 CFSG.Quasithin.St84.G24Ident

@[expose] noncomputable def lettersOf (w : List (Fin 6 × Bool)) : List Nat :=
  List.rec (motive := fun _ => List Nat) List.nil
    (fun l _ ih => List.cons (Nat.add (Nat.mul 2 l.1.val) (Bool.rec (motive := fun _ => Nat) 0 1 l.2)) ih) w

@[expose] noncomputable def blowW (w : List (Fin 6 × Bool)) : Nat :=
  wordF4 CFSG.KD.Misc.G24.Gb (lettersOf w)

@[expose] def wQ1 : List (List (Fin 6 × Bool)) := pc1

@[expose] def wQ2 : List (List (Fin 6 × Bool)) := pc2

@[expose] def wA1 : List (List (Fin 6 × Bool)) := [a1, b1, k1]

@[expose] def wA2 : List (List (Fin 6 × Bool)) := [a2, b2, k2]

@[expose] def wH : List (List (Fin 6 × Bool)) := [k1, k2]

@[expose] noncomputable def GQ1 : List Nat := wQ1.map blowW
@[expose] noncomputable def GQ2 : List Nat := wQ2.map blowW
@[expose] noncomputable def GA1 : List Nat := wA1.map blowW
@[expose] noncomputable def GA2 : List Nat := wA2.map blowW
@[expose] noncomputable def GH : List Nat := wH.map blowW

end CFSG.KD.G24B

#kc_f2bfs CFSG.KD.G24B.EQ1 28 CFSG.KD.G24B.GQ1 4096 6 12
#kc_f2bfs CFSG.KD.G24B.EQ2 28 CFSG.KD.G24B.GQ2 4096 6 12
#kc_f2bfs CFSG.KD.G24B.EA1 28 CFSG.KD.G24B.GA1 4096 6 12
#kc_f2bfs CFSG.KD.G24B.EA2 28 CFSG.KD.G24B.GA2 4096 6 12
#kc_f2bfs CFSG.KD.G24B.EH 28 CFSG.KD.G24B.GH 4096 6 12

end
