module

import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.HarnessGzTree
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo
public import Certificates.Kernel.Sporadic.Fi24Net.Data
public import Certificates.Data.Kernel.Spor.Fi24Pc

#kc_repo #kc_ktree_gz CFSG.KD.Fi24Pc X0 "Certificates/Kernel/Sporadic/Fi24Pc/data/pc0.bin.gz" 65536 4 2424832 3374793118785896410
#kc_repo #kc_ktree_gz CFSG.KD.Fi24Pc X1 "Certificates/Kernel/Sporadic/Fi24Pc/data/pc1.bin.gz" 65536 4 2424832 6812701078681063374
#kc_repo #kc_ktree_gz CFSG.KD.Fi24Pc X2 "Certificates/Kernel/Sporadic/Fi24Pc/data/pc2.bin.gz" 65536 4 2424832 16910138633129304063
#kc_repo #kc_ktree_gz CFSG.KD.Fi24Pc X3 "Certificates/Kernel/Sporadic/Fi24Pc/data/pc3.bin.gz" 65536 4 2424832 9903135248916583205
#kc_repo #kc_ktree_gz CFSG.KD.Fi24Pc X4 "Certificates/Kernel/Sporadic/Fi24Pc/data/pc4.bin.gz" 65536 4 2424832 6193541240755258976
#kc_repo #kc_ktree_gz CFSG.KD.Fi24Pc X5 "Certificates/Kernel/Sporadic/Fi24Pc/data/pc5.bin.gz" 65536 4 2424832 1102686570193150544
#kc_repo #kc_ktree_gz CFSG.KD.Fi24Pc X6 "Certificates/Kernel/Sporadic/Fi24Pc/data/pc6.bin.gz" 65536 4 2424832 5836669515680282799
#kc_repo #kc_ktree_gz CFSG.KD.Fi24Pc X7 "Certificates/Kernel/Sporadic/Fi24Pc/data/pc7.bin.gz" 65536 4 2424832 17162015330233988473
#kc_repo #kc_ktree_gz CFSG.KD.Fi24Pc X8 "Certificates/Kernel/Sporadic/Fi24Pc/data/pc8.bin.gz" 65536 4 2424832 10358077874869466252
#kc_repo #kc_ktree_gz CFSG.KD.Fi24Pc X9 "Certificates/Kernel/Sporadic/Fi24Pc/data/pc9.bin.gz" 65536 4 2424832 7436905607040070886
#kc_repo #kc_ktree_gz CFSG.KD.Fi24Pc X10 "Certificates/Kernel/Sporadic/Fi24Pc/data/pc10.bin.gz" 65536 4 2424832 14156425561659670410
#kc_repo #kc_ktree_gz CFSG.KD.Fi24Pc X11 "Certificates/Kernel/Sporadic/Fi24Pc/data/pc11.bin.gz" 65536 4 2424832 17034327961551952890
#kc_repo #kc_ktree_gz CFSG.KD.Fi24Pc X12 "Certificates/Kernel/Sporadic/Fi24Pc/data/pc12.bin.gz" 65536 4 2424832 7182969156639011844
#kc_repo #kc_ktree_gz CFSG.KD.Fi24Pc X13 "Certificates/Kernel/Sporadic/Fi24Pc/data/pc13.bin.gz" 65536 4 2424832 3014114532745653952
#kc_repo #kc_ktree_gz CFSG.KD.Fi24Pc X14 "Certificates/Kernel/Sporadic/Fi24Pc/data/pc14.bin.gz" 65536 4 2424832 18272575633460270303
#kc_repo #kc_ktree_gz CFSG.KD.Fi24Pc X15 "Certificates/Kernel/Sporadic/Fi24Pc/data/pc15.bin.gz" 65536 4 2424832 7607886945133666835

#kc_repo #kc_json_gz CFSG.KD.Fi24Pc.J "Certificates/Kernel/Sporadic/Fi24Pc/data/pc.json.gz" 354541
  11705157318504880490
  (words : List (List Nat)) (defs : List Nat) (PW : Nat) (CJ : Nat) (OP : Nat) (TB : Nat)
  (B : List Nat) (gens : List (List Nat)) (orb : List (List Nat)) (levels : List (List Nat))
  (tags : List (List Nat)) (fin : List Nat) (RP : Nat) (tgt : List Nat) (trans : List (List Nat))
  (tw : List (List Nat))

public section

namespace CFSG.KD.Fi24Pc

open CFSG.KC CFSG.KC.Loop CFSG.KC.Fi24Net CFSG.KC.Fi24Pc

@[expose] noncomputable def XW (j l : Nat) : Nat :=
  nIf(Nat.blt j (nat_lit 8),
    nIf(Nat.blt j (nat_lit 4),
      nIf(Nat.blt j (nat_lit 2), nIf(Nat.beq j (nat_lit 0), X0 l, X1 l),
        nIf(Nat.beq j (nat_lit 2), X2 l, X3 l)),
      nIf(Nat.blt j (nat_lit 6), nIf(Nat.beq j (nat_lit 4), X4 l, X5 l),
        nIf(Nat.beq j (nat_lit 6), X6 l, X7 l))),
    nIf(Nat.blt j (nat_lit 12),
      nIf(Nat.blt j (nat_lit 10), nIf(Nat.beq j (nat_lit 8), X8 l, X9 l),
        nIf(Nat.beq j (nat_lit 10), X10 l, X11 l)),
      nIf(Nat.blt j (nat_lit 14), nIf(Nat.beq j (nat_lit 12), X12 l, X13 l),
        nIf(Nat.beq j (nat_lit 14), X14 l, nIf(Nat.beq j (nat_lit 15), X15 l, nat_lit 0)))))

@[expose] noncomputable def nck (j : Nat) : Bool := netOK (XW j)

@[expose] noncomputable def wck (g : Nat) : Bool :=
  pcwOK CFSG.KD.Fi24Net.NW XW J.words J.defs (Nat.div g (nat_lit 19)) (Nat.mod g (nat_lit 19))

@[expose] noncomputable def rck (j : Nat) : Bool := relOK (CFSG.KC.Fi24NetPt.letN XW) J.PW J.CJ j

@[expose] noncomputable def tck (k : Nat) : Bool :=
  andB (oOK J.OP) (allBelow (nat_lit 729) (nat_lit 12) (fun a => tabOK XW J.OP J.TB k a))

@[expose] noncomputable def bck (l : Nat) : Bool := orbOK J.TB J.B (nthL J.gens l) (nthL J.orb l) l

@[expose] noncomputable def kck (i : Nat) : Bool :=
  kidsOK i (nthL J.levels i) (nthL J.levels (Nat.add i 1)) (nthL J.tags i)

@[expose] noncomputable def pck (g : Nat) : Bool :=
  (fun i s => repsOK J.TB J.B i (takeL (nat_lit 64) (dropL (Nat.mul (nat_lit 64) s) (nthL J.levels i)))
    (takeL (nat_lit 64) (dropL (Nat.mul (nat_lit 64) s) (nthL J.tags i))))
    (Nat.div g (nat_lit 32)) (Nat.mod g (nat_lit 32))

@[expose] noncomputable def fck (g : Nat) : Bool :=
  finsOK J.TB J.B J.RP (takeL (nat_lit 64) (dropL (Nat.mul (nat_lit 64) g) (nthL J.levels (nat_lit 16))))
    (takeL (nat_lit 64) (dropL (Nat.mul (nat_lit 64) g) J.fin))

@[expose] noncomputable def xone (l : Nat) : Bool :=
  bAnd(Nat.blt (nth J.tgt l) (nat_lit 5),
    transOK CFSG.KD.Fi24Net.NW XW J.RP l (nthL J.tw (nth J.tgt l)) (nthL J.trans l))

@[expose] noncomputable def xck (g : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun m ih => bAnd(bIf(Nat.blt (Nat.add (Nat.mul (nat_lit 8) g) m) (nat_lit 824),
      xone (Nat.add (Nat.mul (nat_lit 8) g) m), true), ih)) (nat_lit 8)

@[expose] noncomputable def lck : Bool := andB (letOK J.words) (andB (letOK J.trans) (letOK J.tw))

end CFSG.KD.Fi24Pc

end
