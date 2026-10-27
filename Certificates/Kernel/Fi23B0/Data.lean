module

public import Certificates.Kernel.Fi23K.ChkDefs
import CFSG.Certificates.Kernel.Common.HarnessGzTree
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

#kc_repo #kc_ktree_gz CFSG.KD.Fi23B0 TR "Certificates/Kernel/Fi23B0/data/tree.bin.gz" 128 4 137984 14863394903245284637
#kc_repo #kc_json_gz CFSG.KD.Fi23B0 "Certificates/Kernel/Fi23B0/data/syl.json.gz" 1258 12705671633536009432 (sylW : List (List Nat))

public section

namespace CFSG.KD.Fi23B0

open CFSG.KC.Enum CFSG.KS.TBfs CFSG.KS.PC CFSG.KS.PEnum CFSG.KD.Fi23K

@[expose] noncomputable def off (t : Nat) : Nat :=
  List.getD [0, 22, 1012, 1034, 1056] t (nat_lit 0)

@[expose] noncomputable def TB (t r : Nat) : Nat := TR (Nat.add (off t) r)

@[expose] noncomputable def hdK (root : Nat) : Bool :=
  tbfsHdK (nat_lit 31671) root (nat_lit 693) (TB (nat_lit 0)) (TB (nat_lit 1)) (TB (nat_lit 2))
    (TB (nat_lit 3))

@[expose] noncomputable def ptsK (i lo len : Nat) : Bool :=
  tbfsSlK (nat_lit 31671) (nat_lit 693) (lvK LL BB (nat_lit 24) i).length LL
    (lvAt LL BB (nat_lit 24) i) (TB (nat_lit 0)) (TB (nat_lit 1)) (TB (nat_lit 2))
    (TB (nat_lit 3)) (TB (nat_lit 4)) lo len

@[expose] noncomputable def hdB : Bool := hdK (nat_lit 28381)

@[expose] noncomputable def ptsB (lo len : Nat) : Bool := ptsK (nat_lit 2) lo len

@[expose] noncomputable def wvL (w : List Int) (x : Nat) : Nat :=
  List.foldr (fun z y => LL (Int.toNat z) y) x w

@[expose] noncomputable def inS (p : Nat) : Bool :=
  bIf(Nat.beq p (nat_lit 2776), true, bIf(Nat.beq p (nat_lit 14566), true,
    Nat.beq p (nat_lit 18249)))

@[expose] noncomputable def presS (w : List Int) : Bool :=
  bAnd(inS (wvL w (nat_lit 2776)), bAnd(inS (wvL w (nat_lit 14566)),
    inS (wvL w (nat_lit 18249))))

@[expose] noncomputable def ltW (w : List Int) : Bool :=
  w.all fun z => Nat.blt (Int.toNat z) (nat_lit 24)

@[expose] noncomputable def maps3 (w : List Int) (a b c a' b' c' : Nat) : Bool :=
  bAnd(Nat.beq (wvL w a) a', bAnd(Nat.beq (wvL w b) b', Nat.beq (wvL w c) c'))

@[expose] noncomputable def sylK (ws : List (List Int)) : Bool :=
  bAnd(ws.all fun w => bAnd(ltW w, bAnd(Nat.beq (wvL w (nat_lit 2776)) (nat_lit 2776), presS w)),
    maps3 (ws.getD (nat_lit 1) []) (nat_lit 2776) (nat_lit 14566) (nat_lit 18249) (nat_lit 2776)
      (nat_lit 18249) (nat_lit 14566))

@[expose] noncomputable def sylZ : List (List Int) := sylW.map (List.map Int.ofNat)

@[expose] noncomputable def sylB : Bool := sylK sylZ

@[expose] def moverW : List Int :=
  [20, 16, 16, 19, 16, 16, 12, 15, 17, 22, 8, 11, 8, 15, 19, 6, 8, 12, 22, 2, 14, 3, 12, 3]

@[expose] def gW : List Int := [8, 8, 8, 2, 2, 13, 11, 8, 4]

@[expose] noncomputable def moverK (w : List Int) : Bool :=
  bAnd(ltW w, maps3 w (nat_lit 2776) (nat_lit 14566) (nat_lit 18249) (nat_lit 14566)
    (nat_lit 2776) (nat_lit 18249))

@[expose] noncomputable def conjK (w : List Int) : Bool :=
  bAnd(ltW w, maps3 w (nat_lit 0) (nat_lit 1) (nat_lit 28381) (nat_lit 2776) (nat_lit 14566)
    (nat_lit 18249))

@[expose] noncomputable def moverB : Bool := moverK moverW

@[expose] noncomputable def conjB : Bool := conjK gW

end CFSG.KD.Fi23B0

end
