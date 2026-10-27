module

public import Certificates.Data.Kernel.HNF26720K
public import CFSG.Certificates.Kernel.Fam.HNSeed.Data.Sel
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.NatItemsGz
import CFSG.Certificates.Kernel.Common.Repo

#kc_repo #kc_nat_items_gz CFSG.KD.HNF26720 "Certificates/Kernel/HNF26720/data/rk.items.gz" 2069942 229550249062905889
    (P 0 18) (Q 0 18) (U 0 18) (V 0 18) (K 0 18)
#kc_select CFSG.KD.HNF26720 PS P 18
#kc_select CFSG.KD.HNF26720 QS Q 18
#kc_select CFSG.KD.HNF26720 US U 18
#kc_select CFSG.KD.HNF26720 VS V 18
#kc_select CFSG.KD.HNF26720 KS K 18

public section

namespace CFSG.KD.HNF26720

noncomputable abbrev mul : Nat → Nat → Nat :=
  CFSG.KC.Ord.mulR 5 13 1729 133 9 CFSG.KD.FamHNSeed.L CFSG.KD.FamHNSeed.H CFSG.KD.FamHNSeed.CM
    CFSG.KD.FamHNSeed.RM

noncomputable abbrev vld : Nat → Bool :=
  CFSG.KC.Ord.validM 5 229957 CFSG.KD.FamHNSeed.L CFSG.KD.FamHNSeed.H

@[expose] noncomputable def Bi : Nat := mul (CFSG.KD.FamHNSeed.RW 2) (CFSG.KD.FamHNSeed.RW 2)

@[expose] noncomputable def pairW (w : List Int) (i : Nat) : Bool :=
  CFSG.KC.HNF26720.pairOK mul vld CFSG.KD.FamHNSeed.L CFSG.KD.FamHNSeed.H CFSG.KD.FamHNSeed.ONE
    (CFSG.KD.FamHNSeed.RW 1) (CFSG.KD.FamHNSeed.RW 2) Bi PS QS US VS KS w (2 * i)

@[expose] noncomputable def commW (w : List Int) : Bool :=
  CFSG.KC.HNF26720.commOK mul (CFSG.KD.FamHNSeed.RW 1) (CFSG.KD.FamHNSeed.RW 2) Bi
    CFSG.KD.FamHNSeed.ONE w

@[expose] noncomputable def distOK : Bool :=
  (List.range 9).all fun i => (List.range 9).all fun j =>
    i == j || !(KS (2 * i) == KS (2 * j)) || !(KS (2 * i + 1) == KS (2 * j + 1))

end CFSG.KD.HNF26720

end
