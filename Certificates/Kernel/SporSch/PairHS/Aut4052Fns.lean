module

public import Certificates.Kernel.SporSch.PairHS.Aut4052Data
public import Certificates.Kernel.SporSch.PairHS.CntFns
public import Certificates.Data.Kernel.SporSch.SrchP
public import Certificates.Data.Kernel.SporSch.PairHeCnt

public section

namespace CertificateChecks.KernelSporSch.PHSA

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.SporSch CertificateChecks.KernelSporSch
open CFSG.QuasithinUnique.Ch1.SporAutHS

@[expose] noncomputable def ltrP (k : Nat) : Nat :=
  nIf(Nat.beq k 0, PHSC.S 0, nIf(Nat.blt k 4, PS0 (Nat.sub k 1), PHSC.S 1))

@[expose] noncomputable def wP (w : List Nat) (x : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun x => x)
    (fun k _ ih x => pg 12 (mask 12) (ltrP k) (ih x)) w x

@[expose] noncomputable def a0P (x : Nat) : Nat := pg 12 (mask 12) (PHSC.S 0) x

@[expose] noncomputable def a1P (x : Nat) : Nat := pg 12 (mask 12) (PHSC.S 1) x

@[expose] noncomputable def flt (f : Nat → Nat) : Bool :=
  bAnd(ordDL PHSCn.bs (fun x => wP l1Word (f x)) 5 [1],
    bAnd(ordDL PHSCn.bs (fun x => wP l2Word (f x)) 12 [6, 4], ordDL PHSCn.bs f 15 [5, 3]))

@[expose] noncomputable def vAt (q : Nat) : Nat := PA4.V.getD q 0

@[expose] noncomputable def srAt (q : Nat) : Nat :=
  srchPR 12 8 PHST.NR PHST.NR PHST.LT PHST.PT PHST.QT PHSC.LR PHSCn.bs (nat_lit 0) a0P
    (wP yWord) flt (Nat.mul q (nat_lit 154)) (nat_lit 154)

@[expose] noncomputable def sr (g r : Nat) : Bool :=
  Nat.beq (srAt (Nat.add (Nat.mul g 5) r)) (vAt (Nat.add (Nat.mul g 5) r))

@[expose] noncomputable def nfG (j : Nat) : Nat := PA4.nfg.getD j 0

@[expose] noncomputable def bindG (j r : Nat) : Bool :=
  PHSCn.bindR (nfG j) (PS0 j) (Nat.mul r 770)

@[expose] noncomputable def diAt (k : Nat) : Nat := PA4.di.getD k 0

@[expose] noncomputable def swAt (l : Nat) : List Nat := PA4.sw.getD l []

@[expose] noncomputable def eqB (f g : Nat → Nat) : Bool := eqOnL PHSCn.bs f g

@[expose] noncomputable def permB : Bool :=
  allN 3 (fun j => permOK 3850 12 (mask 12) (3850 * 12) (PS0 j) (pinvS 3850 12 (mask 12) (PS0 j)))

@[expose] noncomputable def smallB : Bool :=
  bAnd(hexTabK PS0T.chars 4 3850 12 3 PS0,
  bAnd(allN 3 (fun j => nfValidK 4 PHSC.LR (nfG j)),
  bAnd(nfValidK 4 PHSC.LR PA4.d,
  bAnd(allN 4 (fun k => eqB (fun x => a0P (wP [k] x)) (fun x => wP [k] (a0P x))),
  bAnd(eqB (fun x => wP bWord (a0P x)) (fun x => wP yWord (wP bWord x)),
  bAnd(eqB a1P (wP (t0Word ++ bWord ++ bWord ++ t1Word ++ bWord ++ bWord ++ bWord ++ bWord ++
      t2Word)),
  bAnd(ordDL PHSCn.bs (wP bWord) 15 [5, 3],
  bAnd(ordDL PHSCn.bs (fun x => wP l1Word (wP bWord x)) 5 [1],
  bAnd(ordDL PHSCn.bs (fun x => wP l2Word (wP bWord x)) 12 [6, 4],
  bAnd(allN 4 (fun k => bAnd(Nat.blt (diAt k) 512, eqB (fun x => PHSCn.nfp PA4.d (wP [k] x))
      (fun x => PHSCn.nfp (PHSCn.r2 (diAt k)) (PHSCn.nfp PA4.d x)))),
    allN 3 (fun l => bAnd((swAt l).all (fun k => Nat.blt k 4),
      eqB (fun x => PHSCn.nfp (PHSCn.r2 (PHSCn.gr2 l)) (PHSCn.nfp PA4.d x))
        (fun x => PHSCn.nfp PA4.d (wP (swAt l) x))))))))))))))

end CertificateChecks.KernelSporSch.PHSA

end
