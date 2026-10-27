module

public import Certificates.Kernel.Sporadic.ONPar.Data
public import Certificates.Kernel.Sporadic.ON3.Small

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.ONPar

open CFSG.KC.Enum CFSG.KS CFSG.KS.ON CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.Mathieu
open CFSG.ONSchreier
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.ONPar
open CertificateChecks.KernelSpor.ON3 (mG bposK blkK)

@[expose] noncomputable def pk (i : Nat) : Nat := nget PK i

@[expose] noncomputable def c32 (p q : Nat) : Nat := pcomp 32 6 (mask 6) p q

@[expose] noncomputable def c120 (p q : Nat) : Nat := pcomp 120 7 (mask 7) p q

@[expose] noncomputable def tInvOK : Bool :=
  bAnd(Nat.beq (List.length tInv) 512, allN 512 fun j => strictB (nget tInv j) fun q =>
    bAnd(Nat.blt q 512, Nat.beq (c32 (T32E.T q) (T32E.T j)) (pidn 32 6)))

@[expose] noncomputable def cgOK (s : Nat) : Bool :=
  allN 512 fun j => strictB (OME.T s) fun a => strictB (T32E.T j) fun b =>
    strictB (ONPC.G (Nat.add (Nat.mul s 512) j)) fun g =>
    bAnd(Nat.beq g (c32 (c32 (c32 a b) a) (T32E.T (nget tInv j))),
      canonK 32 6 (mask 6) (32 * 6) g)

@[expose] noncomputable def inFour (t : Nat) : Bool :=
  bIf(Nat.beq t (pidn 32 6), true, bIf(Nat.beq t (pk 0), true, bIf(Nat.beq t (pk 1), true,
    Nat.beq t (c32 (pk 0) (pk 1)))))

@[expose] noncomputable def inC (t : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) false (fun i ih => bIf(Nat.beq (ONPC.T i) t, true, ih)) ONPC.cnt

@[expose] noncomputable def cEnumOK : Bool :=
  bAnd(Nat.beq ONPC.k 4096, bAnd(penumHdK (pidn 32 6) ONPC.cnt 16 ONPC.T ONPC.PL,
  bAnd(penumSlK 32 6 (mask 6) (32 * 6) false ONPC.G ONPC.GI ONPC.k ONPC.cnt ONPC.T ONPC.PL
    ONPC.POS ONPC.SRT ONPC.SRI 0 16,
  bAnd(allN ONPC.cnt (fun i => inFour (ONPC.T i)), bAnd(inC (pk 0), inC (pk 1))))))

@[expose] noncomputable def mbK (j b : Nat) : Nat := bposK (mG j (Data.quotientBlocks[b]!)[0]!)

@[expose] noncomputable def bindOK : Bool :=
  bAnd(Nat.beq (List.length PK) 8,
  bAnd(bindArrK Data.T32z 32 6 (pk 0), bAnd(canonK 32 6 (mask 6) (32 * 6) (pk 0),
  bAnd(bindArrK onpV32 32 6 (pk 1), bAnd(canonK 32 6 (mask 6) (32 * 6) (pk 1),
  bAnd(bindArrK Data.quotientConjugator 120 7 (pk 2), bAnd(canonK 120 7 (mask 7) 840 (pk 2),
  bAnd(canonK 120 7 (mask 7) 840 (pk 3), bAnd(Nat.beq (c120 (pk 3) (pk 2)) (pidn 120 7),
  bAnd(bindArrK onpVB 120 7 (pk 4), bAnd(canonK 120 7 (mask 7) 840 (pk 4),
    allN 3 fun j => strictB (pk (Nat.add 5 j)) fun p =>
      bAnd(blkK (mG j) (mbK j), bAnd(canonK 120 7 (mask 7) 840 p,
        allN 120 fun b => Nat.beq (mbK j b) (pg 7 (mask 7) p b))))))))))))))

@[expose] noncomputable def oGenOK : Bool :=
  bAnd(Nat.beq ONPO.k 3, bAnd(Nat.beq ONPO.R (c120 (c120 (pk 2) (pk 4)) (pk 3)),
    allN 3 fun j => bAnd(Nat.beq (ONPO.G j) (c120 (c120 (pk 2) (pk (Nat.add 5 j))) (pk 3)),
      bAnd(canonK 120 7 (mask 7) 840 (ONPO.G j), bAnd(canonK 120 7 (mask 7) 840 (ONPO.GI j),
        Nat.beq (c120 (ONPO.GI j) (ONPO.G j)) (pidn 120 7))))))

@[expose] noncomputable def oHdOK : Bool :=
  bAnd(Nat.beq ONPO.cnt 315, penumHdK ONPO.R ONPO.cnt 400 ONPO.T ONPO.PL)

@[expose] noncomputable def oEnumOK (s : Nat) : Bool :=
  penumSlK 120 7 (mask 7) 840 true ONPO.G ONPO.GI ONPO.k ONPO.cnt ONPO.T ONPO.PL ONPO.POS
    ONPO.SRT ONPO.SRI (Nat.mul s 105) 105

end CertificateChecks.KernelSpor.ONPar

end
