
module

public import Certificates.Kernel.Sporadic.ON5.Data
public import Certificates.Kernel.Sporadic.OddCore.ON2129
public import Certificates.Data.Kernel.Spor.ChainFK
public import Certificates.Kernel.Sporadic.ON3.Defs

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.ON5K

open CFSG.ONSchreier CFSG.KC.Enum CFSG.KS CFSG.KS.ON CFSG.KS.CB CFSG.KS.CH CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum

open CertificateChecks.KernelSpor.ON3 (lv3 nat3)

@[expose] noncomputable def mSl (s : Nat) : Bool :=
  penumSlK 120 7 (mask 7) (Nat.mul 120 7) false ON5M.G ON5M.GI ON5M.k ON5M.cnt ON5M.T ON5M.PL
    ON5M.POS ON5M.SRT ON5M.SRI (Nat.mul s 2016) 2016

@[expose] noncomputable def dG (j : Nat) : Nat := List.getD ON5.dPack j 0

@[expose] noncomputable def qD (i : Nat) : Bool :=
  strictB (ON5M.T i) fun t => allN 4 fun j =>
    Nat.beq (pcomp 120 7 (mask 7) t (dG j)) (pcomp 120 7 (mask 7) (dG j) t)

@[expose] noncomputable def selIn (s : Nat) : List Nat :=
  ON5.dSel.filter fun i => decide (2016 * s ≤ i) && decide (i < 2016 * s + 2016)

@[expose] noncomputable def dSelS (s : Nat) : Bool := selFrom qD 2016 (Nat.mul s 2016) (selIn s)

@[expose] noncomputable def qT (i : Nat) : Bool :=
  strictB (T32E.T i) fun t => allN 6 fun j =>
    Nat.beq (pcomp 32 6 (mask 6) t (T32E.G j)) (pcomp 32 6 (mask 6) (T32E.G j) t)

@[expose] noncomputable def tSelOK : Bool :=
  bAnd(selFrom qT 512 0 ON5.tSel, bAnd(Nat.beq (T32E.T (List.getD ON5.tSel 0 0)) (pidn 32 6),
    bAnd(bindArrK Data.T32z 32 6 (T32E.T (List.getD ON5.tSel 1 0)),
      Nat.beq ON5.tSel.length 2)))

@[expose] noncomputable def dF (j x : Nat) : Nat := tab ON5T.DF (Nat.add (Nat.mul 120 j) x)
@[expose] noncomputable def dFI (j x : Nat) : Nat := tab ON5T.DI (Nat.add (Nat.mul 120 j) x)
@[expose] noncomputable def sF (j x : Nat) : Nat := tab ON5T.SF (Nat.add (Nat.mul 120 j) x)
@[expose] noncomputable def sFI (j x : Nat) : Nat := tab ON5T.SI (Nat.add (Nat.mul 120 j) x)
@[expose] noncomputable def zI (x : Nat) : Nat := tab ON5T.ZI x

@[expose] noncomputable def sPTS : Nat → Nat → Nat := lv3 ON5LM.PTS0 ON5LM.PTS1 ON5LM.PTS2
@[expose] noncomputable def sPOS : Nat → Nat → Nat := lv3 ON5LM.POS0 ON5LM.POS1 ON5LM.POS2
@[expose] noncomputable def sPAR : Nat → Nat → Nat := lv3 ON5LM.PAR0 ON5LM.PAR1 ON5LM.PAR2
@[expose] noncomputable def sLAB : Nat → Nat → Nat := lv3 ON5LM.LAB0 ON5LM.LAB1 ON5LM.LAB2
@[expose] noncomputable def sMr : Nat → Nat := nat3 ON5LM.M0 ON5LM.M1 ON5LM.M2
@[expose] noncomputable def sIdxL (i : Nat) : List Nat := List.getD [ON5.idx0, ON5.idx1, ON5.idx2] i []
@[expose] noncomputable def sIDX (i t : Nat) : Nat := List.getD (sIdxL i) t 0
@[expose] noncomputable def sLEN (i : Nat) : Nat := (sIdxL i).length
@[expose] noncomputable def sB (k : Nat) : Nat := Data.M120Chain.base[k]!

@[expose] noncomputable def smallOK : Bool :=
  bAnd(allN 4 (fun j => allN 120 fun x => bAnd(Nat.beq (dF j x) ((Data.D120Generators[j]!)[x]!),
      bAnd(Nat.blt (dF j x) 120, bAnd(Nat.blt (dFI j x) 120, Nat.beq (dFI j (dF j x)) x)))),
  bAnd(allN Data.M120Chain.strongGenerators.size (fun j => allN 120 fun x =>
      bAnd(Nat.beq (sF j x) ((Data.M120Chain.strongGenerators[j]!)[x]!),
      bAnd(Nat.blt (sF j x) 120, bAnd(Nat.blt (sFI j x) 120, Nat.beq (sFI j (sF j x)) x)))),
  bAnd(allN 32 (fun x => bAnd(Nat.blt (Data.T32z[x]!) 32,
      bAnd(Nat.blt (zI x) 32, Nat.beq (zI (Data.T32z[x]!)) x))),
  bAnd(allN 3 (fun i => bAnd(idxOK sF Data.M120Chain.strongGenerators.size sB i (sIDX i) (sLEN i),
      bAnd(cbHead 120 (sMr i) (sB i) (sPTS i) (sPAR i) (sLAB i),
      bAnd(allN (sMr i) (cbPt 120 (sMr i) (Nat.mul 2 (sLEN i)) (stepX sF sFI (sIDX i) (sLEN i))
          (sPTS i) (sPOS i) (sPAR i) (sLAB i)),
        allN 120 (cbPos 120 (sMr i) (sPTS i) (sPOS i)))))),
    allN 4 fun j => siftFull3 120 sPOS sPAR sLAB sMr (fun i => invX sF sFI (sIDX i) (sLEN i)) sB
      (dF j)))))

end CertificateChecks.KernelSpor.ON5K

end
