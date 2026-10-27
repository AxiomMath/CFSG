module

public import Certificates.Kernel.Sporadic.OddCore.J2CnK
public import Certificates.Kernel.Sporadic.OddCore.J2Loc
public import Certificates.Kernel.GH74.J2X
public import Certificates.Data.Kernel.GH74Ev
public import Certificates.Data.GH74EvSporCheck
meta import Certificates.Data.GH74EvSporCheck
meta import Certificates.Kernel.Sporadic.OddCore.J2Loc
meta import Certificates.Kernel.GH74.J2X
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelGH74.J2Ev

open CFSG.GH74.Generic.S45.EvSpor CFSG.Sporadic.SmallOddCore.Native CFSG.PSL3Four.Native
open CFSG.Sporadic.SmallOddCore

meta def idM : Array Nat := idTab 315
meta def invM (a : Array Nat) : Array Nat := CFSG.Monster.B.Co2.Native.invCand 315 a
meta def cM (k : Nat) : Array Nat := natArr (j2CentTbl k)

meta def kbM : Array (Array Nat) := #[natArr j2KbA, natArr j2KbB]
meta def cbM : Array (Array Nat) := (j2Row2B.centGens.map natArr).toArray
meta def eM : Array (Array Nat) := (j2E16Gens.map natArr).toArray
meta def ids2M : Array (Array Nat) := Array.replicate 2 idM
meta def ids4M : Array (Array Nat) := Array.replicate 4 idM
meta def ids5M : Array (Array Nat) := Array.replicate 5 idM

meta def recOf (gs : Array (Array Nat)) : Array (Array Nat) :=
  (bfs (fun j t => conjTab 315 idM gs[j]! t) gs.size idM 3000).tabs
meta def clOf (gs : Array (Array Nat)) : Array (Array Nat) :=
  ((recOf gs).map fun x => (gs ++ gs.map invM).map fun g => comp 315 x g).flatten
meta def kbRecM : Array (Array Nat) := recOf kbM
meta def cbRecM : Array (Array Nat) := recOf cbM
meta def eRecM : Array (Array Nat) := recOf eM
meta def kbClM : Array (Array Nat) := clOf kbM
meta def cbClM : Array (Array Nat) := clOf cbM
meta def eClM : Array (Array Nat) := clOf eM

meta def cnj (g x : Array Nat) : Array Nat := comp 315 (comp 315 g x) (invM g)

meta def kbQM : Array (Array Nat) :=
  ((List.range 5).toArray.map fun j => kbM.map fun k => cnj cbM[j]! k).flatten ++
  ((List.range 5).toArray.map fun i => (List.range 5).toArray.map fun j =>
    comp 315 (comp 315 cbM[i]! cbM[j]!) (comp 315 (invM cbM[i]!) (invM cbM[j]!))).flatten ++
  ((List.range 4).toArray.map fun j => kbM.map fun k => cnj eM[j]! k).flatten

@[expose] def hWord : List Nat := [1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1]

meta def hWordM : List Nat := [1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1]

meta def hM : Array Nat :=
  hWordM.foldl (fun acc l => comp 315 acc
    ((CFSG.Sporadic.Schreier.PairNative.j2StrongArrs ())[l]!)) idM

meta def hiM : Array (Array Nat) := #[invM hM]

end CertificateChecks.KernelGH74.J2Ev

#kmulh CertificateChecks.KernelGH74.J2KB 315 9 CertificateChecks.KernelGH74.J2Ev.ids2M
  CertificateChecks.KernelGH74.J2Ev.kbM CertificateChecks.KernelGH74.J2Ev.idM 3000
#kmulh CertificateChecks.KernelGH74.J2CB 315 9 CertificateChecks.KernelGH74.J2Ev.ids5M
  CertificateChecks.KernelGH74.J2Ev.cbM CertificateChecks.KernelGH74.J2Ev.idM 3000
#kmulh CertificateChecks.KernelGH74.J2E16 315 9 CertificateChecks.KernelGH74.J2Ev.ids4M
  CertificateChecks.KernelGH74.J2Ev.eM CertificateChecks.KernelGH74.J2Ev.idM 3000
#kfind CertificateChecks.KernelGH74.J2KBCl CertificateChecks.KernelGH74.J2Ev.kbRecM
  CertificateChecks.KernelGH74.J2Ev.kbClM
#kfind CertificateChecks.KernelGH74.J2CBCl CertificateChecks.KernelGH74.J2Ev.cbRecM
  CertificateChecks.KernelGH74.J2Ev.cbClM
#kfind CertificateChecks.KernelGH74.J2E16Cl CertificateChecks.KernelGH74.J2Ev.eRecM
  CertificateChecks.KernelGH74.J2Ev.eClM
#kfind CertificateChecks.KernelGH74.J2KBP CertificateChecks.KernelGH74.J2Ev.kbRecM
  CertificateChecks.KernelGH74.J2Ev.kbQM
#kmisc_packarrs CertificateChecks.KernelGH74.J2HI CertificateChecks.KernelGH74.J2Ev.hiM 9

namespace CertificateChecks.KernelGH74.J2Ev

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH CFSG.KS.GH74
open CertificateChecks.KernelSpor CertificateChecks.KernelSpor.J2Cn

@[expose] noncomputable def cK (p : Nat) : Bool := canonK 315 9 (mask 9) (315 * 9) p

@[expose] noncomputable def iK (p q : Nat) : Bool := invEqK 315 9 (mask 9) (315 * 9) p q

@[expose] noncomputable def bIfN (c : Bool) (a b : Nat) : Nat := nIf(c, a, b)

@[expose] noncomputable def kbQ (c : Nat) : Nat :=
  bIfN (Nat.blt c 10)
    (pc (pc (J2CB.GI (Nat.div c 2)) (J2XT (Nat.mod c 2))) (J2CentI (Nat.add 18 (Nat.div c 2))))
    (bIfN (Nat.blt c 35)
      (pc (pc (J2CB.GI (Nat.div (Nat.sub c 10) 5)) (J2CB.GI (Nat.mod (Nat.sub c 10) 5)))
        (pc (J2CentI (Nat.add 18 (Nat.div (Nat.sub c 10) 5)))
          (J2CentI (Nat.add 18 (Nat.mod (Nat.sub c 10) 5)))))
      (pc (pc (J2XT (Nat.add 4 (Nat.div (Nat.sub c 35) 2))) (J2XT (Nat.mod (Nat.sub c 35) 2)))
        (J2XI (Nat.add 4 (Nat.div (Nat.sub c 35) 2)))))

@[expose] noncomputable def hK : Nat := wfoldK 315 9 (mask 9) J2P.S hWord idK

@[expose] noncomputable def bK : Nat := pc (pc (J2HI 0) (J2XT 1)) hK

theorem base_ok : bAnd(allN 2 (fun j => bAnd(Nat.beq (J2KB.GI j) (J2XT j),
      Nat.beq (J2KB.G j) idK)),
    bAnd(allN 5 (fun j => bAnd(Nat.beq (J2CB.GI j) (F (Nat.add 18 j)),
      Nat.beq (J2CB.G j) idK)),
    bAnd(allN 4 (fun j => bAnd(Nat.beq (J2E16.GI j) (J2XT (Nat.add 4 j)),
      Nat.beq (J2E16.G j) idK)),
    bAnd(Nat.beq J2KB.cnt 60, bAnd(Nat.beq J2CB.cnt 240, bAnd(Nat.beq J2E16.cnt 16,
    bAnd(penumHdK idK J2KB.cnt 3000 J2KB.T J2KB.PL,
    bAnd(penumHdK idK J2CB.cnt 3000 J2CB.T J2CB.PL,
      penumHdK idK J2E16.cnt 3000 J2E16.T J2E16.PL)))))))) = true := by
  quickRfl

theorem facts_ok : bAnd(sK (J2XT 0), bAnd(sK (J2XT 1),
    bAnd(allN 4 (fun j => sK (J2XT (Nat.add 4 j))),
    bAnd(involK (J2XT 2), bAnd(bIf(sK (J2XT 2), false, true), bAnd(sK (pc (J2XT 2) (F 0)),
      bAnd(commK (J2XT 2) (F 31),
    bAnd(involK (J2XT 3), bAnd(bIf(sK (J2XT 3), false, true), bAnd(sK (pc (J2XT 3) (F 0)),
      bAnd(commK (J2XT 3) (F 17),
    allN 43 (fun c => atK J2KB.cnt J2KB.T J2KBP c (kbQ c)))))))))))))
    = true := by
  quickRfl

theorem e16_ab : allN J2E16.cnt (fun i => bAnd(Nat.beq (pc (J2E16.T i) (J2E16.T i)) idK,
    allN J2E16.cnt (fun j => commK (J2E16.T i) (J2E16.T j)))) = true := by
  quickRfl

theorem kb_center : bAnd(allN J2KB.cnt (fun i => bIf(bAnd(commK (J2KB.T i) (J2XT 0),
      commK (J2KB.T i) (J2XT 1)), Nat.beq (J2KB.T i) idK, true)),
    bAnd(commK (F 17) (J2XT 0), commK (F 17) (J2XT 1))) = true := by
  quickRfl

theorem h_ok : bAnd(cK hK, bAnd(cK (J2HI 0), bAnd(sK hK, bAnd(iK hK (J2HI 0),
    Nat.beq (pc (pc hK (F 31)) (J2HI 0)) (J2XT 0))))) = true := by
  quickRfl

theorem c2_inner : bAnd(Nat.beq (cntBelowK J2C2.cnt (fun i => pcommK 315 9 (J2C2.T i) bK) 30) 12,
    Nat.beq (cntBelowK J2C2.cnt (fun i => bAnd(pcommK 315 9 (J2C2.T i) bK, involK (J2C2.T i))) 30)
      3) = true := by
  quickRfl

theorem c2_outer : allN J2C2.cnt (fun i => bIf(pcomm2K 315 9 (J2XT 2) (J2C2.T i) bK, false, true)) =
    true := by
  quickRfl

theorem kbE : penumSlK 315 9 (mask 9) (315 * 9) true J2KB.G J2KB.GI 2 J2KB.cnt J2KB.T J2KB.PL
    J2KB.POS J2KB.SRT J2KB.SRI 0 J2KB.cnt = true := by quickRfl
theorem kbH : slK J2KB.cnt (hsortPtK 315 9 (mask 9) J2KB.cnt J2KB.T J2KB.HS J2KB.HSI) 0 J2KB.cnt =
    true := by quickRfl
theorem kbCl : slK (Nat.mul J2KB.cnt 4)
    (findPtK J2KB.cnt J2KB.T (prodQK 315 9 (mask 9) 4 J2KB.T (bothK 2 J2KB.GI J2XI)) J2KBCl) 0
    (Nat.mul J2KB.cnt 4) = true := by quickRfl

theorem cbE : penumSlK 315 9 (mask 9) (315 * 9) true J2CB.G J2CB.GI 5 J2CB.cnt J2CB.T J2CB.PL
    J2CB.POS J2CB.SRT J2CB.SRI 0 J2CB.cnt = true := by quickRfl
theorem cbH : slK J2CB.cnt (hsortPtK 315 9 (mask 9) J2CB.cnt J2CB.T J2CB.HS J2CB.HSI) 0 J2CB.cnt =
    true := by quickRfl
theorem cbCl : slK (Nat.mul J2CB.cnt 10)
    (findPtK J2CB.cnt J2CB.T (prodQK 315 9 (mask 9) 10 J2CB.T
      (bothK 5 J2CB.GI (fun j => J2CentI (Nat.add 18 j)))) J2CBCl) 0
    (Nat.mul J2CB.cnt 10) = true := by quickRfl

theorem eE : penumSlK 315 9 (mask 9) (315 * 9) true J2E16.G J2E16.GI 4 J2E16.cnt J2E16.T J2E16.PL
    J2E16.POS J2E16.SRT J2E16.SRI 0 J2E16.cnt = true := by quickRfl
theorem eH : slK J2E16.cnt (hsortPtK 315 9 (mask 9) J2E16.cnt J2E16.T J2E16.HS J2E16.HSI) 0
    J2E16.cnt = true := by quickRfl
theorem eCl : slK (Nat.mul J2E16.cnt 8)
    (findPtK J2E16.cnt J2E16.T (prodQK 315 9 (mask 9) 8 J2E16.T
      (bothK 4 J2E16.GI (fun j => J2XI (Nat.add 4 j)))) J2E16Cl) 0
    (Nat.mul J2E16.cnt 8) = true := by quickRfl

end CertificateChecks.KernelGH74.J2Ev

end
