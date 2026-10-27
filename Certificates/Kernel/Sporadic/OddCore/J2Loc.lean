
module

public import Certificates.Kernel.Sporadic.OddCore.J2Cent
public import Certificates.Kernel.Sporadic.OddCore.MulHCmd
public import Certificates.Data.Kernel.Spor.MulHQ
public import CFSG.Sporadic.SmallOddCore.J2LocalCheckInputs
meta import CFSG.Sporadic.SmallOddCore.J2LocalCheckInputs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.J2Loc

open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native CFSG.PSL3Four.Native
open CFSG.Sporadic.Th.Native

meta def idM : Array Nat := idTab 315

meta def idsM (k : Nat) : Array (Array Nat) := Array.replicate k idM

meta def arrs (L : List CFSG.Sporadic.Th.Native.Table) : Array (Array Nat) := (L.map natArr).toArray

meta def c1M : Array (Array Nat) := arrs j2C1Gens
meta def c2M : Array (Array Nat) := arrs j2C2Gens
meta def dM : Array (Array Nat) := arrs j2DGens
meta def qM : Array (Array Nat) := arrs j2QGens
meta def c1iM : Array (Array Nat) := c1M.map (CFSG.Monster.B.Co2.Native.invCand 315)
meta def c2iM : Array (Array Nat) := c2M.map (CFSG.Monster.B.Co2.Native.invCand 315)
meta def diM : Array (Array Nat) := dM.map (CFSG.Monster.B.Co2.Native.invCand 315)
meta def qiM : Array (Array Nat) := qM.map (CFSG.Monster.B.Co2.Native.invCand 315)
meta def repM (r : Nat) : Array Nat := natArr (j2DReps.getD r (idT 315))
meta def rep0M : Array Nat := repM 0
meta def rep1M : Array Nat := repM 1
meta def rep2M : Array Nat := repM 2
meta def rep3M : Array Nat := repM 3
meta def ids2M : Array (Array Nat) := idsM 2
meta def ids4M : Array (Array Nat) := idsM 4
meta def ids5M : Array (Array Nat) := idsM 5

meta def mulRec (gs : Array (Array Nat)) (cap : Nat) : Array (Array Nat) :=
  (bfs (fun j t => conjTab 315 idM gs[j]! t) gs.size idM cap).tabs

meta def classRec (x : Array Nat) : Array (Array Nat) :=
  (bfs (fun j t => conjTab 315 dM[j]! diM[j]! t) 2 x 100).tabs

meta def o0M : Array (Array Nat) := classRec rep0M
meta def o1M : Array (Array Nat) := classRec rep1M
meta def o2M : Array (Array Nat) := classRec rep2M
meta def o3M : Array (Array Nat) := classRec rep3M
meta def io0M : Array (Array Nat) := idsM o0M.size
meta def io1M : Array (Array Nat) := idsM o1M.size
meta def io2M : Array (Array Nat) := idsM o2M.size
meta def io3M : Array (Array Nat) := idsM o3M.size

meta def dRecM : Array (Array Nat) := mulRec dM 100
meta def c1RecM : Array (Array Nat) := mulRec c1M 300
meta def qRecM : Array (Array Nat) := mulRec qM 100
meta def c2RecM : Array (Array Nat) := mulRec c2M 3000

meta def prodsM (R gs gis : Array (Array Nat)) : Array (Array Nat) :=
  (R.map fun x => (gs ++ gis).map fun g => comp 315 x g).flatten

meta def conjsM (R cs cis : Array (Array Nat)) : Array (Array Nat) :=
  (R.map fun x => (List.range cs.size).toArray.map fun j => conjTab 315 cs[j]! cis[j]! x).flatten

meta def dClM : Array (Array Nat) := prodsM dRecM dM diM
meta def c1ClM : Array (Array Nat) := prodsM c1RecM c1M c1iM
meta def qClM : Array (Array Nat) := prodsM qRecM qM qiM
meta def c2ClM : Array (Array Nat) := prodsM c2RecM c2M c2iM
meta def dNormM : Array (Array Nat) := conjsM dRecM c1M c1iM
meta def qNormM : Array (Array Nat) := conjsM qRecM c2M c2iM

#kmulh CertificateChecks.KernelSpor.J2D 315 9 ids2M dM idM 100
#kmulh CertificateChecks.KernelSpor.J2C1 315 9 ids5M c1M idM 300
#kmulh CertificateChecks.KernelSpor.J2Q 315 9 ids5M qM idM 100
#kmulh CertificateChecks.KernelSpor.J2C2 315 9 ids4M c2M idM 3000
#kmulh CertificateChecks.KernelSpor.J2O0 315 9 dM diM rep0M 100
#kmulh CertificateChecks.KernelSpor.J2O1 315 9 dM diM rep1M 100
#kmulh CertificateChecks.KernelSpor.J2O2 315 9 dM diM rep2M 100
#kmulh CertificateChecks.KernelSpor.J2O3 315 9 dM diM rep3M 100
#kmulh CertificateChecks.KernelSpor.J2N0 315 9 io0M o0M idM 100
#kmulh CertificateChecks.KernelSpor.J2N1 315 9 io1M o1M idM 100
#kmulh CertificateChecks.KernelSpor.J2N2 315 9 io2M o2M idM 100
#kmulh CertificateChecks.KernelSpor.J2N3 315 9 io3M o3M idM 100

#kmisc_packarrs CertificateChecks.KernelSpor.J2DI diM 9
#kmisc_packarrs CertificateChecks.KernelSpor.J2QI qiM 9
#kmisc_packarrs CertificateChecks.KernelSpor.J2C1I c1iM 9
#kmisc_packarrs CertificateChecks.KernelSpor.J2C2I c2iM 9

#kfind CertificateChecks.KernelSpor.J2DCl dRecM dClM
#kfind CertificateChecks.KernelSpor.J2C1Cl c1RecM c1ClM
#kfind CertificateChecks.KernelSpor.J2QCl qRecM qClM
#kfind CertificateChecks.KernelSpor.J2C2Cl c2RecM c2ClM
#kfind CertificateChecks.KernelSpor.J2DNm dRecM dNormM
#kfind CertificateChecks.KernelSpor.J2QNm qRecM qNormM
#kfind CertificateChecks.KernelSpor.J2DIn0 o0M dRecM
#kfind CertificateChecks.KernelSpor.J2DIn1 o1M dRecM
#kfind CertificateChecks.KernelSpor.J2DIn2 o2M dRecM
#kfind CertificateChecks.KernelSpor.J2DIn3 o3M dRecM

end CertificateChecks.KernelSpor.J2Loc

namespace CertificateChecks.KernelSpor.J2Loc

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH

@[expose] noncomputable def pc (p q : Nat) : Nat := pcomp 315 9 (mask 9) p q

@[expose] noncomputable def idK : Nat := pidn 315 9

@[expose] noncomputable def c1L (l : Nat) : Nat := J2CentT.F (Nat.add (nat_lit 17) l)

@[expose] noncomputable def c2L (l : Nat) : Nat := J2CentT.F (Nat.add (nat_lit 31) l)

@[expose] noncomputable def dL (l : Nat) : Nat := J2D.GI (Nat.sub l (nat_lit 1))

theorem gens_ok : bAnd(allN 5 (fun j => canonK 315 9 (mask 9) (315 * 9) (c1L (Nat.succ j))),
    bAnd(allN 4 (fun j => canonK 315 9 (mask 9) (315 * 9) (c2L (Nat.succ j))),
    bAnd(allN 5 (fun j => Nat.beq (J2C1.GI j) (c1L (Nat.succ j))),
    bAnd(allN 4 (fun j => Nat.beq (J2C2.GI j) (c2L (Nat.succ j))),
    bAnd(allN 5 (fun j => invEqK 315 9 (mask 9) (315 * 9) (J2C1.GI j) (J2C1I j)),
    bAnd(allN 4 (fun j => invEqK 315 9 (mask 9) (315 * 9) (J2C2.GI j) (J2C2I j)),
    bAnd(Nat.beq (J2D.GI 0) (wfoldK 315 9 (mask 9) c1L [3, 2] idK),
    bAnd(Nat.beq (J2D.GI 1) (wfoldK 315 9 (mask 9) c1L [2, 4, 2, 4] idK),
    bAnd(allN 2 (fun j => invEqK 315 9 (mask 9) (315 * 9) (J2D.GI j) (J2DI j)),
    bAnd(Nat.beq (J2Q.GI 0) (wfoldK 315 9 (mask 9) c2L [3, 3, 3, 2, 1, 2, 1] idK),
    bAnd(Nat.beq (J2Q.GI 1) (wfoldK 315 9 (mask 9) c2L [3, 3, 2, 3, 2, 1] idK),
    bAnd(Nat.beq (J2Q.GI 2) (wfoldK 315 9 (mask 9) c2L [2, 3, 1, 3, 3, 1] idK),
    bAnd(Nat.beq (J2Q.GI 3) (wfoldK 315 9 (mask 9) c2L [3, 3, 3] idK),
    bAnd(Nat.beq (J2Q.GI 4) (wfoldK 315 9 (mask 9) c2L [4, 4, 4] idK),
    allN 5 (fun j => invEqK 315 9 (mask 9) (315 * 9) (J2Q.GI j) (J2QI j)))))))))))))))) =
    true := by
  quickRfl

theorem ids_ok : bAnd(allN 2 (fun j => Nat.beq (J2D.G j) idK),
    bAnd(allN 5 (fun j => Nat.beq (J2C1.G j) idK), bAnd(allN 5 (fun j => Nat.beq (J2Q.G j) idK),
    bAnd(allN 4 (fun j => Nat.beq (J2C2.G j) idK),
    bAnd(allN J2O0.cnt (fun j => Nat.beq (J2N0.G j) idK),
    bAnd(allN J2O1.cnt (fun j => Nat.beq (J2N1.G j) idK),
    bAnd(allN J2O2.cnt (fun j => Nat.beq (J2N2.G j) idK),
    allN J2O3.cnt (fun j => Nat.beq (J2N3.G j) idK)))))))) = true := by
  quickRfl

theorem reps_ok : bAnd(Nat.beq J2O0.R (wfoldK 315 9 (mask 9) dL [1] idK),
    bAnd(Nat.beq J2O1.R (wfoldK 315 9 (mask 9) dL [2] idK),
    bAnd(Nat.beq J2O2.R (wfoldK 315 9 (mask 9) dL [1, 2] idK),
    bAnd(Nat.beq J2O3.R (wfoldK 315 9 (mask 9) dL [1, 2, 2] idK),
    bAnd(allN 2 (fun j => bAnd(Nat.beq (J2O0.G j) (J2D.GI j), Nat.beq (J2O0.GI j) (J2DI j))),
    bAnd(allN 2 (fun j => bAnd(Nat.beq (J2O1.G j) (J2D.GI j), Nat.beq (J2O1.GI j) (J2DI j))),
    bAnd(allN 2 (fun j => bAnd(Nat.beq (J2O2.G j) (J2D.GI j), Nat.beq (J2O2.GI j) (J2DI j))),
    bAnd(allN 2 (fun j => bAnd(Nat.beq (J2O3.G j) (J2D.GI j), Nat.beq (J2O3.GI j) (J2DI j))),
    bAnd(allN J2O0.cnt (fun j => Nat.beq (J2N0.GI j) (J2O0.T j)),
    bAnd(allN J2O1.cnt (fun j => Nat.beq (J2N1.GI j) (J2O1.T j)),
    bAnd(allN J2O2.cnt (fun j => Nat.beq (J2N2.GI j) (J2O2.T j)),
    allN J2O3.cnt (fun j => Nat.beq (J2N3.GI j) (J2O3.T j))))))))))))) = true := by
  quickRfl

theorem dE : penumSlK 315 9 (mask 9) (315 * 9) true J2D.G J2D.GI 2 J2D.cnt J2D.T J2D.PL J2D.POS
    J2D.SRT J2D.SRI 0 J2D.cnt = true := by quickRfl
theorem c1E : penumSlK 315 9 (mask 9) (315 * 9) true J2C1.G J2C1.GI 5 J2C1.cnt J2C1.T J2C1.PL
    J2C1.POS J2C1.SRT J2C1.SRI 0 J2C1.cnt = true := by quickRfl
theorem qE : penumSlK 315 9 (mask 9) (315 * 9) true J2Q.G J2Q.GI 5 J2Q.cnt J2Q.T J2Q.PL J2Q.POS
    J2Q.SRT J2Q.SRI 0 J2Q.cnt = true := by quickRfl
theorem o0E : penumSlK 315 9 (mask 9) (315 * 9) true J2O0.G J2O0.GI 2 J2O0.cnt J2O0.T J2O0.PL
    J2O0.POS J2O0.SRT J2O0.SRI 0 J2O0.cnt = true := by quickRfl
theorem o1E : penumSlK 315 9 (mask 9) (315 * 9) true J2O1.G J2O1.GI 2 J2O1.cnt J2O1.T J2O1.PL
    J2O1.POS J2O1.SRT J2O1.SRI 0 J2O1.cnt = true := by quickRfl
theorem o2E : penumSlK 315 9 (mask 9) (315 * 9) true J2O2.G J2O2.GI 2 J2O2.cnt J2O2.T J2O2.PL
    J2O2.POS J2O2.SRT J2O2.SRI 0 J2O2.cnt = true := by quickRfl
theorem o3E : penumSlK 315 9 (mask 9) (315 * 9) true J2O3.G J2O3.GI 2 J2O3.cnt J2O3.T J2O3.PL
    J2O3.POS J2O3.SRT J2O3.SRI 0 J2O3.cnt = true := by quickRfl
theorem n0E : penumSlK 315 9 (mask 9) (315 * 9) true J2N0.G J2N0.GI J2O0.cnt J2N0.cnt J2N0.T
    J2N0.PL J2N0.POS J2N0.SRT J2N0.SRI 0 J2N0.cnt = true := by quickRfl
theorem n1E : penumSlK 315 9 (mask 9) (315 * 9) true J2N1.G J2N1.GI J2O1.cnt J2N1.cnt J2N1.T
    J2N1.PL J2N1.POS J2N1.SRT J2N1.SRI 0 J2N1.cnt = true := by quickRfl
theorem n2E : penumSlK 315 9 (mask 9) (315 * 9) true J2N2.G J2N2.GI J2O2.cnt J2N2.cnt J2N2.T
    J2N2.PL J2N2.POS J2N2.SRT J2N2.SRI 0 J2N2.cnt = true := by quickRfl
theorem n3E : penumSlK 315 9 (mask 9) (315 * 9) true J2N3.G J2N3.GI J2O3.cnt J2N3.cnt J2N3.T
    J2N3.PL J2N3.POS J2N3.SRT J2N3.SRI 0 J2N3.cnt = true := by quickRfl

theorem heads : bAnd(penumHdK idK J2D.cnt 100 J2D.T J2D.PL,
    bAnd(penumHdK idK J2C1.cnt 300 J2C1.T J2C1.PL, bAnd(penumHdK idK J2Q.cnt 100 J2Q.T J2Q.PL,
    bAnd(penumHdK idK J2C2.cnt 3000 J2C2.T J2C2.PL,
    bAnd(penumHdK J2O0.R J2O0.cnt 100 J2O0.T J2O0.PL,
    bAnd(penumHdK J2O1.R J2O1.cnt 100 J2O1.T J2O1.PL,
    bAnd(penumHdK J2O2.R J2O2.cnt 100 J2O2.T J2O2.PL,
    bAnd(penumHdK J2O3.R J2O3.cnt 100 J2O3.T J2O3.PL,
    bAnd(penumHdK idK J2N0.cnt 100 J2N0.T J2N0.PL,
    bAnd(penumHdK idK J2N1.cnt 100 J2N1.T J2N1.PL,
    bAnd(penumHdK idK J2N2.cnt 100 J2N2.T J2N2.PL,
    penumHdK idK J2N3.cnt 100 J2N3.T J2N3.PL))))))))))) = true := by
  quickRfl

theorem dH : slK J2D.cnt (hsortPtK 315 9 (mask 9) J2D.cnt J2D.T J2D.HS J2D.HSI) 0 J2D.cnt =
    true := by quickRfl
theorem c1H : slK J2C1.cnt (hsortPtK 315 9 (mask 9) J2C1.cnt J2C1.T J2C1.HS J2C1.HSI) 0
    J2C1.cnt = true := by quickRfl
theorem qH : slK J2Q.cnt (hsortPtK 315 9 (mask 9) J2Q.cnt J2Q.T J2Q.HS J2Q.HSI) 0 J2Q.cnt =
    true := by quickRfl
theorem o0H : slK J2O0.cnt (hsortPtK 315 9 (mask 9) J2O0.cnt J2O0.T J2O0.HS J2O0.HSI) 0
    J2O0.cnt = true := by quickRfl
theorem o1H : slK J2O1.cnt (hsortPtK 315 9 (mask 9) J2O1.cnt J2O1.T J2O1.HS J2O1.HSI) 0
    J2O1.cnt = true := by quickRfl
theorem o2H : slK J2O2.cnt (hsortPtK 315 9 (mask 9) J2O2.cnt J2O2.T J2O2.HS J2O2.HSI) 0
    J2O2.cnt = true := by quickRfl
theorem o3H : slK J2O3.cnt (hsortPtK 315 9 (mask 9) J2O3.cnt J2O3.T J2O3.HS J2O3.HSI) 0
    J2O3.cnt = true := by quickRfl
theorem n0H : slK J2N0.cnt (hsortPtK 315 9 (mask 9) J2N0.cnt J2N0.T J2N0.HS J2N0.HSI) 0
    J2N0.cnt = true := by quickRfl
theorem n1H : slK J2N1.cnt (hsortPtK 315 9 (mask 9) J2N1.cnt J2N1.T J2N1.HS J2N1.HSI) 0
    J2N1.cnt = true := by quickRfl
theorem n2H : slK J2N2.cnt (hsortPtK 315 9 (mask 9) J2N2.cnt J2N2.T J2N2.HS J2N2.HSI) 0
    J2N2.cnt = true := by quickRfl
theorem n3H : slK J2N3.cnt (hsortPtK 315 9 (mask 9) J2N3.cnt J2N3.T J2N3.HS J2N3.HSI) 0
    J2N3.cnt = true := by quickRfl

theorem dCl : slK (Nat.mul J2D.cnt 4)
    (findPtK J2D.cnt J2D.T (prodQK 315 9 (mask 9) 4 J2D.T (bothK 2 J2D.GI J2DI)) J2DCl) 0
    (Nat.mul J2D.cnt 4) = true := by quickRfl
theorem c1Cl : slK (Nat.mul J2C1.cnt 10)
    (findPtK J2C1.cnt J2C1.T (prodQK 315 9 (mask 9) 10 J2C1.T (bothK 5 J2C1.GI J2C1I))
      J2C1Cl) 0
    (Nat.mul J2C1.cnt 10) = true := by quickRfl
theorem qCl : slK (Nat.mul J2Q.cnt 10)
    (findPtK J2Q.cnt J2Q.T (prodQK 315 9 (mask 9) 10 J2Q.T (bothK 5 J2Q.GI J2QI)) J2QCl) 0
    (Nat.mul J2Q.cnt 10) = true := by quickRfl
theorem dNm : slK (Nat.mul J2D.cnt 5)
    (findPtK J2D.cnt J2D.T (conjQK 315 9 (mask 9) 5 J2D.T J2C1.GI J2C1I) J2DNm) 0
    (Nat.mul J2D.cnt 5) = true := by
  quickRfl
theorem qNm : slK (Nat.mul J2Q.cnt 4)
    (findPtK J2Q.cnt J2Q.T (conjQK 315 9 (mask 9) 4 J2Q.T J2C2.GI J2C2I) J2QNm) 0
    (Nat.mul J2Q.cnt 4) = true := by
  quickRfl

@[expose] noncomputable def inClass (i : Nat) : Bool :=
  strictB (J2D.T i) (fun x => bIf(Nat.beq x idK, true,
    bIf(bAnd(Nat.blt (r32 J2DIn0 i) J2O0.cnt, Nat.beq (J2O0.T (r32 J2DIn0 i)) x), true,
    bIf(bAnd(Nat.blt (r32 J2DIn1 i) J2O1.cnt, Nat.beq (J2O1.T (r32 J2DIn1 i)) x), true,
    bIf(bAnd(Nat.blt (r32 J2DIn2 i) J2O2.cnt, Nat.beq (J2O2.T (r32 J2DIn2 i)) x), true,
    bAnd(Nat.blt (r32 J2DIn3 i) J2O3.cnt, Nat.beq (J2O3.T (r32 J2DIn3 i)) x))))))

theorem dIn : allN J2D.cnt inClass = true := by quickRfl

theorem sizes : bAnd(Nat.beq J2D.cnt 60, bAnd(Nat.beq J2C1.cnt 240, bAnd(Nat.beq J2Q.cnt 32,
    bAnd(Nat.beq J2C2.cnt 1920, bAnd(Nat.beq J2N0.cnt 60, bAnd(Nat.beq J2N1.cnt 60,
    bAnd(Nat.beq J2N2.cnt 60, Nat.beq J2N3.cnt 60))))))) = true := by quickRfl

theorem cent1 : Nat.beq (cntBelowK J2C1.cnt (fun i => strictB (J2C1.T i) (fun y =>
    bAnd(Nat.beq (pc y (J2D.GI 0)) (pc (J2D.GI 0) y), Nat.beq (pc y (J2D.GI 1)) (pc (J2D.GI 1) y))))
    4) 4 = true := by
  quickRfl

theorem dNotComm : bIf(Nat.beq (pc (J2D.GI 0) (J2D.GI 1)) (pc (J2D.GI 1) (J2D.GI 0)), false, true) =
    true := by
  quickRfl

end CertificateChecks.KernelSpor.J2Loc

end
