module

public import Certificates.Kernel.LocalComp.L34Fix.Data
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.L34Fix

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KC.BfsPin CFSG.KC.L34K
open CFSG.AGLEmbedding.KFactProofs.CoverThree.SL3FourGen
open CFSG.KLie.CT (andB orB notB)

theorem kH_gens : gensK hGens 42 6 2 L34FH.G = true := by quickRfl
theorem kH_hd : penumHdK (pidn 42 6) 27 27 L34FH.T L34FH.PL = true := by quickRfl
theorem kH_sl : penumSlK 42 6 (mask 6) (42 * 6) false L34FH.G L34FH.GI 2 27 L34FH.T L34FH.PL
    L34FH.POS L34FH.SRT L34FH.SRI 0 27 = true := by
  quickRfl

theorem kM0_gens : gensK mGens[0]! 42 6 2 L34FM0.G = true := by quickRfl
theorem kM0_hd : penumHdK (pidn 42 6) 9 9 L34FM0.T L34FM0.PL = true := by quickRfl
theorem kM0_sl : penumSlK 42 6 (mask 6) (42 * 6) false L34FM0.G L34FM0.GI 2 9 L34FM0.T L34FM0.PL
    L34FM0.POS L34FM0.SRT L34FM0.SRI 0 9 = true := by
  quickRfl

theorem kM1_gens : gensK mGens[1]! 42 6 2 L34FM1.G = true := by quickRfl
theorem kM1_hd : penumHdK (pidn 42 6) 9 9 L34FM1.T L34FM1.PL = true := by quickRfl
theorem kM1_sl : penumSlK 42 6 (mask 6) (42 * 6) false L34FM1.G L34FM1.GI 2 9 L34FM1.T L34FM1.PL
    L34FM1.POS L34FM1.SRT L34FM1.SRI 0 9 = true := by
  quickRfl

theorem kM2_gens : gensK mGens[2]! 42 6 2 L34FM2.G = true := by quickRfl
theorem kM2_hd : penumHdK (pidn 42 6) 9 9 L34FM2.T L34FM2.PL = true := by quickRfl
theorem kM2_sl : penumSlK 42 6 (mask 6) (42 * 6) false L34FM2.G L34FM2.GI 2 9 L34FM2.T L34FM2.PL
    L34FM2.POS L34FM2.SRT L34FM2.SRI 0 9 = true := by
  quickRfl

theorem kM3_gens : gensK mGens[3]! 42 6 2 L34FM3.G = true := by quickRfl
theorem kM3_hd : penumHdK (pidn 42 6) 9 9 L34FM3.T L34FM3.PL = true := by quickRfl
theorem kM3_sl : penumSlK 42 6 (mask 6) (42 * 6) false L34FM3.G L34FM3.GI 2 9 L34FM3.T L34FM3.PL
    L34FM3.POS L34FM3.SRT L34FM3.SRI 0 9 = true := by
  quickRfl

theorem kR : andB (allN 10 fun n => Nat.blt (L34FW.RI.getD n 0) 241920)
    (andB (allN 2 fun j => Nat.beq (L34R.T (L34FW.RI.getD j 0)) (L34FH.G j))
      (allN 4 fun k => allN 2 fun j =>
        Nat.beq (L34R.T (L34FW.RI.getD (Nat.add (Nat.add (Nat.mul 2 k) j) 2) 0)) (L34FM.G k j))) =
    true := by
  quickRfl

theorem kS : allN 2 (fun j => andB (Nat.blt (L34FW.SI.getD j 0) 20160)
    (Nat.beq (L34S.T (L34FW.SI.getD j 0)) (L34FM.G 0 j))) = true := by
  quickRfl

@[expose] noncomputable def memM (k x : Nat) : Bool :=
  notB (allN 9 fun q => notB (Nat.beq (L34FM.T k q) x))

theorem kPair : allN 27 (fun i => allN 27 fun j =>
    orB (notB (commPt 42 6 (L34FH.T i) (L34FH.T j)))
      (notB (allN 4 fun k => notB (andB (memM k (L34FH.T i)) (memM k (L34FH.T j)))))) = true := by
  quickRfl

theorem kFix : allN 3 (fun k => andB
    (allN 2 fun j => andB (Nat.blt (L34FW.FI.getD (Nat.add (Nat.mul 2 k) j) 0) 20160)
      (andB (Nat.blt (L34FW.FQ.getD (Nat.add (Nat.mul 2 k) j) 0) 9) (andB (notB (Nat.beq (L34FM.T (Nat.succ k)
          (L34FW.FQ.getD (Nat.add (Nat.mul 2 k) j) 0)) (pidn 42 6)))
        (commPt 42 6 (L34FW.A (Nat.succ k) j)
          (L34FM.T (Nat.succ k) (L34FW.FQ.getD (Nat.add (Nat.mul 2 k) j) 0))))))
    (allN 3 fun i => Nat.beq (CFSG.KC.L34Two.dwordK 42 6 (L34FW.A (Nat.succ k)) 2 64
      (L34FW.WL.getD (Nat.add (Nat.mul 3 k) i) 0)) (L34R.G i))) = true := by
  quickRfl

end CertificateChecks.KernelLC.L34Fix

end
