module

public import Certificates.Kernel.PropA.Data
public import Certificates.Kernel.PropA.FactData
public import Certificates.Kernel.PropA.FactWords
public import Certificates.Kernel.PropA.Words
public import Certificates.Data.Kernel.Spor.PRec
public import Certificates.Data.Kernel.Spor.PMem
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelPropA

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.PRec CFSG.KS.PMem

theorem pa450010_AB1 : commToK 28 5 (mask 5) pa450010CDX.cnt pa450010CDX.T pa450010PAB1a
    pa450010CDX.cnt pa450010CDX.T pa450010PAB1b (pa450010J.G 0) = true := by quickRfl
theorem pa450010_AB2 : commToK 28 5 (mask 5) pa450010CDX.cnt pa450010CDX.T pa450010PAB2a
    pa450010CDX.cnt pa450010CDX.T pa450010PAB2b (pa450010J.G 1) = true := by quickRfl
theorem pa450010_EJ : conjInK 28 5 (mask 5) pa450010J.cnt pa450010J.T pa450010PEJ pa450010CDX.G
    pa450010CDX.GI pa450010J.G 4 2 = true := by quickRfl
theorem pa450010_EE : commInK 28 5 (mask 5) pa450010J.cnt pa450010J.T pa450010PEE pa450010CDX.G
    pa450010CDX.GI 4 = true := by quickRfl
theorem pa450010_KJ1 : conjInK 28 5 (mask 5) pa450010J.cnt pa450010J.T pa450010PKJ1
    pa450010CKX1.G pa450010CKX1.GI pa450010J.G 5 2 = true := by quickRfl
theorem pa450010_KJ2 : conjInK 28 5 (mask 5) pa450010J.cnt pa450010J.T pa450010PKJ2
    pa450010CKX2.G pa450010CKX2.GI pa450010J.G 5 2 = true := by quickRfl
theorem pa450010_Jcent : centOneK 28 5 (mask 5) (pidn 28 5) pa450010J.cnt pa450010J.T 2
    pa450010J.G = true := by quickRfl
theorem pa450010_JP1 : commToK 28 5 (mask 5) pa450010J.cnt pa450010J.T pa450010PJP1a
    pa450010J.cnt pa450010J.T pa450010PJP1b (pa450010J.G 0) = true := by quickRfl
theorem pa450010_JP2 : commToK 28 5 (mask 5) pa450010J.cnt pa450010J.T pa450010PJP2a
    pa450010J.cnt pa450010J.T pa450010PJP2b (pa450010J.G 1) = true := by quickRfl
theorem pa450010_RP1 : commToK 28 5 (mask 5) pa450010R.cnt pa450010R.T pa450010PRP1a
    pa450010R.cnt pa450010R.T pa450010PRP1b (pa450010R.G 0) = true := by quickRfl
theorem pa450010_RP2 : commToK 28 5 (mask 5) pa450010R.cnt pa450010R.T pa450010PRP2a
    pa450010R.cnt pa450010R.T pa450010PRP2b (pa450010R.G 1) = true := by quickRfl

theorem pa450010_Y1_hd : recHdK 28 5 (mask 5) (28 * 5) (pidn 28 5) (pidn 28 5) 8 pa450010Y1.k
    pa450010Y1.G pa450010Y1.GI pa450010Y1.cnt pa450010Y1.T pa450010Y1.PL 4 pa450010S1 pa450010S1I
    pa450010wY = true := by quickRfl
theorem pa450010_Y1_sl : penumSlK 28 5 (mask 5) (28 * 5) false pa450010Y1.G pa450010Y1.GI
    pa450010Y1.k pa450010Y1.cnt pa450010Y1.T pa450010Y1.PL pa450010Y1.POS pa450010Y1.SRT
    pa450010Y1.SRI 0 8 = true := by quickRfl
theorem pa450010_Y1_cent : bAnd(centK 28 5 (mask 5) (28 * 5) pa450010Y1.k pa450010Y1.G
    (pa450010J.G 0), bAnd(centK 28 5 (mask 5) (28 * 5) pa450010Y1.k pa450010Y1.G (pa450010J.G 1),
    centK 28 5 (mask 5) (28 * 5) pa450010Y1.k pa450010Y1.G pa450010XD.R)) = true := by quickRfl
theorem pa450010_Y1_filt : filtInK 28 5 (mask 5) pa450010CKX1.cnt pa450010CKX1.T 2 pa450010J.G
    pa450010Y1.cnt pa450010Y1.T pa450010PY1 = true := by quickRfl

theorem pa450010_Y2_hd : recHdK 28 5 (mask 5) (28 * 5) (pidn 28 5) (pidn 28 5) 8 pa450010Y2.k
    pa450010Y2.G pa450010Y2.GI pa450010Y2.cnt pa450010Y2.T pa450010Y2.PL 4 pa450010S2 pa450010S2I
    pa450010wY = true := by quickRfl
theorem pa450010_Y2_sl : penumSlK 28 5 (mask 5) (28 * 5) false pa450010Y2.G pa450010Y2.GI
    pa450010Y2.k pa450010Y2.cnt pa450010Y2.T pa450010Y2.PL pa450010Y2.POS pa450010Y2.SRT
    pa450010Y2.SRI 0 8 = true := by quickRfl
theorem pa450010_Y2_cent : bAnd(centK 28 5 (mask 5) (28 * 5) pa450010Y2.k pa450010Y2.G
    (pa450010J.G 0), bAnd(centK 28 5 (mask 5) (28 * 5) pa450010Y2.k pa450010Y2.G (pa450010J.G 1),
    centK 28 5 (mask 5) (28 * 5) pa450010Y2.k pa450010Y2.G pa450010XD.R)) = true := by quickRfl
theorem pa450010_Y2_filt : filtInK 28 5 (mask 5) pa450010CKX2.cnt pa450010CKX2.T 2 pa450010J.G
    pa450010Y2.cnt pa450010Y2.T pa450010PY2 = true := by quickRfl

theorem pa450010_G3_1 : commToK 28 5 (mask 5) pa450010CKX1.cnt pa450010CKX1.T pa450010G3c1
    pa450010Y1.cnt pa450010Y1.T pa450010G3y1 pa450010XD.R = true := by quickRfl
theorem pa450010_G3_2 : commToK 28 5 (mask 5) pa450010CKX2.cnt pa450010CKX2.T pa450010G3c2
    pa450010Y2.cnt pa450010Y2.T pa450010G3y2 pa450010XD.R = true := by quickRfl

theorem pa450010_G1_10 : notCentK 28 5 (mask 5) (28 * 5) pa450010C10.cnt pa450010C10.T
    pa450010G1_10 pa450010XD.R 2 pa450010J.G = true := by quickRfl
theorem pa450010_G1_11 : notCentK 28 5 (mask 5) (28 * 5) pa450010C11.cnt pa450010C11.T
    pa450010G1_11 pa450010XD.R 2 pa450010J.G = true := by quickRfl
theorem pa450010_G1_12 : notCentK 28 5 (mask 5) (28 * 5) pa450010C12.cnt pa450010C12.T
    pa450010G1_12 pa450010XD.R 2 pa450010J.G = true := by quickRfl
theorem pa450010_G1_13 : notCentK 28 5 (mask 5) (28 * 5) pa450010C13.cnt pa450010C13.T
    pa450010G1_13 pa450010XD.R 2 pa450010J.G = true := by quickRfl
theorem pa450010_G1_14 : notCentK 28 5 (mask 5) (28 * 5) pa450010C14.cnt pa450010C14.T
    pa450010G1_14 pa450010XD.R 2 pa450010J.G = true := by quickRfl
theorem pa450010_G1_15 : notCentK 28 5 (mask 5) (28 * 5) pa450010C15.cnt pa450010C15.T
    pa450010G1_15 pa450010XD.R 2 pa450010J.G = true := by quickRfl
theorem pa450010_G1_20 : notCentK 28 5 (mask 5) (28 * 5) pa450010C20.cnt pa450010C20.T
    pa450010G1_20 pa450010XD.R 2 pa450010J.G = true := by quickRfl
theorem pa450010_G1_21 : notCentK 28 5 (mask 5) (28 * 5) pa450010C21.cnt pa450010C21.T
    pa450010G1_21 pa450010XD.R 2 pa450010J.G = true := by quickRfl
theorem pa450010_G1_22 : notCentK 28 5 (mask 5) (28 * 5) pa450010C22.cnt pa450010C22.T
    pa450010G1_22 pa450010XD.R 2 pa450010J.G = true := by quickRfl
theorem pa450010_G1_23 : notCentK 28 5 (mask 5) (28 * 5) pa450010C23.cnt pa450010C23.T
    pa450010G1_23 pa450010XD.R 2 pa450010J.G = true := by quickRfl

theorem pa450010_G5_k : bAnd(wordEqK 28 5 (mask 5) (pidn 28 5) pa450010S1 pa450010S1I 2
    pa450010wG5k (pa450010G5K 0), permOK 28 5 (mask 5) (28 * 5) (pa450010G5K 0) (pa450010G5K 1)) =
      true := by quickRfl
theorem pa450010_G5_z : wordEqK 28 5 (mask 5) (pidn 28 5) pa450010J.G pa450010J.GI 2 pa450010wG5z
    pa450010ZJ.R = true := by quickRfl
theorem pa450010_G5_kx : Nat.beq (pcomp 28 5 (mask 5) (pcomp 28 5 (mask 5) (pa450010G5K 0)
    pa450010XD.R) (pa450010G5K 1)) (pcomp 28 5 (mask 5) pa450010XD.R pa450010ZJ.R) = true := by
  quickRfl
theorem pa450010_G5_S : bAnd(Nat.beq (pa450010G5S 0) (pa450010J.G 0),
    bAnd(Nat.beq (pa450010G5S 1) (pa450010J.G 1),
    bAnd(Nat.beq (pa450010G5S 2) (pcomp 28 5 (mask 5) (pcomp 28 5 (mask 5) (pa450010G5K 0)
      (pa450010J.G 0)) (pa450010G5K 1)),
    bAnd(Nat.beq (pa450010G5S 3) (pcomp 28 5 (mask 5) (pcomp 28 5 (mask 5) (pa450010G5K 0)
      (pa450010J.G 1)) (pa450010G5K 1)),
    allN 4 (fun j => permOK 28 5 (mask 5) (28 * 5) (pa450010G5S j) (pa450010G5SI j)))))) = true := by
  quickRfl
theorem pa450010_G5_ab : bAnd(wordEqK 28 5 (mask 5) (pidn 28 5) pa450010G5S pa450010G5SI 4
    pa450010wG5a (pa450010S1 0), wordEqK 28 5 (mask 5) (pidn 28 5) pa450010G5S pa450010G5SI 4
    pa450010wG5b (pa450010S1 1)) = true := by quickRfl
theorem pa450010_ZJ_hd : recHdK 28 5 (mask 5) (28 * 5) (pidn 28 5) pa450010ZJ.R 15 pa450010ZJ.k
    pa450010ZJ.G pa450010ZJ.GI pa450010ZJ.cnt pa450010ZJ.T pa450010ZJ.PL 2 pa450010S1 pa450010S1I
    pa450010wJ = true := by quickRfl
theorem pa450010_ZJ_sl : penumSlK 28 5 (mask 5) (28 * 5) true pa450010ZJ.G pa450010ZJ.GI
    pa450010ZJ.k pa450010ZJ.cnt pa450010ZJ.T pa450010ZJ.PL pa450010ZJ.POS pa450010ZJ.SRT
    pa450010ZJ.SRI 0 15 = true := by quickRfl
theorem pa450010_ZJ_cover : sqCoverK 28 5 (mask 5) (pidn 28 5) (pidn 28 5) pa450010J.T
    [(pa450010ZJ.cnt, pa450010ZJ.T, pa450010PZJ)] pa450010J.cnt = true := by quickRfl

end CertificateChecks.KernelPropA

end
