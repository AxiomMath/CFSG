module

public import Certificates.Kernel.MaxD2.McLP.Enum
public import Certificates.Kernel.MaxD2.McLP.Data
public import Certificates.Kernel.MaxD2.McLP.Lem45Data
public import Certificates.Data.Kernel.MaxD2.Lem45
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.McLLem45Data
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Data.McLFiveLocalP

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelMaxD2.McLP

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.MaxD2 CFSG.KS.PEnum CFSG.KS.Row
open CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

theorem l45_w : wordEqK 275 9 (mask 9) (pidn 275 9) GP GPI 2 McLLem45.wordW (WL 0) = true := by
  quickRfl
theorem l45_wcn : canonK 275 9 (mask 9) (275 * 9) (WL 0) = true := by quickRfl
theorem l45_u5 : Nat.beq (pw 275 9 (RE.G 0) 5) (pidn 275 9) = true := by quickRfl
theorem l45_ww : Nat.beq (pcomp 275 9 (mask 9) (WL 0) (WL 0)) (pidn 275 9) = true := by quickRfl
theorem l45_wc : allN 5 (fun k => allN 5 (fun l => Nat.beq
    (pcomp 275 9 (mask 9) (wcK 275 9 (RE.G 0) (WL 0) k) (wcK 275 9 (RE.G 0) (WL 0) l))
    (pcomp 275 9 (mask 9) (wcK 275 9 (RE.G 0) (WL 0) l) (wcK 275 9 (RE.G 0) (WL 0) k)))) = true := by
  quickRfl
theorem l45_ne : bIf(Nat.beq (wcK 275 9 (RE.G 0) (WL 0) 1) (wcK 275 9 (RE.G 0) (WL 0) 0), false,
    true) = true := by quickRfl
theorem l45_i0 : Nat.blt (r32 IX 0) RE.cnt = true := by quickRfl
theorem l45_i0' : Nat.beq (RE.T (r32 IX 0)) (RE.G 0) = true := by quickRfl
theorem l45_tree : treeK 275 9 RE.cnt NE.k NE.G NGI RE.T (r32 IX) McLLem45.tree 0 = true := by
  quickRfl
theorem l45_cov : allN RE.cnt (covK 5 120 (r32 ZP) (r32 ZX) (r32 IX) (r32 CV)) = true := by quickRfl

end CertificateChecks.KernelMaxD2.McLP
