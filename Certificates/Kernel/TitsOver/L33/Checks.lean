module

public import Certificates.Kernel.TitsOver.Three.Data
public import Certificates.Kernel.TitsOver.Three.SEnum0
public import Certificates.Kernel.TitsOver.Three.SEnum1
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourTwoTitsData
public import Certificates.Data.Kernel.Spor.Prim
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelTitsOver.L33

open CFSG.KC CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim
open CertificateChecks.KernelTitsOver.Three CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen.TitsL33
open CFSG.HardMathSupport.Dickson.BMRows.M13L33 (l33Rels)

theorem relK0 : (l33Rels.all fun r => wordEqK 1755 11 (mask 11) (pidn 1755 11) S0E.G SGI0 6
    (relWord (l33AWords.getD 0 []) (l33BWords.getD 0 []) r) (pidn 1755 11)) = true := by
  quickRfl

theorem relK1 : (l33Rels.all fun r => wordEqK 1755 11 (mask 11) (pidn 1755 11) S1E.G SGI1 6
    (relWord (l33AWords.getD 1 []) (l33BWords.getD 1 []) r) (pidn 1755 11)) = true := by
  quickRfl

theorem aK0 : bAnd(wordEqK 1755 11 (mask 11) (pidn 1755 11) S0E.G SGI0 6 (l33AWords.getD 0 [])
    (wordK 1755 11 (mask 11) (pidn 1755 11) S0E.G SGI0 (l33AWords.getD 0 [])),
    bAnd(canonK 1755 11 (mask 11) (1755 * 11)
      (wordK 1755 11 (mask 11) (pidn 1755 11) S0E.G SGI0 (l33AWords.getD 0 [])),
    Bool.not (Nat.beq (wordK 1755 11 (mask 11) (pidn 1755 11) S0E.G SGI0 (l33AWords.getD 0 []))
      (pidn 1755 11)))) = true := by
  quickRfl

theorem aK1 : bAnd(wordEqK 1755 11 (mask 11) (pidn 1755 11) S1E.G SGI1 6 (l33AWords.getD 1 [])
    (wordK 1755 11 (mask 11) (pidn 1755 11) S1E.G SGI1 (l33AWords.getD 1 [])),
    bAnd(canonK 1755 11 (mask 11) (1755 * 11)
      (wordK 1755 11 (mask 11) (pidn 1755 11) S1E.G SGI1 (l33AWords.getD 1 [])),
    Bool.not (Nat.beq (wordK 1755 11 (mask 11) (pidn 1755 11) S1E.G SGI1 (l33AWords.getD 1 []))
      (pidn 1755 11)))) = true := by
  quickRfl

end CertificateChecks.KernelTitsOver.L33

end
