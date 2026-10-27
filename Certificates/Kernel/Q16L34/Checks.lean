module

public import Certificates.Data.Kernel.Q16Q16K
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoL3FourHypIIPk
import Certificates.Data.Kernel.Census.Packed
import CFSG.Certificates.Kernel.Enum.Defs
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelQ16L34

open CFSG.KC.Q16Q16K CFSG.ComponentClassification.RankTwoL3Four.HypII

set_option maxRecDepth 400000

@[expose] noncomputable def q16L34R : List Rec := l34CS.pts.toList.map (mkRec 42 6)

theorem q16L34F0 : allL (chkX 42 6 q16L34R) ((q16L34R.drop 0).take 32) = true := by quickRfl
theorem q16L34F1 : allL (chkX 42 6 q16L34R) ((q16L34R.drop 32).take 32) = true := by quickRfl
theorem q16L34F2 : allL (chkX 42 6 q16L34R) ((q16L34R.drop 64).take 32) = true := by quickRfl
theorem q16L34F3 : allL (chkX 42 6 q16L34R) ((q16L34R.drop 96).take 32) = true := by quickRfl
theorem q16L34F4 : allL (chkX 42 6 q16L34R) ((q16L34R.drop 128).take 32) = true := by quickRfl
theorem q16L34F5 : allL (chkX 42 6 q16L34R) ((q16L34R.drop 160).take 32) = true := by quickRfl
theorem q16L34F6 : allL (chkX 42 6 q16L34R) ((q16L34R.drop 192).take 32) = true := by quickRfl
theorem q16L34F7 : allL (chkX 42 6 q16L34R) (q16L34R.drop 224) = true := by quickRfl

end CertificateChecks.KernelQ16L34
