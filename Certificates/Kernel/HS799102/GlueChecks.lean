module

public import Certificates.Kernel.HS799102.GlueData
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelHS799102

open CFSG.KC.PCent CFSG.KC.Enum

theorem ch799102_mem1 : (allN 2 (fun k => memK (mG1 k) (TH.F 2)) &&
    allN 4 (fun j => memK (TV1.F (Nat.add 17 j)) (TH.F 2))) = true := by quickRfl

theorem ch799102_mem2 : (allN 3 (fun k => memK (mG2 k) (TH.F 3)) &&
    allN 4 (fun j => memK (TV2.F (Nat.add 19 j)) (TH.F 3))) = true := by quickRfl

theorem ch799102_mem3 : (allN 4 (fun k => memK (mG3 k) (TH.F 4)) &&
    allN 4 (fun j => memK (TV3.F (Nat.add 17 j)) (TH.F 4))) = true := by quickRfl

theorem ch799102_n1 : (stabLowK 100 7 mG1 2 N1 && baseInK N1 (maskK O1)) = true := by quickRfl

theorem ch799102_n2 : (stabLowK 100 7 mG2 3 N2 && baseInK N2 (maskK O2)) = true := by quickRfl

theorem ch799102_n3 : (stabLowK 100 7 mG3 4 N3 && baseInK N3 (maskK O3)) = true := by quickRfl

theorem ch799102_nprods :
    (Nat.beq ((N1.map fun lv => lv.2.2.2.length).prod) 40320 &&
      Nat.beq ((N2.map fun lv => lv.2.2.2.length).prod) 40320 &&
      Nat.beq ((N3.map fun lv => lv.2.2.2.length).prod) 2880) = true := by quickRfl

theorem ch799102_w1 : normK 100 7 mG1 2 dG1 2 W1 = true := by quickRfl

theorem ch799102_w2 : normK 100 7 mG2 3 dG2 2 W2 = true := by quickRfl

theorem ch799102_w3 : normK 100 7 mG3 4 dG3 2 W3 = true := by quickRfl

end CertificateChecks.KernelHS799102

end
