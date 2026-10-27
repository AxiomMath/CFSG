module

public import Certificates.Data.Kernel.Q16Q16K
public import Certificates.Kernel.Census.M22II.Data
import all Certificates.Kernel.Census.M22II.Data
import all Certificates.Data.Kernel.Q16Q16K
import all Certificates.Data.Kernel.Census.Packed
import all CFSG.Certificates.Kernel.Enum.Defs
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelQ16M22

open CFSG.KC.Q16Q16K CertificateChecks.KernelCensus.M22II

set_option maxRecDepth 400000

@[expose] noncomputable def q16M22R : List Rec := m22IICS.pts.toList.map (mkRec 24 5)

theorem q16M22F0 : allL (chkX 24 5 q16M22R) ((q16M22R.drop 0).take 32) = true := by quickRfl
theorem q16M22F1 : allL (chkX 24 5 q16M22R) ((q16M22R.drop 32).take 32) = true := by quickRfl
theorem q16M22F2 : allL (chkX 24 5 q16M22R) ((q16M22R.drop 64).take 32) = true := by quickRfl
theorem q16M22F3 : allL (chkX 24 5 q16M22R) ((q16M22R.drop 96).take 32) = true := by quickRfl
theorem q16M22F4 : allL (chkX 24 5 q16M22R) ((q16M22R.drop 128).take 32) = true := by quickRfl
theorem q16M22F5 : allL (chkX 24 5 q16M22R) ((q16M22R.drop 160).take 32) = true := by quickRfl
theorem q16M22F6 : allL (chkX 24 5 q16M22R) ((q16M22R.drop 192).take 32) = true := by quickRfl
theorem q16M22F7 : allL (chkX 24 5 q16M22R) (q16M22R.drop 224) = true := by quickRfl

end CertificateChecks.KernelQ16M22
