module

public import Certificates.Data.Kernel.T84S4.Check
public import Certificates.Kernel.T84S4.Data
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelT84S4

open CFSG.KD.T84S4

theorem ch442352_list : listB ACT TM L3 L4 I2 = true := by quickRfl
theorem ch442352_words : wordsB ACT TM WP = true := by quickRfl
theorem ch442352_cut : (S0 ++ S1 ++ S2 ++ S3 ++ S4 ++ S5 ++ S6 ++ S7 == L3) = true := by quickRfl
theorem ch442352_inv : invB ACT TM INV = true := by quickRfl
theorem ch442352_norm : normB ACT TM INV = true := by quickRfl
theorem ch442352_gen3 : gen3B ACT TM = true := by quickRfl
theorem ch442352_fpf : fpfB ACT TM = true := by quickRfl

theorem ch442352_tab0 : tabB ACT TM TC 0 16 = true := by quickRfl
theorem ch442352_tab1 : tabB ACT TM TC 16 16 = true := by quickRfl
theorem ch442352_tab2 : tabB ACT TM TC 32 16 = true := by quickRfl
theorem ch442352_tab3 : tabB ACT TM TC 48 16 = true := by quickRfl
theorem ch442352_tab4 : tabB ACT TM TC 64 16 = true := by quickRfl
theorem ch442352_tab5 : tabB ACT TM TC 80 16 = true := by quickRfl
theorem ch442352_tab6 : tabB ACT TM TC 96 16 = true := by quickRfl
theorem ch442352_tab7 : tabB ACT TM TC 112 16 = true := by quickRfl
theorem ch442352_tab8 : tabB ACT TM TC 128 16 = true := by quickRfl
theorem ch442352_tab9 : tabB ACT TM TC 144 16 = true := by quickRfl
theorem ch442352_tab10 : tabB ACT TM TC 160 16 = true := by quickRfl
theorem ch442352_tab11 : tabB ACT TM TC 176 16 = true := by quickRfl

theorem ch442352_odd0 : oddB TC 0 4 = true := by quickRfl
theorem ch442352_odd1 : oddB TC 4 4 = true := by quickRfl
theorem ch442352_odd2 : oddB TC 8 4 = true := by quickRfl
theorem ch442352_odd3 : oddB TC 12 4 = true := by quickRfl

end CertificateChecks.KernelT84S4

end
