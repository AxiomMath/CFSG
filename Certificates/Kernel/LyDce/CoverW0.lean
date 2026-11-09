module

public import Certificates.Kernel.LyDce.CoverWalkDefs
public import CFSG.Certificates.Kernel.Common.EachTrue
public import CFSG.Certificates.Kernel.LyDce.CoverWalkCutSound
import Certificates.Kernel.LyDce.WalkCutCmd
import CFSG.Certificates.Kernel.Common.Harness

set_option Elab.async false
set_option profiler true
set_option profiler.threshold 100
set_option maxRecDepth 1000000

public section

#lydce_cuts CertificateChecks.KernelLyDce.Wc0 CertificateChecks.KernelLyB.N0
  CertificateChecks.KernelLyB.N1 CertificateChecks.KernelLyDce.o0 CertificateChecks.KernelLyDce.dfs 0
  [265, 489, 771]
#lydce_cuts CertificateChecks.KernelLyDce.Wc1 CertificateChecks.KernelLyB.N0
  CertificateChecks.KernelLyB.N1 CertificateChecks.KernelLyDce.o0 CertificateChecks.KernelLyDce.dfs 1
  [255, 504, 767]
#lydce_cuts CertificateChecks.KernelLyDce.Wc2 CertificateChecks.KernelLyB.N0
  CertificateChecks.KernelLyB.N1 CertificateChecks.KernelLyDce.o0 CertificateChecks.KernelLyDce.dfs 2
  [273, 524, 749]
#lydce_cuts CertificateChecks.KernelLyDce.Wc3 CertificateChecks.KernelLyB.N0
  CertificateChecks.KernelLyB.N1 CertificateChecks.KernelLyDce.o0 CertificateChecks.KernelLyDce.dfs 3
  [257, 518, 768]

namespace CertificateChecks.KernelLyDce

open CFSG.KC CFSG.KC.LyDce CertificateChecks.KernelLyB

theorem wcp0_0 :
    walkSFromTo (NS 0) (NS 1) pk kp tc td (maskOf o0) (((dfs.getD (nat_lit 0) []).drop 0).take (265 - 0))
      Wc0.X1 = true := by quickRfl

theorem wcp0_1 :
    walkSTo (NS 0) (NS 1) pk kp tc td (((dfs.getD (nat_lit 0) []).drop 265).take (489 - 265))
      (Wc0.X1.map (tri (NS 0) (NS 1))) Wc0.X2 = true := by quickRfl

theorem wcp0_2 :
    walkSTo (NS 0) (NS 1) pk kp tc td (((dfs.getD (nat_lit 0) []).drop 489).take (771 - 489))
      (Wc0.X2.map (tri (NS 0) (NS 1))) Wc0.X3 = true := by quickRfl

theorem wcp0_3 :
    walkS (NS 0) (NS 1) pk kp tc td ((dfs.getD (nat_lit 0) []).drop 771) (Wc0.X3.map (tri (NS 0) (NS 1))) = true := by
  quickRfl

theorem wk0 : walkSAt (nat_lit 0) = true :=
  walkSFrom_cut wcp0_0
    (walkS_cut (triInv_map _ _ _) (by decide) wcp0_1
      (walkS_cut (triInv_map _ _ _) (by decide) wcp0_2
      wcp0_3))

theorem wcp1_0 :
    walkSFromTo (NS 0) (NS 1) pk kp tc td (maskOf o0) (((dfs.getD (nat_lit 1) []).drop 0).take (255 - 0))
      Wc1.X1 = true := by quickRfl

theorem wcp1_1 :
    walkSTo (NS 0) (NS 1) pk kp tc td (((dfs.getD (nat_lit 1) []).drop 255).take (504 - 255))
      (Wc1.X1.map (tri (NS 0) (NS 1))) Wc1.X2 = true := by quickRfl

theorem wcp1_2 :
    walkSTo (NS 0) (NS 1) pk kp tc td (((dfs.getD (nat_lit 1) []).drop 504).take (767 - 504))
      (Wc1.X2.map (tri (NS 0) (NS 1))) Wc1.X3 = true := by quickRfl

theorem wcp1_3 :
    walkS (NS 0) (NS 1) pk kp tc td ((dfs.getD (nat_lit 1) []).drop 767) (Wc1.X3.map (tri (NS 0) (NS 1))) = true := by
  quickRfl

theorem wk1 : walkSAt (nat_lit 1) = true :=
  walkSFrom_cut wcp1_0
    (walkS_cut (triInv_map _ _ _) (by decide) wcp1_1
      (walkS_cut (triInv_map _ _ _) (by decide) wcp1_2
      wcp1_3))

theorem wcp2_0 :
    walkSFromTo (NS 0) (NS 1) pk kp tc td (maskOf o0) (((dfs.getD (nat_lit 2) []).drop 0).take (273 - 0))
      Wc2.X1 = true := by quickRfl

theorem wcp2_1 :
    walkSTo (NS 0) (NS 1) pk kp tc td (((dfs.getD (nat_lit 2) []).drop 273).take (524 - 273))
      (Wc2.X1.map (tri (NS 0) (NS 1))) Wc2.X2 = true := by quickRfl

theorem wcp2_2 :
    walkSTo (NS 0) (NS 1) pk kp tc td (((dfs.getD (nat_lit 2) []).drop 524).take (749 - 524))
      (Wc2.X2.map (tri (NS 0) (NS 1))) Wc2.X3 = true := by quickRfl

theorem wcp2_3 :
    walkS (NS 0) (NS 1) pk kp tc td ((dfs.getD (nat_lit 2) []).drop 749) (Wc2.X3.map (tri (NS 0) (NS 1))) = true := by
  quickRfl

theorem wk2 : walkSAt (nat_lit 2) = true :=
  walkSFrom_cut wcp2_0
    (walkS_cut (triInv_map _ _ _) (by decide) wcp2_1
      (walkS_cut (triInv_map _ _ _) (by decide) wcp2_2
      wcp2_3))

theorem wcp3_0 :
    walkSFromTo (NS 0) (NS 1) pk kp tc td (maskOf o0) (((dfs.getD (nat_lit 3) []).drop 0).take (257 - 0))
      Wc3.X1 = true := by quickRfl

theorem wcp3_1 :
    walkSTo (NS 0) (NS 1) pk kp tc td (((dfs.getD (nat_lit 3) []).drop 257).take (518 - 257))
      (Wc3.X1.map (tri (NS 0) (NS 1))) Wc3.X2 = true := by quickRfl

theorem wcp3_2 :
    walkSTo (NS 0) (NS 1) pk kp tc td (((dfs.getD (nat_lit 3) []).drop 518).take (768 - 518))
      (Wc3.X2.map (tri (NS 0) (NS 1))) Wc3.X3 = true := by quickRfl

theorem wcp3_3 :
    walkS (NS 0) (NS 1) pk kp tc td ((dfs.getD (nat_lit 3) []).drop 768) (Wc3.X3.map (tri (NS 0) (NS 1))) = true := by
  quickRfl

theorem wk3 : walkSAt (nat_lit 3) = true :=
  walkSFrom_cut wcp3_0
    (walkS_cut (triInv_map _ _ _) (by decide) wcp3_1
      (walkS_cut (triInv_map _ _ _) (by decide) wcp3_2
      wcp3_3))

end CertificateChecks.KernelLyDce

end
