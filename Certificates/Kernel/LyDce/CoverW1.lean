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

#lydce_cuts CertificateChecks.KernelLyDce.Wc4 CertificateChecks.KernelLyB.N0
  CertificateChecks.KernelLyB.N1 CertificateChecks.KernelLyDce.o0 CertificateChecks.KernelLyDce.dfs 4
  [243, 525, 789]
#lydce_cuts CertificateChecks.KernelLyDce.Wc5 CertificateChecks.KernelLyB.N0
  CertificateChecks.KernelLyB.N1 CertificateChecks.KernelLyDce.o0 CertificateChecks.KernelLyDce.dfs 5
  [237, 482, 781]
#lydce_cuts CertificateChecks.KernelLyDce.Wc6 CertificateChecks.KernelLyB.N0
  CertificateChecks.KernelLyB.N1 CertificateChecks.KernelLyDce.o0 CertificateChecks.KernelLyDce.dfs 6
  [261, 523, 769]
#lydce_cuts CertificateChecks.KernelLyDce.Wc7 CertificateChecks.KernelLyB.N0
  CertificateChecks.KernelLyB.N1 CertificateChecks.KernelLyDce.o0 CertificateChecks.KernelLyDce.dfs 7
  [255, 489, 782]

namespace CertificateChecks.KernelLyDce

open CFSG.KC CFSG.KC.LyDce CertificateChecks.KernelLyB

theorem wcp4_0 :
    walkSFromTo (NS 0) (NS 1) pk kp tc td (maskOf o0) (((dfs.getD (nat_lit 4) []).drop 0).take (243 - 0))
      Wc4.X1 = true := by quickRfl

theorem wcp4_1 :
    walkSTo (NS 0) (NS 1) pk kp tc td (((dfs.getD (nat_lit 4) []).drop 243).take (525 - 243))
      (Wc4.X1.map (tri (NS 0) (NS 1))) Wc4.X2 = true := by quickRfl

theorem wcp4_2 :
    walkSTo (NS 0) (NS 1) pk kp tc td (((dfs.getD (nat_lit 4) []).drop 525).take (789 - 525))
      (Wc4.X2.map (tri (NS 0) (NS 1))) Wc4.X3 = true := by quickRfl

theorem wcp4_3 :
    walkS (NS 0) (NS 1) pk kp tc td ((dfs.getD (nat_lit 4) []).drop 789) (Wc4.X3.map (tri (NS 0) (NS 1))) = true := by
  quickRfl

theorem wk4 : walkSAt (nat_lit 4) = true :=
  walkSFrom_cut wcp4_0
    (walkS_cut (triInv_map _ _ _) (by decide) wcp4_1
      (walkS_cut (triInv_map _ _ _) (by decide) wcp4_2
      wcp4_3))

theorem wcp5_0 :
    walkSFromTo (NS 0) (NS 1) pk kp tc td (maskOf o0) (((dfs.getD (nat_lit 5) []).drop 0).take (237 - 0))
      Wc5.X1 = true := by quickRfl

theorem wcp5_1 :
    walkSTo (NS 0) (NS 1) pk kp tc td (((dfs.getD (nat_lit 5) []).drop 237).take (482 - 237))
      (Wc5.X1.map (tri (NS 0) (NS 1))) Wc5.X2 = true := by quickRfl

theorem wcp5_2 :
    walkSTo (NS 0) (NS 1) pk kp tc td (((dfs.getD (nat_lit 5) []).drop 482).take (781 - 482))
      (Wc5.X2.map (tri (NS 0) (NS 1))) Wc5.X3 = true := by quickRfl

theorem wcp5_3 :
    walkS (NS 0) (NS 1) pk kp tc td ((dfs.getD (nat_lit 5) []).drop 781) (Wc5.X3.map (tri (NS 0) (NS 1))) = true := by
  quickRfl

theorem wk5 : walkSAt (nat_lit 5) = true :=
  walkSFrom_cut wcp5_0
    (walkS_cut (triInv_map _ _ _) (by decide) wcp5_1
      (walkS_cut (triInv_map _ _ _) (by decide) wcp5_2
      wcp5_3))

theorem wcp6_0 :
    walkSFromTo (NS 0) (NS 1) pk kp tc td (maskOf o0) (((dfs.getD (nat_lit 6) []).drop 0).take (261 - 0))
      Wc6.X1 = true := by quickRfl

theorem wcp6_1 :
    walkSTo (NS 0) (NS 1) pk kp tc td (((dfs.getD (nat_lit 6) []).drop 261).take (523 - 261))
      (Wc6.X1.map (tri (NS 0) (NS 1))) Wc6.X2 = true := by quickRfl

theorem wcp6_2 :
    walkSTo (NS 0) (NS 1) pk kp tc td (((dfs.getD (nat_lit 6) []).drop 523).take (769 - 523))
      (Wc6.X2.map (tri (NS 0) (NS 1))) Wc6.X3 = true := by quickRfl

theorem wcp6_3 :
    walkS (NS 0) (NS 1) pk kp tc td ((dfs.getD (nat_lit 6) []).drop 769) (Wc6.X3.map (tri (NS 0) (NS 1))) = true := by
  quickRfl

theorem wk6 : walkSAt (nat_lit 6) = true :=
  walkSFrom_cut wcp6_0
    (walkS_cut (triInv_map _ _ _) (by decide) wcp6_1
      (walkS_cut (triInv_map _ _ _) (by decide) wcp6_2
      wcp6_3))

theorem wcp7_0 :
    walkSFromTo (NS 0) (NS 1) pk kp tc td (maskOf o0) (((dfs.getD (nat_lit 7) []).drop 0).take (255 - 0))
      Wc7.X1 = true := by quickRfl

theorem wcp7_1 :
    walkSTo (NS 0) (NS 1) pk kp tc td (((dfs.getD (nat_lit 7) []).drop 255).take (489 - 255))
      (Wc7.X1.map (tri (NS 0) (NS 1))) Wc7.X2 = true := by quickRfl

theorem wcp7_2 :
    walkSTo (NS 0) (NS 1) pk kp tc td (((dfs.getD (nat_lit 7) []).drop 489).take (782 - 489))
      (Wc7.X2.map (tri (NS 0) (NS 1))) Wc7.X3 = true := by quickRfl

theorem wcp7_3 :
    walkS (NS 0) (NS 1) pk kp tc td ((dfs.getD (nat_lit 7) []).drop 782) (Wc7.X3.map (tri (NS 0) (NS 1))) = true := by
  quickRfl

theorem wk7 : walkSAt (nat_lit 7) = true :=
  walkSFrom_cut wcp7_0
    (walkS_cut (triInv_map _ _ _) (by decide) wcp7_1
      (walkS_cut (triInv_map _ _ _) (by decide) wcp7_2
      wcp7_3))

end CertificateChecks.KernelLyDce

end
