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

#lydce_cuts CertificateChecks.KernelLyDce.Wc8 CertificateChecks.KernelLyB.N0
  CertificateChecks.KernelLyB.N1 CertificateChecks.KernelLyDce.o0 CertificateChecks.KernelLyDce.dfs 8
  [255, 533, 736]
#lydce_cuts CertificateChecks.KernelLyDce.Wc9 CertificateChecks.KernelLyB.N0
  CertificateChecks.KernelLyB.N1 CertificateChecks.KernelLyDce.o0 CertificateChecks.KernelLyDce.dfs 9
  [257, 534, 790]
#lydce_cuts CertificateChecks.KernelLyDce.Wc10 CertificateChecks.KernelLyB.N0
  CertificateChecks.KernelLyB.N1 CertificateChecks.KernelLyDce.o0 CertificateChecks.KernelLyDce.dfs 10
  [261, 505, 790]
#lydce_cuts CertificateChecks.KernelLyDce.Wc11 CertificateChecks.KernelLyB.N0
  CertificateChecks.KernelLyB.N1 CertificateChecks.KernelLyDce.o0 CertificateChecks.KernelLyDce.dfs 11
  [274, 517, 791]

namespace CertificateChecks.KernelLyDce

open CFSG.KC CFSG.KC.LyDce CertificateChecks.KernelLyB

theorem wcp8_0 :
    walkSFromTo (NS 0) (NS 1) pk kp tc td (maskOf o0) (((dfs.getD (nat_lit 8) []).drop 0).take (255 - 0))
      Wc8.X1 = true := by quickRfl

theorem wcp8_1 :
    walkSTo (NS 0) (NS 1) pk kp tc td (((dfs.getD (nat_lit 8) []).drop 255).take (533 - 255))
      (Wc8.X1.map (tri (NS 0) (NS 1))) Wc8.X2 = true := by quickRfl

theorem wcp8_2 :
    walkSTo (NS 0) (NS 1) pk kp tc td (((dfs.getD (nat_lit 8) []).drop 533).take (736 - 533))
      (Wc8.X2.map (tri (NS 0) (NS 1))) Wc8.X3 = true := by quickRfl

theorem wcp8_3 :
    walkS (NS 0) (NS 1) pk kp tc td ((dfs.getD (nat_lit 8) []).drop 736) (Wc8.X3.map (tri (NS 0) (NS 1))) = true := by
  quickRfl

theorem wk8 : walkSAt (nat_lit 8) = true :=
  walkSFrom_cut wcp8_0
    (walkS_cut (triInv_map _ _ _) (by decide) wcp8_1
      (walkS_cut (triInv_map _ _ _) (by decide) wcp8_2
      wcp8_3))

theorem wcp9_0 :
    walkSFromTo (NS 0) (NS 1) pk kp tc td (maskOf o0) (((dfs.getD (nat_lit 9) []).drop 0).take (257 - 0))
      Wc9.X1 = true := by quickRfl

theorem wcp9_1 :
    walkSTo (NS 0) (NS 1) pk kp tc td (((dfs.getD (nat_lit 9) []).drop 257).take (534 - 257))
      (Wc9.X1.map (tri (NS 0) (NS 1))) Wc9.X2 = true := by quickRfl

theorem wcp9_2 :
    walkSTo (NS 0) (NS 1) pk kp tc td (((dfs.getD (nat_lit 9) []).drop 534).take (790 - 534))
      (Wc9.X2.map (tri (NS 0) (NS 1))) Wc9.X3 = true := by quickRfl

theorem wcp9_3 :
    walkS (NS 0) (NS 1) pk kp tc td ((dfs.getD (nat_lit 9) []).drop 790) (Wc9.X3.map (tri (NS 0) (NS 1))) = true := by
  quickRfl

theorem wk9 : walkSAt (nat_lit 9) = true :=
  walkSFrom_cut wcp9_0
    (walkS_cut (triInv_map _ _ _) (by decide) wcp9_1
      (walkS_cut (triInv_map _ _ _) (by decide) wcp9_2
      wcp9_3))

theorem wcp10_0 :
    walkSFromTo (NS 0) (NS 1) pk kp tc td (maskOf o0) (((dfs.getD (nat_lit 10) []).drop 0).take (261 - 0))
      Wc10.X1 = true := by quickRfl

theorem wcp10_1 :
    walkSTo (NS 0) (NS 1) pk kp tc td (((dfs.getD (nat_lit 10) []).drop 261).take (505 - 261))
      (Wc10.X1.map (tri (NS 0) (NS 1))) Wc10.X2 = true := by quickRfl

theorem wcp10_2 :
    walkSTo (NS 0) (NS 1) pk kp tc td (((dfs.getD (nat_lit 10) []).drop 505).take (790 - 505))
      (Wc10.X2.map (tri (NS 0) (NS 1))) Wc10.X3 = true := by quickRfl

theorem wcp10_3 :
    walkS (NS 0) (NS 1) pk kp tc td ((dfs.getD (nat_lit 10) []).drop 790) (Wc10.X3.map (tri (NS 0) (NS 1))) = true := by
  quickRfl

theorem wk10 : walkSAt (nat_lit 10) = true :=
  walkSFrom_cut wcp10_0
    (walkS_cut (triInv_map _ _ _) (by decide) wcp10_1
      (walkS_cut (triInv_map _ _ _) (by decide) wcp10_2
      wcp10_3))

theorem wcp11_0 :
    walkSFromTo (NS 0) (NS 1) pk kp tc td (maskOf o0) (((dfs.getD (nat_lit 11) []).drop 0).take (274 - 0))
      Wc11.X1 = true := by quickRfl

theorem wcp11_1 :
    walkSTo (NS 0) (NS 1) pk kp tc td (((dfs.getD (nat_lit 11) []).drop 274).take (517 - 274))
      (Wc11.X1.map (tri (NS 0) (NS 1))) Wc11.X2 = true := by quickRfl

theorem wcp11_2 :
    walkSTo (NS 0) (NS 1) pk kp tc td (((dfs.getD (nat_lit 11) []).drop 517).take (791 - 517))
      (Wc11.X2.map (tri (NS 0) (NS 1))) Wc11.X3 = true := by quickRfl

theorem wcp11_3 :
    walkS (NS 0) (NS 1) pk kp tc td ((dfs.getD (nat_lit 11) []).drop 791) (Wc11.X3.map (tri (NS 0) (NS 1))) = true := by
  quickRfl

theorem wk11 : walkSAt (nat_lit 11) = true :=
  walkSFrom_cut wcp11_0
    (walkS_cut (triInv_map _ _ _) (by decide) wcp11_1
      (walkS_cut (triInv_map _ _ _) (by decide) wcp11_2
      wcp11_3))

end CertificateChecks.KernelLyDce

end
