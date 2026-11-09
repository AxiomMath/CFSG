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

#kc_each CertificateChecks.KernelLyDce wk (fun i => CertificateChecks.KernelLyDce.walkSAt i) 15 16

#lydce_cuts CertificateChecks.KernelLyDce.Wc12 CertificateChecks.KernelLyB.N0
  CertificateChecks.KernelLyB.N1 CertificateChecks.KernelLyDce.o0 CertificateChecks.KernelLyDce.dfs 12
  [238, 484, 756]
#lydce_cuts CertificateChecks.KernelLyDce.Wc13 CertificateChecks.KernelLyB.N0
  CertificateChecks.KernelLyB.N1 CertificateChecks.KernelLyDce.o0 CertificateChecks.KernelLyDce.dfs 13
  [267, 516, 791]
#lydce_cuts CertificateChecks.KernelLyDce.Wc14 CertificateChecks.KernelLyB.N0
  CertificateChecks.KernelLyB.N1 CertificateChecks.KernelLyDce.o0 CertificateChecks.KernelLyDce.dfs 14
  [263, 489, 743]

namespace CertificateChecks.KernelLyDce

open CFSG.KC CFSG.KC.LyDce CertificateChecks.KernelLyB

theorem wcp12_0 :
    walkSFromTo (NS 0) (NS 1) pk kp tc td (maskOf o0) (((dfs.getD (nat_lit 12) []).drop 0).take (238 - 0))
      Wc12.X1 = true := by quickRfl

theorem wcp12_1 :
    walkSTo (NS 0) (NS 1) pk kp tc td (((dfs.getD (nat_lit 12) []).drop 238).take (484 - 238))
      (Wc12.X1.map (tri (NS 0) (NS 1))) Wc12.X2 = true := by quickRfl

theorem wcp12_2 :
    walkSTo (NS 0) (NS 1) pk kp tc td (((dfs.getD (nat_lit 12) []).drop 484).take (756 - 484))
      (Wc12.X2.map (tri (NS 0) (NS 1))) Wc12.X3 = true := by quickRfl

theorem wcp12_3 :
    walkS (NS 0) (NS 1) pk kp tc td ((dfs.getD (nat_lit 12) []).drop 756) (Wc12.X3.map (tri (NS 0) (NS 1))) = true := by
  quickRfl

theorem wk12 : walkSAt (nat_lit 12) = true :=
  walkSFrom_cut wcp12_0
    (walkS_cut (triInv_map _ _ _) (by decide) wcp12_1
      (walkS_cut (triInv_map _ _ _) (by decide) wcp12_2
      wcp12_3))

theorem wcp13_0 :
    walkSFromTo (NS 0) (NS 1) pk kp tc td (maskOf o0) (((dfs.getD (nat_lit 13) []).drop 0).take (267 - 0))
      Wc13.X1 = true := by quickRfl

theorem wcp13_1 :
    walkSTo (NS 0) (NS 1) pk kp tc td (((dfs.getD (nat_lit 13) []).drop 267).take (516 - 267))
      (Wc13.X1.map (tri (NS 0) (NS 1))) Wc13.X2 = true := by quickRfl

theorem wcp13_2 :
    walkSTo (NS 0) (NS 1) pk kp tc td (((dfs.getD (nat_lit 13) []).drop 516).take (791 - 516))
      (Wc13.X2.map (tri (NS 0) (NS 1))) Wc13.X3 = true := by quickRfl

theorem wcp13_3 :
    walkS (NS 0) (NS 1) pk kp tc td ((dfs.getD (nat_lit 13) []).drop 791) (Wc13.X3.map (tri (NS 0) (NS 1))) = true := by
  quickRfl

theorem wk13 : walkSAt (nat_lit 13) = true :=
  walkSFrom_cut wcp13_0
    (walkS_cut (triInv_map _ _ _) (by decide) wcp13_1
      (walkS_cut (triInv_map _ _ _) (by decide) wcp13_2
      wcp13_3))

theorem wcp14_0 :
    walkSFromTo (NS 0) (NS 1) pk kp tc td (maskOf o0) (((dfs.getD (nat_lit 14) []).drop 0).take (263 - 0))
      Wc14.X1 = true := by quickRfl

theorem wcp14_1 :
    walkSTo (NS 0) (NS 1) pk kp tc td (((dfs.getD (nat_lit 14) []).drop 263).take (489 - 263))
      (Wc14.X1.map (tri (NS 0) (NS 1))) Wc14.X2 = true := by quickRfl

theorem wcp14_2 :
    walkSTo (NS 0) (NS 1) pk kp tc td (((dfs.getD (nat_lit 14) []).drop 489).take (743 - 489))
      (Wc14.X2.map (tri (NS 0) (NS 1))) Wc14.X3 = true := by quickRfl

theorem wcp14_3 :
    walkS (NS 0) (NS 1) pk kp tc td ((dfs.getD (nat_lit 14) []).drop 743) (Wc14.X3.map (tri (NS 0) (NS 1))) = true := by
  quickRfl

theorem wk14 : walkSAt (nat_lit 14) = true :=
  walkSFrom_cut wcp14_0
    (walkS_cut (triInv_map _ _ _) (by decide) wcp14_1
      (walkS_cut (triInv_map _ _ _) (by decide) wcp14_2
      wcp14_3))

end CertificateChecks.KernelLyDce

end
