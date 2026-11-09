module

public import Certificates.Data.Kernel.OpsLayMcert
public import Certificates.Kernel.LocalComp.LaySnaps
public import Certificates.Kernel.TcGen.Fi23
public import Certificates.Kernel.Fi23U3.Prog
meta import Certificates.Kernel.Fi23U3.Prog
public import CFSG.Certificates.Kernel.Common.Each
public import CFSG.Certificates.Kernel.Common.ForallTree
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.LocalQT.RunF3Sound
import Certificates.Kernel.LocalComp.LayF3Cuts

set_option maxRecDepth 400000
set_option Elab.async false

#lay_snaps CertificateChecks.KernelFi23U3.S 3 253 CertificateChecks.KernelTc.Fi23.A
  CertificateChecks.KernelTc.Fi23.B CertificateChecks.KernelFi23U3.prog 25 50

#lay_f3_cuts_l CertificateChecks.KernelFi23U3.F3u2 3 253 16 CertificateChecks.KernelFi23U3.S.S2
  CertificateChecks.KernelFi23U3.prog 50 2 [45]
#lay_f3_cuts_l CertificateChecks.KernelFi23U3.F3u3 3 253 16 CertificateChecks.KernelFi23U3.S.S3
  CertificateChecks.KernelFi23U3.prog 50 3 [37]

public section

namespace CertificateChecks.KernelFi23U3

open CFSG.KC.OpsLayK CertificateChecks.KernelTc.Fi23 CFSG.KC.OpsLayF3

@[expose] noncomputable def chU (i : Nat) : Bool :=
  chunkL lay prog 50 i (S.SL.getD i []) (S.SL.getD (i + 1) [])

theorem init : eqL (S.SL.getD 0 []) (initR lay A B 25) = true := by quickRfl

#kc_each chU 0 2
#kc_each chU 4 5

theorem f3good : Good lay 16 := ⟨lay_ok, rfl, by decide, by decide⟩

theorem f3pu2_0 :
    runV (ctxOf lay 16) ((((prog.drop (2 * 50)).take 50).drop 0).take (45 - 0))
      (gL lay 16 (S.SL.getD 2 []))
      (fun R => eqVL R F3u2.M1) = true := by quickRfl

theorem f3pu2_1 :
    runV (ctxOf lay 16) (((prog.drop (2 * 50)).take 50).drop 45)
      F3u2.M1
      (fun R => eqVL R (gL lay 16 (S.SL.getD (2 + 1) []))) = true := by quickRfl

theorem f3vu2 : (allValid lay (S.SL.getD 2 []) && allValid lay (S.SL.getD (2 + 1) [])) = true := by
  quickRfl

theorem chU2 : chU (nat_lit 2) = true :=
  chunkL_of_F3 f3good (chunkL3_intro f3vu2
    (runV_split (by decide) f3pu2_0
      f3pu2_1))

theorem f3pu3_0 :
    runV (ctxOf lay 16) ((((prog.drop (3 * 50)).take 50).drop 0).take (37 - 0))
      (gL lay 16 (S.SL.getD 3 []))
      (fun R => eqVL R F3u3.M1) = true := by quickRfl

theorem f3pu3_1 :
    runV (ctxOf lay 16) (((prog.drop (3 * 50)).take 50).drop 37)
      F3u3.M1
      (fun R => eqVL R (gL lay 16 (S.SL.getD (3 + 1) []))) = true := by quickRfl

theorem f3vu3 : (allValid lay (S.SL.getD 3 []) && allValid lay (S.SL.getD (3 + 1) [])) = true := by
  quickRfl

theorem chU3 : chU (nat_lit 3) = true :=
  chunkL_of_F3 f3good (chunkL3_intro f3vu3
    (runV_split (by decide) f3pu3_0
      f3pu3_1))

#kc_forall_tree ch_all (fun i => chU i = true) 5 CertificateChecks.KernelFi23U3.chU

theorem m_eq : S.m = 5 := rfl

theorem ch_neg : (!chunkL lay prog 50 0 (S.SL.getD 0 []) (S.SL.getD 2 [])) = true := by
  quickRfl

@[expose] noncomputable def RF : List Nat := S.SL.getD 5 []

@[expose] noncomputable def X (i : Nat) : Nat := getR lay RF ([16, 19, 22, 4].getD i 0)

end CertificateChecks.KernelFi23U3

end
