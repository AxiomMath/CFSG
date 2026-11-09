module

public import Certificates.Data.Kernel.OpsRenL
public import Certificates.Kernel.Fi23U3.Snaps
public import Certificates.Kernel.LocalComp.LaySnapsFrom
public import CFSG.Certificates.Kernel.Common.Each
public import CFSG.Certificates.Kernel.Common.ForallTree
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo
public import CFSG.Certificates.Kernel.LocalQT.RunF3Sound
import Certificates.Kernel.LocalComp.LayF3Cuts

set_option maxRecDepth 400000
set_option Elab.async false

#kc_repo #kc_json CertificateChecks.KernelFi23U3.D "Certificates/Kernel/Fi23U3/data/chain.json"
  10930 3410109472472256960 (cs : List CFSG.KC.OpsLayK.RChunk) (B : List (List Nat))
  (G : List (List Nat)) (T : List (List Nat))

#lay_snaps_from CertificateChecks.KernelFi23U3.Q 3 253 CertificateChecks.KernelFi23U3.S.S5
  CertificateChecks.KernelFi23U3.D.cs

#lay_f3_cuts_v CertificateChecks.KernelFi23U3.F3r1 3 253 16 CertificateChecks.KernelFi23U3.Q.S1
  CertificateChecks.KernelFi23U3.D.cs 1 [60, 120]
#lay_f3_cuts_v CertificateChecks.KernelFi23U3.F3r2 3 253 16 CertificateChecks.KernelFi23U3.Q.S2
  CertificateChecks.KernelFi23U3.D.cs 2 [60, 120]
#lay_f3_cuts_v CertificateChecks.KernelFi23U3.F3r3 3 253 16 CertificateChecks.KernelFi23U3.Q.S3
  CertificateChecks.KernelFi23U3.D.cs 3 [60]

public section

namespace CertificateChecks.KernelFi23U3

open CFSG.KC.OpsLayK CertificateChecks.KernelTc.Fi23 CFSG.KC.OpsLayF3

theorem cs_length : D.cs.length = 4 := rfl

theorem q0_eq : Q.S0 = S.S5 := rfl

@[expose] noncomputable def rc (i : Nat) : Bool :=
  chunkV lay (D.cs.getD i (0, [], [])) (Q.SL.getD i []) (Q.SL.getD (i + 1) [])

#kc_each rc 0 1

theorem f3pr1_0 :
    runV (ctxOf lay 16) ((((D.cs.getD 1 (0, [], [])).2.1.map opOf).drop 0).take (60 - 0))
      (gL lay 16 (padR lay (Q.SL.getD 1 []) (D.cs.getD 1 (0, [], [])).1))
      (fun R => eqVL R F3r1.M1) = true := by quickRfl

theorem f3pr1_1 :
    runV (ctxOf lay 16) ((((D.cs.getD 1 (0, [], [])).2.1.map opOf).drop 60).take (120 - 60))
      F3r1.M1
      (fun R => eqVL R F3r1.M2) = true := by quickRfl

theorem f3pr1_2 :
    runV (ctxOf lay 16) (((D.cs.getD 1 (0, [], [])).2.1.map opOf).drop 120)
      F3r1.M2
      (fun R => eqVL ((D.cs.getD 1 (0, [], [])).2.2.map (getV (ctxOf lay 16) R))
        (gL lay 16 (Q.SL.getD (1 + 1) []))) = true := by quickRfl

theorem f3vr1 : (allValid lay (Q.SL.getD 1 []) && allValid lay (Q.SL.getD (1 + 1) [])) = true := by
  quickRfl

theorem rc1 : rc (nat_lit 1) = true :=
  chunkV_of_F3 f3good (chunkV3_intro f3vr1
    (runV_split (by decide) f3pr1_0
      (runV_split (by decide) f3pr1_1
      f3pr1_2)))

theorem f3pr2_0 :
    runV (ctxOf lay 16) ((((D.cs.getD 2 (0, [], [])).2.1.map opOf).drop 0).take (60 - 0))
      (gL lay 16 (padR lay (Q.SL.getD 2 []) (D.cs.getD 2 (0, [], [])).1))
      (fun R => eqVL R F3r2.M1) = true := by quickRfl

theorem f3pr2_1 :
    runV (ctxOf lay 16) ((((D.cs.getD 2 (0, [], [])).2.1.map opOf).drop 60).take (120 - 60))
      F3r2.M1
      (fun R => eqVL R F3r2.M2) = true := by quickRfl

theorem f3pr2_2 :
    runV (ctxOf lay 16) (((D.cs.getD 2 (0, [], [])).2.1.map opOf).drop 120)
      F3r2.M2
      (fun R => eqVL ((D.cs.getD 2 (0, [], [])).2.2.map (getV (ctxOf lay 16) R))
        (gL lay 16 (Q.SL.getD (2 + 1) []))) = true := by quickRfl

theorem f3vr2 : (allValid lay (Q.SL.getD 2 []) && allValid lay (Q.SL.getD (2 + 1) [])) = true := by
  quickRfl

theorem rc2 : rc (nat_lit 2) = true :=
  chunkV_of_F3 f3good (chunkV3_intro f3vr2
    (runV_split (by decide) f3pr2_0
      (runV_split (by decide) f3pr2_1
      f3pr2_2)))

theorem f3pr3_0 :
    runV (ctxOf lay 16) ((((D.cs.getD 3 (0, [], [])).2.1.map opOf).drop 0).take (60 - 0))
      (gL lay 16 (padR lay (Q.SL.getD 3 []) (D.cs.getD 3 (0, [], [])).1))
      (fun R => eqVL R F3r3.M1) = true := by quickRfl

theorem f3pr3_1 :
    runV (ctxOf lay 16) (((D.cs.getD 3 (0, [], [])).2.1.map opOf).drop 60)
      F3r3.M1
      (fun R => eqVL ((D.cs.getD 3 (0, [], [])).2.2.map (getV (ctxOf lay 16) R))
        (gL lay 16 (Q.SL.getD (3 + 1) []))) = true := by quickRfl

theorem f3vr3 : (allValid lay (Q.SL.getD 3 []) && allValid lay (Q.SL.getD (3 + 1) [])) = true := by
  quickRfl

theorem rc3 : rc (nat_lit 3) = true :=
  chunkV_of_F3 f3good (chunkV3_intro f3vr3
    (runV_split (by decide) f3pr3_0
      f3pr3_1))

#kc_forall_tree rc_all (fun i => rc i = true) 4 CertificateChecks.KernelFi23U3.rc

theorem rc_neg_sel :
    (!chunkV lay (25, [], [16, 19, 22, 5]) (Q.SL.getD 0 []) (Q.SL.getD 1 [])) = true := by
  quickRfl

theorem rc_neg_op : (!chunkV lay ((D.cs.getD 1 (0, [], [])).1,
    ((D.cs.getD 1 (0, [], [])).2.1.take 1), (D.cs.getD 1 (0, [], [])).2.2)
    (Q.SL.getD 1 []) (Q.SL.getD 2 [])) = true := by
  quickRfl

@[expose] noncomputable def M₀ : List Nat := (Q.SL.getD 4 []).reverse

end CertificateChecks.KernelFi23U3

end
