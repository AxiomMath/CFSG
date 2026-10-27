module

public import Certificates.Data.Kernel.OpsRenL
public import Certificates.Kernel.Fi23U3.Snaps
public import Certificates.Kernel.LocalComp.LaySnapsFrom
public import CFSG.Certificates.Kernel.Common.Each
public import CFSG.Certificates.Kernel.Common.ForallTree
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

set_option maxRecDepth 400000
set_option Elab.async false

#kc_repo #kc_json_gz CertificateChecks.KernelFi23U3.D "Certificates/Kernel/Fi23U3/data/chain.json.gz"
  10930 3410109472472256960 (cs : List CFSG.KC.OpsLayK.RChunk) (B : List (List Nat))
  (G : List (List Nat)) (T : List (List Nat))

#lay_snaps_from CertificateChecks.KernelFi23U3.Q 3 253 CertificateChecks.KernelFi23U3.S.S5
  CertificateChecks.KernelFi23U3.D.cs

public section

namespace CertificateChecks.KernelFi23U3

open CFSG.KC.OpsLayK CertificateChecks.KernelTc.Fi23

theorem cs_length : D.cs.length = 4 := rfl

theorem q0_eq : Q.S0 = S.S5 := rfl

@[expose] noncomputable def rc (i : Nat) : Bool :=
  chunkV lay (D.cs.getD i (0, [], [])) (Q.SL.getD i []) (Q.SL.getD (i + 1) [])

#kc_each rc 0 4

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
