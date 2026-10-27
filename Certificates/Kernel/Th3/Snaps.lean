module

public import Certificates.Data.Kernel.OpsLayMcert
public import Certificates.Kernel.LocalComp.LaySeeds
public import Certificates.Kernel.LocalComp.LaySnaps
public import Certificates.Kernel.Th3.Prog
meta import Certificates.Kernel.Th3.Prog
public import CFSG.Certificates.Kernel.Common.Each
public import CFSG.Certificates.Kernel.Common.ForallTree
import CFSG.Certificates.Kernel.Common.Harness
import all CFSG.Blueprint.NativeSporadic

set_option maxRecDepth 400000
set_option Elab.async false

#lay_seeds CertificateChecks.KernelTh3.L 2 248
  CFSG.Blueprint.NativeSporadic.ThSeed1 CFSG.Blueprint.NativeSporadic.ThSeed2

#lay_snaps CertificateChecks.KernelTh3.S 2 248 CertificateChecks.KernelTh3.L.A
  CertificateChecks.KernelTh3.L.B CertificateChecks.KernelTh3.prog 8 50

public section

namespace CertificateChecks.KernelTh3

open CFSG.KC.OpsLayK CertificateChecks.KernelTh3.L

@[expose] noncomputable def chTh3 (i : Nat) : Bool :=
  chunkL lay prog 50 i (S.SL.getD i []) (S.SL.getD (i + 1) [])

theorem init : eqL (S.SL.getD 0 []) (initR lay A B 8) = true := by quickRfl

#kc_each chTh3 0 3

#kc_forall_tree ch_all (fun i => chTh3 i = true) 3 CertificateChecks.KernelTh3.chTh3

theorem m_eq : S.m = 3 := rfl

theorem ch_neg : (!chunkL lay prog 50 0 (S.SL.getD 0 []) (S.SL.getD 2 [])) = true := by
  quickRfl

@[expose] noncomputable def RF : List Nat := S.SL.getD 3 []

@[expose] noncomputable def X (i : Nat) : Nat := getR lay RF ([5, 4, 7].getD i 0)

end CertificateChecks.KernelTh3

end
