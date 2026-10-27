module

public import Certificates.Data.Kernel.OpsLayMcert
public import Certificates.Kernel.LocalComp.LaySeeds
public import Certificates.Kernel.LocalComp.LaySnaps
public import Certificates.Kernel.Ly3.Prog
meta import Certificates.Kernel.Ly3.Prog
public import CFSG.Certificates.Kernel.Common.Each
public import CFSG.Certificates.Kernel.Common.ForallTree
import CFSG.Certificates.Kernel.Common.Harness
import all CFSG.Blueprint.NativeSporadic

set_option maxRecDepth 400000
set_option Elab.async false

#lay_seeds CertificateChecks.KernelLy3.L 5 111
  CFSG.Blueprint.NativeSporadic.LySeed1 CFSG.Blueprint.NativeSporadic.LySeed2

#lay_snaps CertificateChecks.KernelLy3.S 5 111 CertificateChecks.KernelLy3.L.A
  CertificateChecks.KernelLy3.L.B CertificateChecks.KernelLy3.prog 9 50

public section

namespace CertificateChecks.KernelLy3

open CFSG.KC.OpsLayK CertificateChecks.KernelLy3.L

@[expose] noncomputable def chLy3 (i : Nat) : Bool :=
  chunkL lay prog 50 i (S.SL.getD i []) (S.SL.getD (i + 1) [])

theorem init : eqL (S.SL.getD 0 []) (initR lay A B 9) = true := by quickRfl

#kc_each chLy3 0 4

#kc_forall_tree ch_all (fun i => chLy3 i = true) 4 CertificateChecks.KernelLy3.chLy3

theorem m_eq : S.m = 4 := rfl

theorem ch_neg : (!chunkL lay prog 50 0 (S.SL.getD 0 []) (S.SL.getD 2 [])) = true := by
  quickRfl

@[expose] noncomputable def RF : List Nat := S.SL.getD 4 []

@[expose] noncomputable def X (i : Nat) : Nat := getR lay RF ([5, 7, 8].getD i 0)

end CertificateChecks.KernelLy3

end
