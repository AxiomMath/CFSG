module

public import Certificates.Data.Kernel.OpsLayMcert
public import Certificates.Kernel.LocalComp.LaySnaps
public import Certificates.Kernel.TcGen.Fi23
public import Certificates.Kernel.Fi23U3.Prog
meta import Certificates.Kernel.Fi23U3.Prog
public import CFSG.Certificates.Kernel.Common.Each
public import CFSG.Certificates.Kernel.Common.ForallTree
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000
set_option Elab.async false

#lay_snaps CertificateChecks.KernelFi23U3.S 3 253 CertificateChecks.KernelTc.Fi23.A
  CertificateChecks.KernelTc.Fi23.B CertificateChecks.KernelFi23U3.prog 25 50

public section

namespace CertificateChecks.KernelFi23U3

open CFSG.KC.OpsLayK CertificateChecks.KernelTc.Fi23

@[expose] noncomputable def chU (i : Nat) : Bool :=
  chunkL lay prog 50 i (S.SL.getD i []) (S.SL.getD (i + 1) [])

theorem init : eqL (S.SL.getD 0 []) (initR lay A B 25) = true := by quickRfl

#kc_each chU 0 5

#kc_forall_tree ch_all (fun i => chU i = true) 5 CertificateChecks.KernelFi23U3.chU

theorem m_eq : S.m = 5 := rfl

theorem ch_neg : (!chunkL lay prog 50 0 (S.SL.getD 0 []) (S.SL.getD 2 [])) = true := by
  quickRfl

@[expose] noncomputable def RF : List Nat := S.SL.getD 5 []

@[expose] noncomputable def X (i : Nat) : Nat := getR lay RF ([16, 19, 22, 4].getD i 0)

end CertificateChecks.KernelFi23U3

end
