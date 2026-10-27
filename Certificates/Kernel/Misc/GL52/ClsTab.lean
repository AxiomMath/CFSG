module

public import Certificates.Data.Kernel.Misc.GL52Mat
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Repo

#kc_repo #kc_decls CertificateChecks.KernelMisc.GL52K.D "Certificates/Kernel/Misc/GL52/data/cls.txt" 6558 6417815466806755546

#kc_listDispatch CertificateChecks.KernelMisc.GL52K.D basR bR 26

#kc_listDispatch CertificateChecks.KernelMisc.GL52K.D basN bN 81

public section

namespace CertificateChecks.KernelMisc.GL52K

open CFSG.KC.Misc.GLM CFSG.KC.Ord

@[expose] noncomputable def pR (i : Nat) : List (Nat × Nat) := [(D.repC.getD i 0, D.repC.getD i 0)]

@[expose] noncomputable def pZ : List (Nat × Nat) := [(D.tau2, D.tau2), (D.tauB, D.tauB)]

@[expose] noncomputable def pN (i j : Nat) : List (Nat × Nat) :=
  [(D.tau2, D.r0C.getD i 0), (D.tauB, D.r0C.getD j 0)]

@[expose] noncomputable def basOK (ps : List (Nat × Nat)) (L : List Nat) : Bool :=
  listBeq (elimK ps (25 * ps.length) 25).2 L

@[expose] noncomputable def repOK (i : Nat) : Bool :=
  andB (Nat.blt 0 (D.repO.getD i 0)) (andB (ordK (D.repC.getD i 0) (D.repO.getD i 0))
    (andB (Nat.beq (rankK (Nat.xor (D.repC.getD i 0) idK)) (D.repR.getD i 0))
      (Nat.beq (invK (D.repC.getD i 0)) (D.repV.getD i 0))))

@[expose] noncomputable def nOK (i j : Nat) : Bool :=
  andB (basOK (pN i j) (D.basN (9 * i + j)))
    (Nat.beq (unitCntK (D.basN (9 * i + j))) (D.nN.getD (9 * i + j) 0))

end CertificateChecks.KernelMisc.GL52K

end
