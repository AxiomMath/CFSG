module

public import Certificates.Kernel.EvenBN.Lists
public import Certificates.Data.Kernel.EvenBN.BaseTw
public import Certificates.Kernel.SporSch.Tits.GenAll5
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelEvenBN

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch CertificateChecks.KernelSpor
open Certificates.TitsAschbacherE32

@[expose] noncomputable def VP (i : Nat) : Nat :=
  pcomp 1755 11 (mask 11) (pcomp 1755 11 (mask 11) Pi (V i)) PiI

@[expose] noncomputable def PC (t0 t1 t2 t3 t4 : Nat) : Bool :=
  (!(fIdx.all fun i => baseComm TitsH.BP 5 (gptR t0 t1 t2 t3 t4) (pgR (V i))) ||
      FL.any fun f => eqPts 1755 11 (mask 11) f t0 t1 t2 t3 t4) &&
    !(fIdx.all fun i => baseTw TitsH.BP 5 (gptR t0 t1 t2 t3 t4) (pgR (VP i)) (pgR (V i)))

@[expose] noncomputable def QC : Nat → Nat → Nat → Nat → Nat → Nat → Bool :=
  survQ (fun t0 t1 t2 t3 t4 => !PC t0 t1 t2 t3 t4) 0

end CertificateChecks.KernelEvenBN

#kst_all5 CertificateChecks.KernelEvenBN.TitsCF 1755 11 10 8 CertificateChecks.KernelSpor.TitsH.LR
  CertificateChecks.KernelSpor.TitsH.TR CertificateChecks.KernelEvenBN.QC

namespace CertificateChecks.KernelEvenBN

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch CertificateChecks.KernelSpor
open Certificates.TitsAschbacherE32

theorem vpK : fIdx.all (fun i =>
    siftK 1755 11 (mask 11) (1755 * 11) (pidn 1755 11) TitsH.LR TitsH.TRI TitsH.BP 5 0 (V i) &&
    siftK 1755 11 (mask 11) (1755 * 11) (pidn 1755 11) TitsH.LR TitsH.TRI TitsH.BP 5 0 (VP i) &&
    canonK 1755 11 (mask 11) (1755 * 11) (VP i) &&
    Nat.beq (pcomp 1755 11 (mask 11) (VP i) Pi) (pcomp 1755 11 (mask 11) Pi (V i))) = true := by
  quickRfl

theorem piPI : permOK 1755 11 (mask 11) (1755 * 11) Pi PiI = true := by quickRfl

theorem negPiSift : (siftK 1755 11 (mask 11) (1755 * 11) (pidn 1755 11) TitsH.LR TitsH.TRI TitsH.BP 5 0
    Pi).not = true := by quickRfl

end CertificateChecks.KernelEvenBN

end
