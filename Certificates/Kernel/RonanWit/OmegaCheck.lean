module

public import Certificates.Kernel.RonanWit.OmegaData
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.ForallChunks
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelRonanWit.Omega

open CFSG.KC.Wit3 CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.Misc.ArrEnum
open CFSG.KC.Misc.Clos (allR)

theorem permS : allN 10 (fun k => permB 360 9 (GS k)) = true := by quickRfl

theorem wordsP : allN 5 (fun k => wordEqK 360 9 (mask 9) (pidn 360 9) GS
    (fun k => pinvS 360 9 (mask 9) (GS k)) 10 (getW pws k) (PG k) &&
    lettersK 10 (getW pws k)) = true := by quickRfl

theorem wordsQ : allN 4 (fun k => wordEqK 360 9 (mask 9) (pidn 360 9) GS
    (fun k => pinvS 360 9 (mask 9) (GS k)) 10 (getW qws k) (QG k) &&
    lettersK 8 (getW qws k)) = true := by quickRfl

theorem wordsY : allN 2 (fun l => wordEqK 360 9 (mask 9) (pidn 360 9) GS
    (fun k => pinvS 360 9 (mask 9) (GS k)) 10 (getW yws l) (YS l) &&
    lettersK 8 (getW yws l)) = true := by quickRfl

theorem headP : headK 360 9 5 729 PG PT = true := by quickRfl
theorem headQ : headK 360 9 4 243 QG QT = true := by quickRfl

@[expose] noncomputable def ptC (c : Nat) : Bool :=
  allR (81 * c) 81 (pointK 360 9 5 729 PG PT (EF EP) PAR LAB)

@[expose] noncomputable def kyC (c : Nat) : Bool :=
  allR (81 * c) 81 (fun i => keyOK 360 9 pps PT K i && ordOK 729 K SO SI i)

@[expose] noncomputable def qptC (c : Nat) : Bool :=
  allR (81 * c) 81 (pointK 360 9 4 243 QG QT (EF QEP) QPAR QLAB)

@[expose] noncomputable def qkyC (c : Nat) : Bool :=
  allR (81 * c) 81 (fun i => keyOK 360 9 qps QT QK i && ordOK 243 QK QSO QSI i)

@[expose] noncomputable def wtC (c : Nat) : Bool :=
  allR (81 * c) 81 (witPtK 360 9 243 2 PT QT YS W)

end CertificateChecks.KernelRonanWit.Omega

#kc_each CertificateChecks.KernelRonanWit.Omega.ptC 0 9
#kc_each CertificateChecks.KernelRonanWit.Omega.kyC 0 9
#kc_each CertificateChecks.KernelRonanWit.Omega.qptC 0 3
#kc_each CertificateChecks.KernelRonanWit.Omega.qkyC 0 3
#kc_each CertificateChecks.KernelRonanWit.Omega.wtC 0 9

namespace CertificateChecks.KernelRonanWit.Omega

#kc_forall_chunks ptS (fun c => ptC c = true) 9 CertificateChecks.KernelRonanWit.Omega.ptC 1
#kc_forall_chunks kyS (fun c => kyC c = true) 9 CertificateChecks.KernelRonanWit.Omega.kyC 1
#kc_forall_chunks qptS (fun c => qptC c = true) 3 CertificateChecks.KernelRonanWit.Omega.qptC 1
#kc_forall_chunks qkyS (fun c => qkyC c = true) 3 CertificateChecks.KernelRonanWit.Omega.qkyC 1
#kc_forall_chunks wtS (fun c => wtC c = true) 9 CertificateChecks.KernelRonanWit.Omega.wtC 1

end CertificateChecks.KernelRonanWit.Omega

end
