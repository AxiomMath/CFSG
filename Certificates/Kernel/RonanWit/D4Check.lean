module

public import Certificates.Kernel.RonanWit.D4Data
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.ForallChunks
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelRonanWit.D4

open CFSG.KC.Wit3 CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.Misc.ArrEnum
open CFSG.KC.Misc.Clos (allR)

theorem permS : allN 2 (fun k => permB 2457 12 (GS k)) = true := by quickRfl

theorem wordsP : allN 4 (fun k => wordEqK 2457 12 (mask 12) (pidn 2457 12) GS
    (fun k => pinvS 2457 12 (mask 12) (GS k)) 2 (getW pws k) (PG k) &&
    lettersK 2 (getW pws k)) = true := by quickRfl

theorem wordsY : (wordEqK 2457 12 (mask 12) (pidn 2457 12) GS
    (fun k => pinvS 2457 12 (mask 12) (GS k)) 2 (getW yws 0) (YS 0) &&
    lettersK 2 (getW yws 0)) = true := by quickRfl

theorem head : headK 2457 12 4 81 PG PT = true := by quickRfl

@[expose] noncomputable def ptC (c : Nat) : Bool :=
  allR (27 * c) 27 (pointK 2457 12 4 81 PG PT (EF EP) PAR LAB)

@[expose] noncomputable def kyC (c : Nat) : Bool :=
  allR (27 * c) 27 (fun i => keyOK 2457 12 pps PT K i && ordOK 81 K SO SI i)

@[expose] noncomputable def wtC (c : Nat) : Bool :=
  allR (27 * c) 27 (witPtK 2457 12 81 1 PT PT YS W)

end CertificateChecks.KernelRonanWit.D4

#kc_each CertificateChecks.KernelRonanWit.D4.ptC 0 3
#kc_each CertificateChecks.KernelRonanWit.D4.kyC 0 3
#kc_each CertificateChecks.KernelRonanWit.D4.wtC 0 3

namespace CertificateChecks.KernelRonanWit.D4

#kc_forall_chunks ptS (fun c => ptC c = true) 3 CertificateChecks.KernelRonanWit.D4.ptC 1
#kc_forall_chunks kyS (fun c => kyC c = true) 3 CertificateChecks.KernelRonanWit.D4.kyC 1
#kc_forall_chunks wtS (fun c => wtC c = true) 3 CertificateChecks.KernelRonanWit.D4.wtC 1

end CertificateChecks.KernelRonanWit.D4

end
