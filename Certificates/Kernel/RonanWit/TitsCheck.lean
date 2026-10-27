module

public import Certificates.Kernel.RonanWit.TitsData
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.ForallChunks
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelRonanWit.Tits

open CFSG.KC.Wit3 CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.Misc.ArrEnum
open CFSG.KC.Misc.Clos (allR)

theorem permS : allN 2 (fun k => permB 1755 11 (GS k)) = true := by quickRfl

theorem wordsP : allN 2 (fun k => wordEqK 1755 11 (mask 11) (pidn 1755 11) GS
    (fun k => pinvS 1755 11 (mask 11) (GS k)) 2 (getW pws k) (PG k) &&
    lettersK 2 (getW pws k)) = true := by quickRfl

theorem wordsY : (wordEqK 1755 11 (mask 11) (pidn 1755 11) GS
    (fun k => pinvS 1755 11 (mask 11) (GS k)) 2 (getW yws 0) (YS 0) &&
    lettersK 2 (getW yws 0)) = true := by quickRfl

theorem head : headK 1755 11 2 27 PG PT = true := by quickRfl

@[expose] noncomputable def ptC (c : Nat) : Bool :=
  allR (27 * c) 27 (pointK 1755 11 2 27 PG PT (EF EP) PAR LAB)

@[expose] noncomputable def kyC (c : Nat) : Bool :=
  allR (27 * c) 27 (fun i => keyOK 1755 11 pps PT K i && ordOK 27 K SO SI i)

@[expose] noncomputable def wtC (c : Nat) : Bool :=
  allR (27 * c) 27 (witPtK 1755 11 27 1 PT PT YS W)

end CertificateChecks.KernelRonanWit.Tits

#kc_each CertificateChecks.KernelRonanWit.Tits.ptC 0 1
#kc_each CertificateChecks.KernelRonanWit.Tits.kyC 0 1
#kc_each CertificateChecks.KernelRonanWit.Tits.wtC 0 1

namespace CertificateChecks.KernelRonanWit.Tits

#kc_forall_chunks ptS (fun c => ptC c = true) 1 CertificateChecks.KernelRonanWit.Tits.ptC 1
#kc_forall_chunks kyS (fun c => kyC c = true) 1 CertificateChecks.KernelRonanWit.Tits.kyC 1
#kc_forall_chunks wtS (fun c => wtC c = true) 1 CertificateChecks.KernelRonanWit.Tits.wtC 1

end CertificateChecks.KernelRonanWit.Tits

end
