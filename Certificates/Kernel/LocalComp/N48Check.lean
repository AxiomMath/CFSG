module

public import Certificates.Kernel.LocalComp.HexaCheck
public import CFSG.Certificates.Kernel.N48KSound
meta import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4Q47Data
import CFSG.Certificates.Kernel.Common.Harness
import Certificates.Kernel.Sporadic.ON.Gen

public section

set_option maxRecDepth 400000

#lc_bfs CertificateChecks.KernelLC.N48 CFSG.ComponentClassification.AS81.Q47.q47NGens 64 7

namespace CertificateChecks.KernelLC.N48Check

open CFSG.KC.BfsPin CFSG.KC.HexaK CFSG.KC.N48K CFSG.KC.Enum CFSG.KS CFSG.KS.Raw
open CFSG.ComponentClassification.AS81.Q47 CFSG.ComponentClassification.AS81.N48
open CertificateChecks.KernelLC CertificateChecks.KernelLC.HexaCheck

theorem kBind : (Nat.beq q47NGens.toArray.size N48.ng &&
    allN N48.ng fun k => bindArrK q47NGens.toArray[k]! 64 7 (N48.G k)) = true := by quickRfl

theorem kPerm : gensPerm N48.ng N48.G = true := by quickRfl

@[expose] noncomputable def I : List Nat := invL 7 N48.N N48.T

theorem kLen : I.length = 50 := by
  decide +kernel

@[expose] noncomputable def rk (i : Nat) : Bool := rankRowK 7 I i

@[expose] noncomputable def pk (i : Nat) : Bool := pairRowK 7 I i

end CertificateChecks.KernelLC.N48Check

set_option Elab.async false

#kon_slices CertificateChecks.KernelLC.N48Check.rk 0 50
#kon_join CertificateChecks.KernelLC.N48Check.rkAll CertificateChecks.KernelLC.N48Check.rk 50
#kon_slices CertificateChecks.KernelLC.N48Check.pk 0 50
#kon_join CertificateChecks.KernelLC.N48Check.pkAll CertificateChecks.KernelLC.N48Check.pk 50

namespace CertificateChecks.KernelLC.N48Check

open CFSG.KC.BfsPin CFSG.KC.HexaK CFSG.KC.N48K CFSG.KC.Enum CFSG.KS CFSG.KS.Raw
open CFSG.ComponentClassification.AS81.Q47 CFSG.ComponentClassification.AS81.N48
open CertificateChecks.KernelLC CertificateChecks.KernelLC.HexaCheck

theorem n48Check_true : n48Check = true := by
  rw [n48Check_eq]
  have hL : (invL 7 N48.N N48.T).length = 50 := kLen
  exact n48K_sound (pin kBind kPerm N48.ok (by decide)) rfl (fun i hi => rkAll i (Nat.lt_of_lt_of_eq hi hL))
    (fun i hi => pkAll i (Nat.lt_of_lt_of_eq hi hL))

end CertificateChecks.KernelLC.N48Check

end
