module

public import CFSG.Sporadic.J4.QT2LocFiveNative
public import Certificates.Kernel.J4Q.QTBase
public import CFSG.Certificates.Kernel.J4Q.RepQT2B
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Sporadic.J4.QT2LocNative
public import CFSG.Sporadic.J4.QTRankWitNative

public section

namespace CertificateChecks.KernelJ4Q

open CFSG.KC.J4Q CFSG.KD.J4Q CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.QT2

theorem five_enc : WfA fiveRows ∧ encR fiveRows = wordJ c rm one [L0, L1, L2] [L0i, L1i, L2i] fiveWord :=
  enc_wordRows hK loc_gens loc_invs fiveWord

theorem fivePow_ok : chkFivePow = true := by
  unfold chkFivePow
  rw [eqRows_of (pow_enc hK five_enc 5) (id_enc hK)]
  quickRfl

theorem fiveMasks_ok : chkFiveMasks = true := by quickRfl

open CFSG CFSG.Sporadic CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT2 in
open CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT in
theorem c4004 : (chkFivePow = true)
    ∧ (chkFiveMasks = true) := ⟨fivePow_ok, fiveMasks_ok⟩

end CertificateChecks.KernelJ4Q

end
