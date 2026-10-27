module

public import CFSG.Certificates.Kernel.LocalQTSecSound
import Certificates.Kernel.LocalQT.Cmd
import all CFSG.Blueprint.NativeSporadic
meta import Certificates.Data.CFSGNative.SectionRank.Co3
public import CFSG.Open.Defs

set_option maxRecDepth 100000

#lqt_sr_elem CFSG.KD.LQT.Co3 CFSG.SectionRank.Native.co3Data 2 22
  CFSG.Blueprint.NativeSporadic.Co3Seed1 CFSG.Blueprint.NativeSporadic.Co3Seed2

public section

namespace CertificateChecks.KernelLocalQT

open CFSG.Blueprint CFSG.Open CFSG.KC.LQT

theorem co3_elem : ∃ E : Subgroup NativeSporadic.Co3, IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 4 := by
  have h := elem_sound _ CFSG.KD.LQT.Co3.lay_ok CFSG.KD.LQT.Co3.decA CFSG.KD.LQT.Co3.decB
    CFSG.KD.LQT.Co3.one CFSG.KD.LQT.Co3.steps CFSG.KD.LQT.Co3.elem
  rw [← CFSG.KD.LQT.Co3.LA_eq, ← CFSG.KD.LQT.Co3.LB_eq] at h
  exact h

end CertificateChecks.KernelLocalQT

end
