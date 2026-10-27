module

public import CFSG.Certificates.Kernel.LocalQTSecSound
import Certificates.Kernel.LocalQT.Cmd
import all CFSG.Blueprint.NativeSporadic
meta import Certificates.Data.CFSGNative.SectionRank.Co2
public import CFSG.Open.Defs

set_option maxRecDepth 100000

#lqt_sr_elem CFSG.KD.LQT.Co2 CFSG.SectionRank.Native.co2Data 2 22
  CFSG.Blueprint.NativeSporadic.Co2Seed1 CFSG.Blueprint.NativeSporadic.Co2Seed2

public section

namespace CertificateChecks.KernelLocalQT

open CFSG.Blueprint CFSG.Open CFSG.KC.LQT

theorem co2_elem : ∃ E : Subgroup NativeSporadic.Co2, IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 4 := by
  have h := elem_sound _ CFSG.KD.LQT.Co2.lay_ok CFSG.KD.LQT.Co2.decA CFSG.KD.LQT.Co2.decB
    CFSG.KD.LQT.Co2.one CFSG.KD.LQT.Co2.steps CFSG.KD.LQT.Co2.elem
  rw [← CFSG.KD.LQT.Co2.LA_eq, ← CFSG.KD.LQT.Co2.LB_eq] at h
  exact h

end CertificateChecks.KernelLocalQT

end
