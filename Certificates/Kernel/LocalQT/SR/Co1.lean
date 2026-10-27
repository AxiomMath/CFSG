module

public import CFSG.Certificates.Kernel.LocalQTSecSound
import Certificates.Kernel.LocalQT.Cmd
import all CFSG.Blueprint.NativeSporadic
meta import Certificates.Data.CFSGNative.SectionRank.Co1
public import CFSG.Open.Defs

set_option maxRecDepth 100000

#lqt_sr_elem CFSG.KD.LQT.Co1 CFSG.SectionRank.Native.co1Data 2 24
  CFSG.Blueprint.NativeSporadic.Co1Seed1 CFSG.Blueprint.NativeSporadic.Co1Seed2

public section

namespace CertificateChecks.KernelLocalQT

open CFSG.Blueprint CFSG.Open CFSG.KC.LQT

theorem co1_elem : ∃ E : Subgroup NativeSporadic.Co1, IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 4 := by
  have h := elem_sound _ CFSG.KD.LQT.Co1.lay_ok CFSG.KD.LQT.Co1.decA CFSG.KD.LQT.Co1.decB
    CFSG.KD.LQT.Co1.one CFSG.KD.LQT.Co1.steps CFSG.KD.LQT.Co1.elem
  rw [← CFSG.KD.LQT.Co1.LA_eq, ← CFSG.KD.LQT.Co1.LB_eq] at h
  exact h

end CertificateChecks.KernelLocalQT

end
