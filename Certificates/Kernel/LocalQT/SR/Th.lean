module

public import CFSG.Certificates.Kernel.LocalQTSecSound
import Certificates.Kernel.LocalQT.Cmd
import all CFSG.Blueprint.NativeSporadic
meta import Certificates.Data.CFSGNative.SectionRank.Th
public import CFSG.Open.Defs

set_option maxRecDepth 100000

#lqt_sr_elem CFSG.KD.LQT.Th CFSG.SectionRank.Native.thData 2 248
  CFSG.Blueprint.NativeSporadic.ThSeed1 CFSG.Blueprint.NativeSporadic.ThSeed2

public section

namespace CertificateChecks.KernelLocalQT

open CFSG.Blueprint CFSG.Open CFSG.KC.LQT

theorem th_elem : ∃ E : Subgroup NativeSporadic.Th, IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 4 := by
  have h := elem_sound _ CFSG.KD.LQT.Th.lay_ok CFSG.KD.LQT.Th.decA CFSG.KD.LQT.Th.decB
    CFSG.KD.LQT.Th.one CFSG.KD.LQT.Th.steps CFSG.KD.LQT.Th.elem
  rw [← CFSG.KD.LQT.Th.LA_eq, ← CFSG.KD.LQT.Th.LB_eq] at h
  exact h

end CertificateChecks.KernelLocalQT

end
