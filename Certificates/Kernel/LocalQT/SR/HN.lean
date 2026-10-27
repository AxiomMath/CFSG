module

public import CFSG.Certificates.Kernel.LocalQTSecSound
import Certificates.Kernel.LocalQT.Cmd
import all CFSG.Blueprint.NativeSporadic
meta import Certificates.Data.CFSGNative.SectionRank.HN
public import CFSG.Open.Defs

set_option maxRecDepth 100000

#lqt_sr_elem CFSG.KD.LQT.HN CFSG.SectionRank.Native.hnData 5 133
  CFSG.Blueprint.NativeSporadic.HNSeed1 CFSG.Blueprint.NativeSporadic.HNSeed2

public section

namespace CertificateChecks.KernelLocalQT

open CFSG.Blueprint CFSG.Open CFSG.KC.LQT

theorem hn_elem : ∃ E : Subgroup NativeSporadic.HN, IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 4 := by
  have h := elem_sound _ CFSG.KD.LQT.HN.lay_ok CFSG.KD.LQT.HN.decA CFSG.KD.LQT.HN.decB
    CFSG.KD.LQT.HN.one CFSG.KD.LQT.HN.steps CFSG.KD.LQT.HN.elem
  rw [← CFSG.KD.LQT.HN.LA_eq, ← CFSG.KD.LQT.HN.LB_eq] at h
  exact h

end CertificateChecks.KernelLocalQT

end
