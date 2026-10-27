module

public import CFSG.Certificates.Kernel.LocalQTSecSound
import Certificates.Kernel.LocalQT.Cmd
import all CFSG.Blueprint.NativeSporadic
meta import Certificates.Data.CFSGNative.SectionRank.ON
public import CFSG.Open.Defs

set_option maxRecDepth 100000

#lqt_sr_elem CFSG.KD.LQT.ON CFSG.SectionRank.Native.onanData 3 154
  CFSG.Blueprint.NativeSporadic.ONSeed1 CFSG.Blueprint.NativeSporadic.ONSeed2

public section

namespace CertificateChecks.KernelLocalQT

open CFSG.Blueprint CFSG.Open CFSG.KC.LQT

theorem on_elem : ∃ E : Subgroup NativeSporadic.ON, IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 4 := by
  have h := elem_sound _ CFSG.KD.LQT.ON.lay_ok CFSG.KD.LQT.ON.decA CFSG.KD.LQT.ON.decB
    CFSG.KD.LQT.ON.one CFSG.KD.LQT.ON.steps CFSG.KD.LQT.ON.elem
  rw [← CFSG.KD.LQT.ON.LA_eq, ← CFSG.KD.LQT.ON.LB_eq] at h
  exact h

end CertificateChecks.KernelLocalQT

end
