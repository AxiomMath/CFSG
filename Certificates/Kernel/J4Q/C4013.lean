
module

public import Certificates.Kernel.J4Q.C4013Base

public import CFSG.Sporadic.J4.QT2LocX0KNative
public import Certificates.Kernel.J4Q.KOrbOk
public import Certificates.Kernel.J4Q.C4027I
public import Certificates.Kernel.J4Q.D4K
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ4Q

open CFSG.KC.J4Q CFSG.KD.J4Q CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.QT2A
  CFSG.Sporadic.J4.QT2

theorem kcomm_ok : chkKComm = true := by
  obtain ⟨-, hmap, hwf⟩ := kOrb_ok
  have h0 := x0Gen_enc (i := 0) (by decide)
  have hq : ∀ X ∈ kOrb.mats.toList,
      eqRows (mulRows X (x0GenRows[0]!)) (mulRows (x0GenRows[0]!) X) = commQ (encR X) := by
    intro X hX
    rw [eqRows_of (mul_enc hK ⟨hwf X hX, rfl⟩ h0) (mul_enc hK h0 ⟨hwf X hX, rfl⟩), commQ]
  have hf := filter_map_comm (q := commQ) (f := encR) _ hq
  rw [hmap, List.filter_map] at hf
  have hx : ((List.range 15360).filter (commQ ∘ CFSG.KD.KO.MSF)) = KCOMM := by
    rw [← eqLK_spec kcomm_chk]
    apply List.filter_congr
    intro k hk
    have h := kDer_spec (List.mem_range.1 hk)
    unfold kDerK at h
    exact xboolEq_spec h
  rw [hx] at hf
  have hl := congrArg List.length hf
  rw [List.length_map, List.length_map, kcomm_len] at hl
  unfold chkKComm
  rw [hl]
  rfl

theorem c4013 : chkKAll = true := by
  unfold chkKAll
  simp only [Bool.and_eq_true]
  exact ⟨⟨⟨kgens_ok, kOrb_ok.1⟩, kcomm_ok⟩, estab_ok⟩

end CertificateChecks.KernelJ4Q

end
