module

public import Certificates.Kernel.SmithEK.ChkD2

public section

namespace CertificateChecks.KernelSmithEK

open CFSG.SmithE CFSG.SmithE.K CFSG.F4.Native CFSG.Fischer CFSG.Fischer.Native CFSG.Sporadic.Th
  CFSG.Sporadic.Th.Native

attribute [local irreducible] CFSG.F4.Native.uPts CFSG.F4.Native.uPos tvTabs perpTab uaPts

theorem uaMem_pb {j q : Nat} (hj : j < 891) (hq : q < 693) :
    uaMem uaPts[j]! q = (pb.P.getD j 0).testBit q := by
  have h := chkUA_eq
  have e : chkUA () = (uaPts.size == 891 &&
      parAll 891 7 (fun i => uaPlaneOK (perpTab ()) tvTabs uaPts[i]!) &&
      uaHypOK (perpTab ()) tvTabs && uaDistinctOK uaPts && uaMaskOK uaPts) := rfl
  rw [e, Bool.and_eq_true] at h
  have hm := h.2
  unfold uaMaskOK at hm
  have h1 := (allIn_eq_true.1 ((allIn_eq_true.1 hm) j (Nat.zero_le _) hj)) q (Nat.zero_le _) hq
  rw [beq_iff_eq, maskArr_get hj] at h1
  rw [← h1, pb_get hj, testBit_ptBits, pts_length, uPts_eq]
  simp [hq, List.getElem!_toArray, List.getElem!_eq_getElem?_getD, List.getD_eq_getElem?_getD]

end CertificateChecks.KernelSmithEK
