module

public import Certificates.Kernel.J4Q.VcOk
import Certificates.Kernel.J4Q.VcA
import Certificates.Kernel.J4Q.VcN
import Certificates.Kernel.J4Q.C4011
import Certificates.Kernel.J4Q.VlE

public section

namespace CertificateChecks.KernelJ4Q

open CFSG.KC.J4Q CFSG.KD.J4Q CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT2

theorem vlK4011 : VlK4011 := ⟨vlj_all, CFSG.KD.J4Q.ETCA.all, seg_all, pair_all⟩

theorem ngK_ok : NgK :=
  ⟨ngMask_chk, ngB3_chk, CFSG.KD.J4Q.VA9C.all, CFSG.KD.J4Q.VB7C.all, CFSG.KD.J4Q.VXI.all⟩

theorem gaK_len (g : Nat) : (gaK g).length = 16 := by
  unfold gaK
  cases Nat.blt g 17
  · simp [grpK]
  · change (smapK _ (rangeK 16)).length = 16
    rw [smapK_eq, rangeK_eq, List.length_map, List.length_range]

theorem c4012 : vlAll.size = 149 ∧ (∀ g < 149, vlAll[g]!.size = 16) ∧
    (∀ g < 149, ∃ r ∈ vlRepIdx, ∃ c < 6720, vlConjEq r g c = true ∧
      eqRows (mulRows vlCx[c]! vlCxInv[c]!) (idRows ()) = true) ∧ chkNamed = true := by
  obtain ⟨hn, hrep⟩ := named_of vlK4011 il17_chk ngK_ok CFSG.KD.J4Q.VNM.all
  refine ⟨vlAll_size' vlK4011, fun g hg => ?_, fun g hg => ?_, hn⟩
  · have := congrArg List.length (vlAll_enc vlK4011 il17_chk hg).2
    rwa [List.length_map, Array.length_toList, gaK_len] at this
  · rw [hrep]
    exact cls_of vlK4011 il17_chk CFSG.KD.J4Q.VCA.all hg

end CertificateChecks.KernelJ4Q

end
