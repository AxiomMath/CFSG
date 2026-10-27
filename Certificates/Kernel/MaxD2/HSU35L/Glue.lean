module

public import Certificates.Kernel.MaxD2.HSU35L.Checks
public import Certificates.Kernel.MaxD2.HSU.Glue
public import CFSG.Certificates.Kernel.BfsPinAlg
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelMaxD2.HSU35L

open CFSG.KC CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.MaxD2
open CertificateChecks.KernelMaxD2.HSU Certificates.ThreeFourTwoHSU35 CFSG.PSL3Four.Native

theorem labels_ok : labelsOK () = true := by decide +kernel

theorem label_lt {i : Nat} (hi : i < 50) : hsU35Labels[i]! < 100 := by
  have h := labels_ok
  simp only [labelsOK, Bool.and_eq_true, allBelow, List.all_eq_true, List.mem_range,
    decide_eq_true_eq] at h
  exact h.1.2 i hi

theorem tab {k : Nat} (hk : k < 6) : Certificates.MaxD2Perm.wT Certificates.HSU35.dataU
    (hsU35GenWords.getD k []) = unpack 100 7 (TK k) :=
  c_wT_u HSU.hypsH.toHypsC (allN_spec wq k hk)

theorem acts {k : Nat} (hk : k < 6) : actsOK k = true := by
  unfold actsOK
  simp only [tab hk, allBelow, List.all_eq_true, List.mem_range, beq_iff_eq]
  intro i hi
  rw [CFSG.KC.BfsPin.unpack_getElem!, if_pos (label_lt hi)]
  exact Nat.eq_of_beq_eq_true (allN_spec (allN_spec actK k hk) i hi)

theorem check : hsU35Check () = true := by
  unfold hsU35Check
  rw [Bool.and_eq_true]
  refine ⟨labels_ok, ?_⟩
  simp only [allBelow, List.all_eq_true, List.mem_range]
  exact fun k hk => acts hk

end CertificateChecks.KernelMaxD2.HSU35L

end
