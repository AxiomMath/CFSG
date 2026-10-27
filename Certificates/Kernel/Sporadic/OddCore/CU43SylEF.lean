module

public import Certificates.Kernel.Sporadic.OddCore.CU43SylF
public import Certificates.Kernel.Sporadic.OddCore.CU43SylE
public import Certificates.Kernel.Multipliers.U43BFacts

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.CU43SylE

open CFSG.EvenSporadicStandard.M24Std.CU43 CFSG.Sporadic.SmallOddCore
open CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Th.Native
open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH CFSG.KC.BfsPin
open CertificateChecks.KernelSpor.CU43Syl CertificateChecks.KernelU43B

theorem invs : ∀ j < 5, invEqK 820 10 (mask 10) (820 * 10) (CU43S.GI j) (CU43SI j) = true ∧
    canonK 820 10 (mask 10) (820 * 10) (CU43SI j) = true := by
  intro j hj
  have h := (bAnd_iff _ _).1 (allN_spec inv_ok j hj)
  exact ⟨h.2, h.1⟩

theorem s_tabsL : TabsOK 820 10 5 CU43S.GI sylTabs.toList.toArray := by
  rw [Array.toArray_toList]
  exact s_tabs

theorem gen_mem {x : Table} (hx : x ∈ sylTabs) :
    ∃ j < 5, x = tabT (unpack 820 10 (CU43S.GI j)) ∧
      canonK 820 10 (mask 10) (820 * 10) (CU43S.GI j) = true :=
  TabsOK_list s_tabsL (Array.mem_toList_iff.2 hx)

theorem inP_unpack {X : Nat} (hc : canonK 820 10 (mask 10) (820 * 10) X = true)
    (h : inPK X = true) : inP (unpack 820 10 X) = true := by
  unfold inP CFSG.EvenSporadicStandard.M24Std.CU43.levels baseArr
  rw [KernelU43B.base_eq]
  exact siftK_sound KernelU43B.binds KernelU43B.perm C.hl rfl (range_of_canonK hc) h

theorem perm_ok : sylPermCheck = true := by
  unfold sylPermCheck
  rw [Array.all_eq_true']
  intro x hx
  obtain ⟨j, hj, rfl, hc⟩ := gen_mem hx
  obtain ⟨h1, h2⟩ := invs j hj
  rw [Bool.and_eq_true, invT_unpack (lt_of_canonK h2) h1]
  exact ⟨permOK_unpack hc h1, invOK_unpack hc h2 h1⟩

theorem inP_all : sylInPCheck = true := by
  unfold sylInPCheck
  rw [Array.all_eq_true']
  intro x hx
  obtain ⟨j, hj, rfl, hc⟩ := gen_mem hx
  rw [natArr_tabT hc]
  exact inP_unpack hc (allN_spec inP_ok j hj)

theorem s_cl : ∀ c < CU43S.cnt * (5 + 5), findPtK CU43S.cnt CU43S.T
    (prodQK 820 10 (mask 10) (5 + 5) CU43S.T (bothK 5 CU43S.GI CU43SI)) CU43Cl c = true :=
  fun c hc => slK_spec sCl c (Nat.zero_le _) (by change c < Nat.mul CU43S.cnt 10; omega)
    (by change c < Nat.mul CU43S.cnt 10; omega)

theorem enum_ok : sylEnumCheck = true := by
  have h := enumOK_of (gs := sylTabs.toList) (cap := sylCap) (m := 128) CU43Syl.base.1
    (fun j hj => (gen hj).2) s_tabsL invs CU43Syl.base.2.2.2.2.2 s_pe s_hs s_cl hcnt
  unfold CFSG.Sporadic.SmallOddCore.enumOK at h
  simp only [Array.toArray_toList, Bool.and_eq_true] at h
  unfold sylEnumCheck sylEnum
  simp only [Bool.and_eq_true]
  exact ⟨⟨⟨h.1.1.1.2, h.1.1.2⟩, h.1.2⟩, h.2⟩

theorem facts26014 : sylPermCheck = true ∧ sylInPCheck = true ∧ sylEnumCheck = true :=
  ⟨perm_ok, inP_all, enum_ok⟩

end CertificateChecks.KernelSpor.CU43SylE

end
