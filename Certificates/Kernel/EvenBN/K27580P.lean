module

public import Certificates.Kernel.EvenBN.K27580D
import CFSG.Certificates.Kernel.Common.Harness
meta import Certificates.Data.TitsAschbacherE32

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelEvenBN.E32

meta def sNJMeta27 : List (Array Nat) :=
  (Certificates.TitsAschbacherE32.sInvs ()).filter fun a => !Certificates.TitsAschbacherParrott.inJ a

meta def xkMeta27 (i : Nat) : List (Array Nat) :=
  Certificates.TitsAschbacherE32.xkSet (Certificates.TitsAschbacherE32.eArrs ())
    (Certificates.TitsAschbacherE32.fArrs ()) Certificates.TitsAschbacherE32.xkData[i]!

meta def xkMeta27_0 : List (Array Nat) := xkMeta27 0
meta def xkMeta27_1 : List (Array Nat) := xkMeta27 1
meta def xkMeta27_2 : List (Array Nat) := xkMeta27 2
meta def xkMeta27_3 : List (Array Nat) := xkMeta27 3
meta def xkMeta27_4 : List (Array Nat) := xkMeta27 4
meta def xkMeta27_5 : List (Array Nat) := xkMeta27 5
meta def xkMeta27_6 : List (Array Nat) := xkMeta27 6
meta def xkMeta27_7 : List (Array Nat) := xkMeta27 7

end CertificateChecks.KernelEvenBN.E32

#kst_plist CertificateChecks.KernelEvenBN.E32.NJLit27 11 CertificateChecks.KernelEvenBN.E32.sNJMeta27
#kst_plist CertificateChecks.KernelEvenBN.E32.XLit27_0 11 CertificateChecks.KernelEvenBN.E32.xkMeta27_0
#kst_plist CertificateChecks.KernelEvenBN.E32.XLit27_1 11 CertificateChecks.KernelEvenBN.E32.xkMeta27_1
#kst_plist CertificateChecks.KernelEvenBN.E32.XLit27_2 11 CertificateChecks.KernelEvenBN.E32.xkMeta27_2
#kst_plist CertificateChecks.KernelEvenBN.E32.XLit27_3 11 CertificateChecks.KernelEvenBN.E32.xkMeta27_3
#kst_plist CertificateChecks.KernelEvenBN.E32.XLit27_4 11 CertificateChecks.KernelEvenBN.E32.xkMeta27_4
#kst_plist CertificateChecks.KernelEvenBN.E32.XLit27_5 11 CertificateChecks.KernelEvenBN.E32.xkMeta27_5
#kst_plist CertificateChecks.KernelEvenBN.E32.XLit27_6 11 CertificateChecks.KernelEvenBN.E32.xkMeta27_6
#kst_plist CertificateChecks.KernelEvenBN.E32.XLit27_7 11 CertificateChecks.KernelEvenBN.E32.xkMeta27_7

namespace CertificateChecks.KernelEvenBN.E32

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch CertificateChecks.KernelSpor

theorem lK : SI.L.all (fun A => canonK 1755 11 (mask 11) (1755 * 11) A && sS A) = true := by
  quickRfl

@[expose] noncomputable def NJ27 : List Nat := NJLit27

@[expose] noncomputable def XL27 : List (List Nat) :=
  [XLit27_0, XLit27_1, XLit27_2, XLit27_3, XLit27_4, XLit27_5, XLit27_6, XLit27_7]

theorem njK27 : NJ27.all (fun B => !sJ B) = true := by quickRfl
theorem xlK27 : (XL == XL27) = true := by quickRfl

@[expose] noncomputable def WK27 : List Nat :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7,
   7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 2,
   2, 2, 2, 2, 2, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 0, 0, 0, 0, 0,
   0, 0, 0, 2, 2, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 4, 4, 4, 4, 4, 4, 4, 4, 5, 5, 5, 5, 5, 5, 5, 5, 5,
   5, 5, 5, 5, 5, 5, 5, 4, 4, 4, 4, 4, 4, 4, 4]

@[expose] noncomputable def pivT27 (A k : Nat) (om : List Nat) : Bool :=
  EL.any (Nat.beq A) || ((XL27.drop k).take 1).any fun xs => om.all fun B =>
    xs.any (Nat.beq B) || (NJ27.any (Nat.beq B) && sJ A)

@[expose] noncomputable def pivS27 (A k : Nat) : Bool := pivT27 A k (SI.L.filter (commP A))

theorem pivK_of_pivS27 (A k : Nat) (h : pivS27 A k = true) : pivK A = true := by
  unfold pivS27 pivT27 at h
  unfold pivK
  rw [beq_iff_eq.1 xlK27]
  simp only [Bool.or_eq_true] at h ⊢
  refine h.imp id fun h => ?_
  obtain ⟨xs, hx, h⟩ := List.any_eq_true.1 h
  refine List.any_eq_true.2 ⟨xs, List.mem_of_mem_drop (List.mem_of_mem_take hx),
    List.all_eq_true.2 fun B hB => ?_⟩
  obtain ⟨hBL, hc⟩ := List.mem_filter.1 hB
  simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hc
  have h2 := List.all_eq_true.1 h B (List.mem_filter.2 ⟨hBL, hc.1⟩)
  simp only [Bool.or_eq_true, Bool.and_eq_true] at h2
  rcases h2 with h2 | ⟨hN, hJ⟩
  · exact h2
  · obtain ⟨y, hy, hBy⟩ := List.any_eq_true.1 hN
    have hy' := List.all_eq_true.1 njK27 y hy
    rw [← Nat.eq_of_beq_eq_true hBy, Bool.not_eq_true'] at hy'
    rw [hJ, hy'] at hc
    simp at hc

theorem fstK27 : ((SI.L.zip WK27).map Prod.fst == SI.L) = true := by quickRfl

theorem pivSAll27 : (SI.L.zip WK27).all (fun p => pivS27 p.1 p.2) = true := by quickRfl

theorem pivAllK27 : SI.L.all pivK = true := by
  refine List.all_eq_true.2 fun A hA => ?_
  rw [← beq_iff_eq.1 fstK27] at hA
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hA
  exact pivK_of_pivS27 p.1 p.2 (List.all_eq_true.1 pivSAll27 p hp)

end CertificateChecks.KernelEvenBN.E32

end
