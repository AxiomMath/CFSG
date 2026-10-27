module

public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Kernel.Sporadic.OddCore.LinesCmd
public import CFSG.Certificates.Kernel.Spor.DecLinesRead
public import CFSG.Sporadic.HNOddCore.DCheckInputs
meta import CFSG.Sporadic.HNOddCore.InvArrays
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.HND

open CFSG.Sporadic.HNOddCore.InvData

meta def f1L : Array (Array Nat) := linesOf f1Text
meta def f4L : Array (Array Nat) := linesOf f4Text
meta def f6L : Array (Array Nat) := linesOf f6Text

end CertificateChecks.KernelSpor.HND

#ks_chars CertificateChecks.KernelSpor.HNT.F1 CFSG.Sporadic.HNOddCore.InvData.f1Text
#ks_lines CertificateChecks.KernelSpor.HNT.F1 CertificateChecks.KernelSpor.HND.f1L
#ks_chars CertificateChecks.KernelSpor.HNT.F4 CFSG.Sporadic.HNOddCore.InvData.f4Text
#ks_lines CertificateChecks.KernelSpor.HNT.F4 CertificateChecks.KernelSpor.HND.f4L
#ks_chars CertificateChecks.KernelSpor.HNT.F6 CFSG.Sporadic.HNOddCore.InvData.f6Text
#ks_lines CertificateChecks.KernelSpor.HNT.F6 CertificateChecks.KernelSpor.HND.f6L
#ks_chars CertificateChecks.KernelSpor.HNT.O1 CFSG.Sporadic.HNOddCore.InvData.o1Text
#ks_lines CertificateChecks.KernelSpor.HNT.O1 CFSG.Sporadic.HNOddCore.InvData.o1Lists
#ks_chars CertificateChecks.KernelSpor.HNT.O6 CFSG.Sporadic.HNOddCore.InvData.o6Text
#ks_lines CertificateChecks.KernelSpor.HNT.O6 CFSG.Sporadic.HNOddCore.InvData.o6Lists
#ks_chars CertificateChecks.KernelSpor.HNT.S1 CFSG.Sporadic.HNOddCore.InvData.s1Text
#ks_lines CertificateChecks.KernelSpor.HNT.S1 CFSG.Sporadic.HNOddCore.InvData.s1Perms
#ks_chars CertificateChecks.KernelSpor.HNT.S4 CFSG.Sporadic.HNOddCore.InvData.s4Text
#ks_lines CertificateChecks.KernelSpor.HNT.S4 CFSG.Sporadic.HNOddCore.InvData.s4Perms
#ks_chars CertificateChecks.KernelSpor.HNT.CS CFSG.Sporadic.HNOddCore.InvData.cstrongText
#ks_lines CertificateChecks.KernelSpor.HNT.CS CFSG.Sporadic.HNOddCore.InvData.cstrongPerms
#ks_chars CertificateChecks.KernelSpor.HNT.QP CFSG.Sporadic.HNOddCore.InvData.qpermText
#ks_lines CertificateChecks.KernelSpor.HNT.QP CFSG.Sporadic.HNOddCore.InvData.qPerms
#ks_chars CertificateChecks.KernelSpor.HNT.PG CFSG.Sporadic.HNOddCore.InvData.pgenText
#ks_lines CertificateChecks.KernelSpor.HNT.PG CFSG.Sporadic.HNOddCore.InvData.pgenPerms
#ks_chars CertificateChecks.KernelSpor.HNT.PC CFSG.Sporadic.HNOddCore.InvData.pconjText
#ks_lines CertificateChecks.KernelSpor.HNT.PC CFSG.Sporadic.HNOddCore.InvData.pconjPerms

namespace CertificateChecks.KernelSpor.HND

open CFSG.Sporadic.HNOddCore CFSG.Sporadic.HNOddCore.InvData CFSG.Sporadic.HNOddCore.Native
open CFSG.KS.DecLines CFSG.YGroups.ModelNative

theorem natsAt_zero {s : String} (h : (linesOf s).size ≠ 0) : natsAt s 0 = (linesOf s)[0]! := by
  unfold natsAt
  unfold linesOf at h ⊢
  cases hd : dataLines s with
  | nil => simp [hd] at h
  | cons l ls => simp

theorem shape_of {L : List (List Nat)} {k m : Nat}
    (h : (L.length == k && L.all (fun a => a.length == m)) = true) :
    ((L.map List.toArray).toArray.size == k && allSize (L.map List.toArray).toArray m) = true := by
  simpa [allSize, List.all_toArray, Function.comp_def] using h

theorem f1_eq : linesOf f1Text = (HNT.F1.E.map List.toArray).toArray := by
  rw [HNT.F1.eq]; exact linesOf_of_chk HNT.F1.ok
theorem f4_eq : linesOf f4Text = (HNT.F4.E.map List.toArray).toArray := by
  rw [HNT.F4.eq]; exact linesOf_of_chk HNT.F4.ok
theorem f6_eq : linesOf f6Text = (HNT.F6.E.map List.toArray).toArray := by
  rw [HNT.F6.eq]; exact linesOf_of_chk HNT.F6.ok
theorem o1_eq : o1Lists = (HNT.O1.E.map List.toArray).toArray := by
  unfold o1Lists; rw [HNT.O1.eq]; exact linesOf_of_chk HNT.O1.ok
theorem o6_eq : o6Lists = (HNT.O6.E.map List.toArray).toArray := by
  unfold o6Lists; rw [HNT.O6.eq]; exact linesOf_of_chk HNT.O6.ok
theorem s1_eq : s1Perms = (HNT.S1.E.map List.toArray).toArray := by
  unfold s1Perms; rw [HNT.S1.eq]; exact linesOf_of_chk HNT.S1.ok
theorem s4_eq : s4Perms = (HNT.S4.E.map List.toArray).toArray := by
  unfold s4Perms; rw [HNT.S4.eq]; exact linesOf_of_chk HNT.S4.ok
theorem cs_eq : cstrongPerms = (HNT.CS.E.map List.toArray).toArray := by
  unfold cstrongPerms; rw [HNT.CS.eq]; exact linesOf_of_chk HNT.CS.ok
theorem qp_eq : qPerms = (HNT.QP.E.map List.toArray).toArray := by
  unfold qPerms; rw [HNT.QP.eq]; exact linesOf_of_chk HNT.QP.ok
theorem pg_eq : pgenPerms = (HNT.PG.E.map List.toArray).toArray := by
  unfold pgenPerms; rw [HNT.PG.eq]; exact linesOf_of_chk HNT.PG.ok
theorem pc_eq : pconjPerms = (HNT.PC.E.map List.toArray).toArray := by
  unfold pconjPerms; rw [HNT.PC.eq]; exact linesOf_of_chk HNT.PC.ok

theorem f1Arr_eq : f1Arr = (HNT.F1.E.map List.toArray).toArray[0]! := by
  rw [f1Arr, natsAt_zero (by rw [f1_eq]; decide +kernel), f1_eq]
theorem f4Arr_eq : f4Arr = (HNT.F4.E.map List.toArray).toArray[0]! := by
  rw [f4Arr, natsAt_zero (by rw [f4_eq]; decide +kernel), f4_eq]
theorem f6Arr_eq : f6Arr = (HNT.F6.E.map List.toArray).toArray[0]! := by
  rw [f6Arr, natsAt_zero (by rw [f6_eq]; decide +kernel), f6_eq]

theorem fixSizes : fixSizesOK = true := by
  unfold fixSizesOK
  rw [f1Arr_eq, f4Arr_eq, f6Arr_eq, o1_eq, o6_eq]
  decide +kernel

theorem s1_shape : (s1Perms.size == 9 && allSize s1Perms 1156) = true := by
  rw [s1_eq]; exact shape_of (by decide +kernel)
theorem s4_shape : (s4Perms.size == 11 && allSize s4Perms 800) = true := by
  rw [s4_eq]; exact shape_of (by decide +kernel)
theorem cs_shape : (cstrongPerms.size == 20 && allSize cstrongPerms 800) = true := by
  rw [cs_eq]; exact shape_of (by decide +kernel)
theorem qp_shape : (qPerms.size == 8 && allSize qPerms 800) = true := by
  rw [qp_eq]; exact shape_of (by decide +kernel)
theorem pg_shape : (pgenPerms.size == 14 && allSize pgenPerms 800) = true := by
  rw [pg_eq]; exact shape_of (by decide +kernel)
theorem pc_shape : (pconjPerms.size == 6 && allSize pconjPerms 256) = true := by
  rw [pc_eq]; exact shape_of (by decide +kernel)

end CertificateChecks.KernelSpor.HND

end
