module

public import Certificates.Kernel.SporSch.Ly.PermA
public import Certificates.Kernel.SporSch.Ly.PermB
public import Certificates.Kernel.SporSch.Ly.PermC
public import Certificates.Kernel.SporSch.Ly.PermD
public import Certificates.Kernel.SporSch.Ly.Perm8a
public import Certificates.Kernel.SporSch.Ly.Perm9a
public import Certificates.Kernel.SporSch.Ly.Perm10a
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Basic

public section

namespace CertificateChecks.KernelSporSch.LyPerm

open CFSG.Sporadic.LySchreier CFSG.Sporadic.LySchreier.Native

theorem facts : ∀ a b c d : Fin 11,
    (∀ j : Fin 4, ∀ x, qCand a b c d (arrFun (qImgArr[j.val]!) x) =
      arrFun (qImgArr[j.val]!) (qCand a b c d x)) →
    (∀ x y, qCand a b c d x = qCand a b c d y → x = y) →
    ∃ m : Fin 12, ∀ x, qCand a b c d x = arrFun (qNaturalCentralizer[m.val]!) x := by
  intro a
  fin_cases a
  · exact q0
  · exact q1
  · exact q2
  · exact q3
  · exact q4
  · exact q5
  · exact q6
  · exact q7
  · refine qstmt_of fun b => ?_
    fin_cases b
    exacts [r8_0, r8_1, r8_2, r8_3, r8_4, r8_5, r8_6, r8_7, r8_8, r8_9, r8_10]
  · refine qstmt_of fun b => ?_
    fin_cases b
    exacts [r9_0, r9_1, r9_2, r9_3, r9_4, r9_5, r9_6, r9_7, r9_8, r9_9, r9_10]
  · refine qstmt_of fun b => ?_
    fin_cases b
    exacts [r10_0, r10_1, r10_2, r10_3, r10_4, r10_5, r10_6, r10_7, r10_8, r10_9, r10_10]

end CertificateChecks.KernelSporSch.LyPerm

end
