module

public import Certificates.Kernel.Ly6117.Data
public import CFSG.Sporadic.Recognition.LyonsFinalCore107
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.StrLitToList

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLy6117

open CFSG.KD.Ly6117 CFSG.Sporadic.Recognition.LyonsSims.LyFinal CFSG.KC.StrLitToList

theorem allK_take_drop (R : List (List (Fin 6 × Bool))) (k : Nat) :
    allK G GI R = (allK G GI (R.take k) && allK G GI (R.drop k)) := by
  unfold allK
  rw [← List.all_append, List.take_append_drop]

theorem relCore_0 : allK G GI (Rcore107.take 45) = true := by
  simp only [Rcore107, core107Strings, List.map_cons, List.map_nil, parseWord, strLitToList]
  quickRfl

theorem relCore_1 : allK G GI ((Rcore107.drop 45).take 37) = true := by
  simp only [Rcore107, core107Strings, List.map_cons, List.map_nil, parseWord, strLitToList]
  quickRfl

theorem relCore_2 : allK G GI ((Rcore107.drop 45).drop 37) = true := by
  simp only [Rcore107, core107Strings, List.map_cons, List.map_nil, parseWord, strLitToList]
  quickRfl

theorem relCore : allK G GI Rcore107 = true := by
  rw [allK_take_drop Rcore107 45, allK_take_drop (Rcore107.drop 45) 37, relCore_0, relCore_1,
    relCore_2]
  rfl

end CertificateChecks.KernelLy6117

end
