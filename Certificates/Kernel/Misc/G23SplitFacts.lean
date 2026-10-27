module

public import Certificates.Kernel.Misc.G23F3Facts
public import Certificates.Kernel.Misc.G23SplitChecks
import CFSG.Certificates.Kernel.Spor.PK.MiscBase

public section

namespace CFSG.KD.Misc.G23F3

open CFSG.KS.Mat3 CFSG.KC.Misc.G23F3 CFSG.LieType.Multipliers.G23 CFSG.Sporadic.He.Native
open CFSG.CGT.PushingUpLit.CGT6.EmbModule

theorem spl_eq (hc : constsK = true) (w : List (Fin 4)) :
    rootProd w = ofM3 (mat3 14 196 (SK w)) := by
  rw [(SK_sound hc w).2]
  exact rootProd_eq w

theorem splitCheck_true : splitCheck = true := by
  have h := split_ok
  rw [CFSG.KS.PK.andB_eq, Bool.and_eq_true] at h
  obtain ⟨hc, hs⟩ := h
  obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18⟩ :=
    splitK_sound hc (SK_sound hc uW).1 (SK_sound hc vW).1 (SK_sound hc z0W).1
      (SK_sound hc a1W).1 (SK_sound hc a2W).1 (SK_sound hc cW).1 hs
  have e1 : entryOf splA1 0 5 = (mat3 14 196 (SK a1W) 0 5).val := by
    rw [splA1, spl_eq hc]
    exact ofM3_entry _ 0 5
  have e2 : entryOf splZ 0 12 = (mat3 14 196 (SK z0W) 0 12).val := by
    rw [splZ, spl_eq hc]
    exact ofM3_entry _ 0 12
  unfold splitCheck
  rw [e1, e2]
  simp only [splU, splV, splZ, splA1, splA2, splC, spl_eq hc, mulM3_eq, toM3_ofM3, idM3_eq]
  simp only [r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18,
    beq_self_eq_true, Bool.and_self]
  rfl

end CFSG.KD.Misc.G23F3

end
