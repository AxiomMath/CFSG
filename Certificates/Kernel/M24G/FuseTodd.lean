module

public import Certificates.Kernel.M24G.FuseToddChecks
public import Certificates.Kernel.M24G.KzeroChecks
public import CFSG.Certificates.Kernel.M24G.FuseToddSound

public section

namespace CFSG.KC.M24G.FuseC

open CFSG.KC.M24G CFSG.Quasithin.H13.AS91.M24G

theorem kzeroK0List_kL : Native.kzeroK0List () = KzeroD.kL :=
  kzeroK0List_eq KzeroC.kzeroSyl_ok KzeroC.kzeroK0_ok

theorem fuseTodd_parts :
    fuseCommLoopF (badMask (Native.octsS Native.baseSext)) (xorCloseM (fuseCommGensK KzeroD.kL)).2
      = true ∧
    fuseX0LoopF (fuseWordF (Native.fuseULetters ()) Native.fuseX0Word)
      (badMask (Native.octsS Native.baseSext)) KzeroD.kL = true ∧
    fusePiBLoopF (badMask (Native.octsS Native.baseSext)) = true ∧
    fusePiALoopF (badMask (Native.octsS Native.baseSext))
      (Native.fuseSigmaWords.map (fuseWordF (Native.fuseLetters ()))) = true := by
  have h := fuseTodd_okF
  unfold fuseToddF at h
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

theorem fuseCommCheck_ok : Native.fuseCommCheck () = true := by
  unfold Native.fuseCommCheck
  rw [fuseCommLoop_eq, fuseCommGens_eq, kzeroK0List_kL]
  exact fuseTodd_parts.1

theorem fuseDuadCheck_ok : Native.fuseDuadCheck () = true := by decide +kernel

theorem fuseX0Check_ok : Native.fuseX0Check () = true := by
  unfold Native.fuseX0Check Native.fuseX0Tab
  rw [fuseWord_fun, kzeroK0List_kL, fuseX0Loop_eq _ _ _ (by decide +kernel)]
  exact fuseTodd_parts.2.1

theorem fusePiBCheck_ok : Native.fusePiBCheck () = true := by
  unfold Native.fusePiBCheck
  rw [fusePiBLoop_eq]
  exact fuseTodd_parts.2.2.1

theorem fusePiACheck_ok : Native.fusePiACheck () = true := by
  unfold Native.fusePiACheck
  rw [fuseWord_fun, fusePiALoop_eq _ _ (by decide +kernel)]
  exact fuseTodd_parts.2.2.2

end CFSG.KC.M24G.FuseC
