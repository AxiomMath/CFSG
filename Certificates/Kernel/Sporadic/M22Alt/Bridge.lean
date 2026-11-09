module

public import Certificates.Kernel.Sporadic.M22Alt.Check
public import CFSG.Certificates.Kernel.Spor.MCentProved
public import CFSG.Sporadic.Schreier.M22Data
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.SporSch.MathieuOCSound
public import CFSG.Sporadic.Schreier.M11Data
public import CFSG.Certificates.Kernel.SporSch.ChainKRepsQ

public section

namespace CertificateChecks.KernelSpor.M22Alt

open CFSG.Sporadic.Schreier CFSG.Certificates CFSG.Sporadic.Mathieu CFSG.Monster.B.Mathieu
open CFSG.Sporadic.Schreier.Native CFSG.KS CFSG.KS.MEnum CFSG.KS.M11

set_option maxRecDepth 100000

theorem tA_eq : tA = imageList m22gA := by decide

theorem tB_eq : tB = imageList m22gB := by decide

theorem W_eq : W = [[1], [2]] ++ m22Words.map (List.map shiftLabel) := by decide

theorem counts : (m22Certificate.check = true)
    ∧ (ordTest 22 2 (toTable m22gA) = true ∧ ordTest 22 4 (toTable m22gB) = true ∧
      pairTest 22 11 6 2 4 (toTable m22gA) (toTable m22gB) = true)
    ∧ ((orderTables m22Certificate 2).length = 1155 ∧
      (orderTables m22Certificate 4).length = 41580)
    ∧ (classOK 22 (pairTables m22gA m22gB) (pairTables m22gA⁻¹ m22gB⁻¹)
        (orderTables m22Certificate 2) 2000 = true ∧
      classTotal 22 (pairTables m22gA m22gB) (pairTables m22gA⁻¹ m22gB⁻¹)
        (orderTables m22Certificate 2) (orderTables m22Certificate 4) 2000 11 6 2 4 =
        1774080) := by
  have h := CFSG.KS.MCent.mCent_sound (gA := m22gA) (gB := m22gB) (words := m22Words)
    (hn := by decide) (bv := #v[0, 1, 2, 3, 4]) (hbs := by decide) (cap := 2000)
    (CB := m22CB) (RX := [0]) (d := C0) tA_eq tB_eq W_eq (by decide) rfl (by decide) base
    m22cent m22reps (by decide) (by decide) (by decide) (by decide)
    (Nat.eq_of_beq_eq_true m22rX)
    (fun _ pR => CFSG.KS.SporSch.MOC.datum_factsQ tA_eq tB_eq (by decide)
      ((CFSG.KS.SporSch.MOC.allC_iff _ CL).1 cls C0 (List.mem_singleton_self C0))
      (by decide +kernel) pR)
    (Nat.eq_of_beq_eq_true oA) (Nat.eq_of_beq_eq_true oB) pAB (by norm_num) (by norm_num)
    (by norm_num)
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  exact ⟨h1, ⟨h2, h3, h4⟩, ⟨h5.trans (by decide), h6.trans (by decide)⟩, h7,
    h8.trans (by decide)⟩

end CertificateChecks.KernelSpor.M22Alt

end
