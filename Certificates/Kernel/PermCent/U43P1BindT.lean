module

public import Certificates.Kernel.PermCent.U43P1Tab
public import Certificates.Kernel.PermCent.U43P1Img

set_option maxRecDepth 400000
set_option maxHeartbeats 0

public section

namespace CertificateChecks.KernelPermCent.U43P1

open CFSG.ComponentClassification.HarrisLit.P1.U43.Cover CFSG.KC.Enum CFSG.KS

theorem u43BindM :
    ((List.range 6).all fun k => ((List.range (tM1a.getD k []).length).all fun j =>
      (List.range 820).all fun i => Nat.beq (at10 (tM1aG k j) i)
        (u43Img ((tM1a.getD k []).getD j (0, false)).1
          ((tM1a.getD k []).getD j (0, false)).2 i)) &&
        Nat.beq (tM1aT k 0) (pidn 820 10)) = true := by
  decide +kernel

theorem u43BindI :
    ((List.range 4).all fun k => ((List.range (tIa.getD k []).length).all fun j =>
      (List.range 820).all fun i => Nat.beq (at10 (tIaG k j) i)
        (u43Img ((tIa.getD k []).getD j (0, false)).1
          ((tIa.getD k []).getD j (0, false)).2 i)) &&
        Nat.beq (tIaT k 0) (pidn 820 10)) = true := by
  decide +kernel

theorem bindsT :
    (((List.range 6).all fun k => gensOK (tM1a.getD k []) (tM1aG k) &&
        Nat.beq (tM1aT k 0) (pidn 820 10)) &&
      ((List.range 4).all fun k => gensOK (tIa.getD k []) (tIaG k) &&
        Nat.beq (tIaT k 0) (pidn 820 10))) = true ∧
    TM0.N = 16 ∧ TM1.N = 32 ∧ TM2.N = 32 ∧ TM3.N = 32 ∧ TM4.N = 32 ∧ TM5.N = 32 ∧
    TI0.N = 16 ∧ TI1.N = 32 ∧ TI2.N = 32 ∧ TI3.N = 32 ∧
    TM0.ng = 3 ∧ TM1.ng = 4 ∧ TM2.ng = 4 ∧ TM3.ng = 3 ∧ TM4.ng = 4 ∧ TM5.ng = 3 ∧
    TI0.ng = 2 ∧ TI1.ng = 3 ∧ TI2.ng = 3 ∧ TI3.ng = 3 := by
  simp only [u43_gensOK]
  refine ⟨?_, ?_⟩
  · rw [Bool.and_eq_true]
    exact ⟨u43BindM, u43BindI⟩
  · decide +kernel

end CertificateChecks.KernelPermCent.U43P1

end
