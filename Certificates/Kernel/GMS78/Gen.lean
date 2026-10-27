module

public import CFSG.Certificates.Kernel.GMS78RuGen
public import Certificates.Data.GMS78RuNCoord

public section

namespace CertificateChecks.KernelGMS78

open CFSG.KC.GMS CFSG.GMS78Ru CFSG.GMS78RuSim CFSG.GMS78RuS CFSG.GMS78RuN CFSG.GMS78RuQ

theorem isoExt_eq (tab : List (List V3)) (c e : Fin 8) (bs : List V3) (done : List (V3 × V3)) :
    isoExt tab c e bs done = Gen.isoExt mulTab tab c e bs done := by
  induction bs generalizing done with
  | nil => rfl
  | cons b bs ih =>
    simp only [isoExt, Gen.isoExt, ih]
    rfl

theorem c1_eq : c1Check = Gen.c1Check mulTab := rfl
theorem c2_eq : c2Check = Gen.c2Check mulTab specialList := rfl
theorem c3_eq : c3Check = Gen.c3Check mulTab := by
  simp only [c3Check, Gen.c3Check, isoExt_eq]
  rfl
theorem q0_eq : q0Check = Gen.q0Check mulTab qTab steinData := rfl
theorem s0_eq : s0Check = Gen.s0Check steinData specialList := rfl
theorem s1_eq : s1Check = Gen.s1Check mulTab steinData := rfl

theorem sMaskN_eq (c n : Nat) : sMaskN c n = Gen.sMaskN sBasis c n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [sMaskN, Gen.sMaskN, ih]

theorem gamN_eq (c c' n : Nat) : gamN c c' n = Gen.gamN qTab sBasis c c' n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [gamN, Gen.gamN, ih, sMaskN_eq]; rfl

theorem dPartN_eq (d : Fin 8) (c n : Nat) : dPartN d c n = Gen.dPartN qTab sBasis d c n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [dPartN, Gen.dPartN, ih, gam, Gen.gam, gamN_eq]

theorem gamCol_eq : gamColCheck = Gen.gamColCheck qTab nBetaTab sBasis := by
  simp only [gamColCheck, Gen.gamColCheck, sMaskN_eq]
  rfl

theorem dPart_eq : dPartCheck = Gen.dPartCheck qTab nBetaTab nTwTab sBasis nCols nBasis dCodeTab := by
  simp only [dPartCheck, Gen.dPartCheck, dPart, Gen.dPart, dPartN_eq, sMask, Gen.sMask, sMaskN_eq]
  rfl

end CertificateChecks.KernelGMS78

end
