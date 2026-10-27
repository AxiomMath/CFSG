module

public import Certificates.Kernel.SporSch.Ly.FiveLanesData
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.RankThree.Native.LyFiveArrays

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.LyFL

open CFSG.KC.Enum CFSG.KS CertificateChecks.KernelSporSch.LyBS CFSG.RankThree.Native CFSG.KD.OrdLy

@[expose] noncomputable def chkVL (i : Fin 4) : Bool :=
  Nat.beq (pw (V i.val) 5) ONE && Nat.beq (mul D.XX (V i.val)) (mul (V i.val) D.XX)

@[expose] noncomputable def chkCommL (i j : Fin 4) : Bool :=
  Nat.beq (mul (mul (mul (V i.val) (V j.val)) (pw (V i.val) 4)) (pw (V j.val) 4))
    (pw D.XX (lyFiveOmega i j).val)

@[expose] noncomputable def chkConjL (i : Fin 4) : Bool :=
  Nat.beq (mul D.AA (V i.val)) (mul (nfL (lyFiveAlpha i).val fun j => (lyFiveAbar j i).val) D.AA) &&
    Nat.beq (mul D.BB (V i.val)) (mul (nfL (lyFiveBeta i).val fun j => (lyFiveBbar j i).val) D.BB)

theorem sA25 : Nat.beq (pw D.AA 25) ONE = true := by quickRfl
theorem sX : (!Nat.beq D.XX ONE) = true := by quickRfl
theorem sB8 : Nat.beq (pw D.BB 8) ONE = true := by quickRfl
theorem sB4 : (!Nat.beq (pw D.BB 4) ONE) = true := by quickRfl
theorem sBX : Nat.beq (mul D.BB D.XX) (mul (pw D.XX 2) D.BB) = true := by quickRfl
theorem sV : (List.finRange 4).all chkVL = true := by quickRfl
theorem sComm : (List.finRange 4).all (fun i => (List.finRange 4).all (chkCommL i)) = true := by
  quickRfl
theorem sConj : (List.finRange 4).all chkConjL = true := by quickRfl

end CertificateChecks.KernelSporSch.LyFL

end
