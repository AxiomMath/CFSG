module

public import Certificates.Kernel.Fi23P.Small
public import Certificates.Kernel.KDenseP.TwoPoint.FiImg
public import Certificates.Kernel.Fi23K.Letters
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CFSG.KD.Fi23P

open CFSG.KC.Enum CFSG.KC.Fi23K CFSG.KD.Fi23K CFSG.Monster.Existence.Fi23Sp8.Native

noncomputable abbrev WD (k : Nat) : List Int :=
  CFSG.KS.Words.decW (CertificateChecks.KernelKDenseP.TwoPoint.FIW.WC k)
    (CertificateChecks.KernelKDenseP.TwoPoint.FIW.WL k)

noncomputable abbrev PD (k : Nat) : List Int := (WD k).take (((WD k).length - 84) / 2)

set_option Elab.async false

theorem base_ok : allN 10 (fun k => allN 6 fun j =>
    Nat.beq (wv G ((WD k).map regZ) j) (tb G k j)) = true := by quickRfl

theorem pi_ok : allN 10 (fun k => Nat.beq (wv G ((PD k).map regZ) 0) (piL.getD k 0)) = true := by
  quickRfl

theorem conj_ok : (List.range 10).all (fun k => WD k == PD k ++ dPow ++ invWord (PD k) &&
    (PD k).all fun z => z == 1 || z == -1 || z == 2 || z == -2) = true := by quickRfl

end CFSG.KD.Fi23P

end
