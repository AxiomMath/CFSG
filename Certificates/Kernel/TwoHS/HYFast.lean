module

public import Certificates.Kernel.TwoHS.HYOps
public import Certificates.Kernel.TwoHS.FastC

public section

namespace CFSG.KD.TwoHS

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.MulH CFSG.KD.TwoHS.FC
open CFSG.EvenSporadicStandard.TwoHS

@[expose] noncomputable def pcF (p q : Nat) : Nat := pcompC 11200 14 (mask 14) p q

theorem pc_F : pc = pcF := by
  funext p q
  exact (CFSG.KS.PK.pcompC_eq 11200 14 p q).symm

@[expose] noncomputable def WKF (wd : List Nat) : Nat := wfoldKC 11200 14 (mask 14) L wd idK

theorem WK_F : WK = WKF := by
  funext wd
  exact wfoldK_C 11200 14 L wd idK

@[expose] noncomputable def WKIF (wd : List Nat) : Nat := WKF wd.reverse

theorem WKI_F : WKI = WKIF := by
  funext wd
  show WK wd.reverse = WKF wd.reverse
  rw [WK_F]

@[expose] noncomputable def ULF (l : Nat) : Nat := WKF (harUW.getD (l - 1) [])

theorem UL_F : UL = ULF := by
  funext l
  show WK (harUW.getD (l - 1) []) = WKF (harUW.getD (l - 1) [])
  rw [WK_F]

@[expose] noncomputable def UKF (wd : List Nat) : Nat := wfoldKC 11200 14 (mask 14) ULF wd idK

theorem UK_F : UK = UKF := by
  funext wd
  show wfoldK 11200 14 (mask 14) UL wd idK = wfoldKC 11200 14 (mask 14) ULF wd idK
  rw [wfoldK_C, UL_F]

@[expose] noncomputable def EVKF (G GI : Fin 6 → Nat) (wd : List (Fin 6 × Bool)) : Nat :=
  wd.foldl (fun acc l => pcF acc (cond l.2 (G l.1) (GI l.1))) idK

theorem EVK_F : EVK = EVKF := by
  funext G GI wd
  unfold EVK EVKF
  rw [pc_F]

@[expose] noncomputable def pwF (p e : Nat) : Nat := ppwC 11200 14 p e

theorem pw_F : pw = pwF := by
  funext p e
  show CFSG.KC.PkPow.ppw 11200 14 p e = ppwC 11200 14 p e
  rw [ppw_fun_C]

@[expose] noncomputable def fxF (p : Nat) : Nat := nfixC 11200 14 p

theorem fx_F : fx = fxF := by
  funext p
  show CFSG.KC.PkPow.nfix 11200 14 p = nfixC 11200 14 p
  rw [nfix_fun_C]

theorem invEqK_F :
    invEqK 11200 14 (mask 14) (11200 * 14) = permOKC 11200 14 (mask 14) (11200 * 14) :=
  invEqK_fun_C 11200 14 (11200 * 14)

end CFSG.KD.TwoHS

end
