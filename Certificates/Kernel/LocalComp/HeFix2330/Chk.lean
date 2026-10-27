module

public import Certificates.Kernel.LocalComp.HeFix2330.Data
public import Certificates.Kernel.LocalComp.HeFix
public import Certificates.Kernel.Sporadic.OddCore.HeL2
public import Certificates.Kernel.SporSch.HeT.B2114K
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeldFixTwoBCheckInputs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.HeFix2330

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.PEnum CFSG.KC.PermTool
open CFSG.ComponentClassification.GrSLit.HeldFix CertificateChecks.KernelLC.HeFix
open CertificateChecks.KernelSpor

@[expose] noncomputable def pc (p q : Nat) : Nat := pcomp 8330 14 (mask 14) p q

@[expose] noncomputable def QI (i : Nat) : Nat :=
  CFSG.KC.PermTool.wordTabK 8330 14 CertificateChecks.KernelSporSch.HeB14.C1I
    (hfQWords.getD i []).reverse

@[expose] noncomputable def H (w : List Nat) : Nat := CFSG.KC.PermTool.wordTabK 8330 14 PC1 w

@[expose] noncomputable def pc' (p q : Nat) : Nat := pcomp 42 6 (mask 6) p q

@[expose] noncomputable def pi' (p : Nat) : Nat := pinvS 42 6 (mask 6) p

@[expose] noncomputable def X (w : List Nat) : Nat := CFSG.KC.PermTool.wordTabK 42 6 HXE.G w

@[expose] noncomputable def CG (i : Nat) : Nat :=
  pc' (pc' (pc' (X (hfCommWords.getD (2 * i) [])) (X (hfCommWords.getD (2 * i + 1) [])))
    (pi' (X (hfCommWords.getD (2 * i) [])))) (pi' (X (hfCommWords.getD (2 * i + 1) [])))

theorem kQ : (allN 2 (fun i => permOK 8330 14 (mask 14) (8330 * 14) (H (hfQWords.getD i []))
      (QI i)) && allN 9 (fun j => cn (CertificateChecks.KernelSporSch.HeB14.C1I j)) &&
    Nat.beq (pc (pc (pc (H (hfQWords.getD 0 [])) (H (hfQWords.getD 1 [])))
      (QI 0)) (QI 1)) PT1) = true := by
  quickRfl

theorem kO : (allN 2 (fun i => Nat.beq (H (hfRep 7 (hfOrd7Words.getD i []))) (pidn 8330 14) &&
      !Nat.beq (H (hfOrd7Words.getD i [])) (pidn 8330 14)) &&
    allN 3 (fun i => Nat.beq (H (hfRep 3 (hfOrd3Words.getD i []))) (pidn 8330 14) &&
      !Nat.beq (H (hfOrd3Words.getD i [])) (pidn 8330 14))) = true := by
  quickRfl

theorem kC : allN 6 (fun i => permOK 42 6 (mask 6) (42 * 6) (X (hfCommWords.getD i []))
      (pi' (X (hfCommWords.getD i []))) &&
    Nat.beq (pc' (pi' (X (hfCommWords.getD i []))) (X (hfCommWords.getD i []))) (pidn 42 6)) =
      true := by
  quickRfl

theorem kG : (Nat.beq HCE.k 3 && Nat.beq HSE.k 2 && Nat.beq HTE.k 3 &&
    allN 3 (fun i => Nat.beq (HCE.G i) (CG i) && canonK 42 6 (mask 6) (42 * 6) (HCE.G i)) &&
    allN 2 (fun i => Nat.beq (HSE.G i) (X (hfOrd7Words.getD i [])) &&
      canonK 42 6 (mask 6) (42 * 6) (HSE.G i)) &&
    allN 3 (fun i => Nat.beq (HTE.G i) (X (hfOrd3Words.getD i [])) &&
      canonK 42 6 (mask 6) (42 * 6) (HTE.G i))) = true := by
  quickRfl

theorem kHd : (penumHdK (pidn 42 6) HCE.cnt 10752 HCE.T HCE.PL &&
    penumHdK (pidn 42 6) HSE.cnt 10752 HSE.T HSE.PL &&
    penumHdK (pidn 42 6) HTE.cnt 10752 HTE.T HTE.PL &&
    Nat.beq HCE.cnt 10752 && Nat.beq HSE.cnt 10752 && Nat.beq HTE.cnt 10752) = true := by
  quickRfl

theorem c_sl0 : penumSlK 42 6 (mask 6) (42 * 6) false HCE.G HCE.GI HCE.k HCE.cnt HCE.T HCE.PL
    HCE.POS HCE.SRT HCE.SRI 0 2688 = true := by quickRfl

theorem c_sl1 : penumSlK 42 6 (mask 6) (42 * 6) false HCE.G HCE.GI HCE.k HCE.cnt HCE.T HCE.PL
    HCE.POS HCE.SRT HCE.SRI 2688 2688 = true := by quickRfl

theorem c_sl2 : penumSlK 42 6 (mask 6) (42 * 6) false HCE.G HCE.GI HCE.k HCE.cnt HCE.T HCE.PL
    HCE.POS HCE.SRT HCE.SRI 5376 2688 = true := by quickRfl

theorem c_sl3 : penumSlK 42 6 (mask 6) (42 * 6) false HCE.G HCE.GI HCE.k HCE.cnt HCE.T HCE.PL
    HCE.POS HCE.SRT HCE.SRI 8064 2688 = true := by quickRfl

theorem s_sl0 : penumSlK 42 6 (mask 6) (42 * 6) false HSE.G HSE.GI HSE.k HSE.cnt HSE.T HSE.PL
    HSE.POS HSE.SRT HSE.SRI 0 2688 = true := by quickRfl

theorem s_sl1 : penumSlK 42 6 (mask 6) (42 * 6) false HSE.G HSE.GI HSE.k HSE.cnt HSE.T HSE.PL
    HSE.POS HSE.SRT HSE.SRI 2688 2688 = true := by quickRfl

theorem s_sl2 : penumSlK 42 6 (mask 6) (42 * 6) false HSE.G HSE.GI HSE.k HSE.cnt HSE.T HSE.PL
    HSE.POS HSE.SRT HSE.SRI 5376 2688 = true := by quickRfl

theorem s_sl3 : penumSlK 42 6 (mask 6) (42 * 6) false HSE.G HSE.GI HSE.k HSE.cnt HSE.T HSE.PL
    HSE.POS HSE.SRT HSE.SRI 8064 2688 = true := by quickRfl

theorem t_sl0 : penumSlK 42 6 (mask 6) (42 * 6) false HTE.G HTE.GI HTE.k HTE.cnt HTE.T HTE.PL
    HTE.POS HTE.SRT HTE.SRI 0 2688 = true := by quickRfl

theorem t_sl1 : penumSlK 42 6 (mask 6) (42 * 6) false HTE.G HTE.GI HTE.k HTE.cnt HTE.T HTE.PL
    HTE.POS HTE.SRT HTE.SRI 2688 2688 = true := by quickRfl

theorem t_sl2 : penumSlK 42 6 (mask 6) (42 * 6) false HTE.G HTE.GI HTE.k HTE.cnt HTE.T HTE.PL
    HTE.POS HTE.SRT HTE.SRI 5376 2688 = true := by quickRfl

theorem t_sl3 : penumSlK 42 6 (mask 6) (42 * 6) false HTE.G HTE.GI HTE.k HTE.cnt HTE.T HTE.PL
    HTE.POS HTE.SRT HTE.SRI 8064 2688 = true := by quickRfl

end CertificateChecks.KernelLC.HeFix2330

end
