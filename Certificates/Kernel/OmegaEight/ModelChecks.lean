module

public import Certificates.Data.Kernel.O8.ModelW
public import Certificates.Kernel.OmegaEight.ModelData
public import Certificates.Kernel.OmegaEight.CPChains
public import Certificates.Kernel.OmegaEight.AutChainAP
public import Certificates.Kernel.OmegaEight.AutChainOmP
public import Certificates.Kernel.OmegaEight.NatData
public import Certificates.Kernel.OmegaEight.OrthGens
public import Certificates.Kernel.OmegaEight.S0Data
public import Certificates.Kernel.LocalComp.Omega1Chain
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage1Q3Data
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelO8

open CFSG.KC.O8 CFSG.KLie.CT CFSG.KS CFSG.KS.Raw CFSG.EvenSmallLie
  CFSG.EvenSmallLie.OmegaEight.Stage1 CFSG.EvenSmallLie.OmegaEight.Stage1.Model
  CertificateChecks.KernelLC.W3185
open CFSG.KC.Enum (pidn permOK pg)

theorem pOP_0 : (pOrig .plus)[0]! = unpack 120 9 (PP.S 0) := by decide +kernel
theorem pOP_1 : (pOrig .plus)[1]! = unpack 120 9 (PP.S 1) := by decide +kernel
theorem pOP_2 : (pOrig .plus)[2]! = unpack 120 9 (PP.S 2) := by decide +kernel
theorem pOP_3 : (pOrig .plus)[3]! = unpack 120 9 (PP.S 3) := by decide +kernel
theorem pOP_4 : (pOrig .plus)[4]! = unpack 120 9 (PP.S 4) := by decide +kernel
theorem pOP_5 : (pOrig .plus)[5]! = unpack 120 9 (PP.S 5) := by decide +kernel
theorem pOP_6 : (pOrig .plus)[6]! = unpack 120 9 (PP.S 6) := by decide +kernel
theorem pOP_7 : (pOrig .plus)[7]! = unpack 120 9 (PP.S 7) := by decide +kernel
theorem pOP_8 : (pOrig .plus)[8]! = unpack 120 9 (PP.S 8) := by decide +kernel
theorem pOP_9 : (pOrig .plus)[9]! = unpack 120 9 (PP.S 9) := by decide +kernel
theorem pOP_10 : (pOrig .plus)[10]! = unpack 120 9 (PP.S 10) := by decide +kernel
theorem pOP_11 : (pOrig .plus)[11]! = unpack 120 9 (PP.S 11) := by decide +kernel

theorem pOP_bind : (pOrig .plus).size = 12 ∧
    ∀ j < 12, (pOrig .plus)[j]! = unpack 120 9 (PP.S j) := by
  refine ⟨rfl, fun j hj => ?_⟩
  interval_cases j
  exacts [pOP_0, pOP_1, pOP_2, pOP_3, pOP_4, pOP_5, pOP_6, pOP_7, pOP_8, pOP_9, pOP_10, pOP_11]

theorem pOM_0 : (pOrig .minus)[0]! = unpack 136 8 (PM.S 0) := by decide +kernel
theorem pOM_1 : (pOrig .minus)[1]! = unpack 136 8 (PM.S 1) := by decide +kernel
theorem pOM_2 : (pOrig .minus)[2]! = unpack 136 8 (PM.S 2) := by decide +kernel
theorem pOM_3 : (pOrig .minus)[3]! = unpack 136 8 (PM.S 3) := by decide +kernel
theorem pOM_4 : (pOrig .minus)[4]! = unpack 136 8 (PM.S 4) := by decide +kernel
theorem pOM_5 : (pOrig .minus)[5]! = unpack 136 8 (PM.S 5) := by decide +kernel
theorem pOM_6 : (pOrig .minus)[6]! = unpack 136 8 (PM.S 6) := by decide +kernel
theorem pOM_7 : (pOrig .minus)[7]! = unpack 136 8 (PM.S 7) := by decide +kernel
theorem pOM_8 : (pOrig .minus)[8]! = unpack 136 8 (PM.S 8) := by decide +kernel
theorem pOM_9 : (pOrig .minus)[9]! = unpack 136 8 (PM.S 9) := by decide +kernel
theorem pOM_10 : (pOrig .minus)[10]! = unpack 136 8 (PM.S 10) := by decide +kernel
theorem pOM_11 : (pOrig .minus)[11]! = unpack 136 8 (PM.S 11) := by decide +kernel

theorem pOM_bind : (pOrig .minus).size = 12 ∧
    ∀ j < 12, (pOrig .minus)[j]! = unpack 136 8 (PM.S j) := by
  refine ⟨rfl, fun j hj => ?_⟩
  interval_cases j
  exacts [pOM_0, pOM_1, pOM_2, pOM_3, pOM_4, pOM_5, pOM_6, pOM_7, pOM_8, pOM_9, pOM_10, pOM_11]

theorem permsPP : CFSG.KC.Enum.allN 20 (fun j => permOK 120 9 (mask 9) (120 * 9) (PP.S j) (PP.SI j)) =
    true := by quickRfl
theorem permsPM : CFSG.KC.Enum.allN 18 (fun j => permOK 136 8 (mask 8) (136 * 8) (PM.S j) (PM.SI j)) =
    true := by quickRfl
theorem permsUP : CFSG.KC.Enum.allN 12 (fun j => permOK 120 9 (mask 9) (120 * 9) (UP.S j) (UP.SI j)) =
    true := by quickRfl
theorem permsUM : CFSG.KC.Enum.allN 12 (fun j => permOK 136 8 (mask 8) (136 * 8) (UM.S j) (UM.SI j)) =
    true := by quickRfl

theorem kBasicP : basicOK 120 9 (fun y => psiK false NSP NIP 120 9 5665569 y) (fun i => PP.S (6 + i))
    (fun i => PP.SI (6 + i)) (fun k => UP.S (6 + k)) (fun k => UP.SI (6 + k)) GPlus UPlus
    ⟨Om1.LR, Om1.TRI, Om1.BP, 7⟩ ⟨PP.LR, PP.TRI, PP.BP, 6⟩ ⟨UP.LR, UP.TRI, UP.BP, 5⟩ = true := by
  quickRfl

theorem kBasicM : basicOK 136 8 (fun y => psiK true NSM NIM 136 8 4552225 y) (fun i => PM.S (6 + i))
    (fun i => PM.SI (6 + i)) (fun k => UM.S (6 + k)) (fun k => UM.SI (6 + k)) GMinus UMinus
    ⟨LMn.LR, LMn.TRI, LMn.BP, 7⟩ ⟨PM.LR, PM.TRI, PM.BP, 6⟩ ⟨UM.LR, UM.TRI, UM.BP, 3⟩ = true := by
  quickRfl

theorem kOSetP : oSetOK 120 9 (fun y => psiK false NSP NIP 120 9 5665569 y)
    ⟨Om1.LR, Om1.TRI, Om1.BP, 7⟩ PP.BP 6 135 MdTP MdTIP 135 = true := by
  quickRfl

theorem kOSetM : oSetOK 136 8 (fun y => psiK true NSM NIM 136 8 4552225 y)
    ⟨LMn.LR, LMn.TRI, LMn.BP, 7⟩ PM.BP 6 119 MdTM MdTIM 119 = true := by
  quickRfl

theorem kR3P :
    r3OK 120 9 (fun y => psiK false NSP NIP 120 9 5665569 y) UP.S 12 MdTP MdTIP 135 = true := by
  quickRfl

theorem kR3Perm : allN 135 (fun i => permOK 120 9 (mask 9) (120 * 9) (perAt 120 9 MdTP i)
    (perAt 120 9 MdTIP i)) = true := by
  quickRfl

theorem kSizeP : s5SizeOK MdCLSP MdNCP MdSZP = true := by quickRfl

theorem kSizeM : s5SizeOK MdCLSM MdNCM MdSZM = true := by quickRfl

theorem kRepP : s5RepOK MdCLSP MdREPSP MdNCP = true := by quickRfl

theorem kRepM : s5RepOK MdCLSM MdREPSM MdNCM = true := by quickRfl

theorem kClsP : allN 4096 (fun i => orB (Nat.beq (clsAt MdCLSP i) 0)
    (notB (Nat.beq (Nat.land (clsAt MdCLSP i) 127) 0))) = true := by
  quickRfl

theorem kClsM : allN 4096 (fun i => orB (Nat.beq (clsAt MdCLSM i) 0)
    (notB (Nat.beq (Nat.land (clsAt MdCLSM i) 127) 0))) = true := by
  quickRfl

theorem kNCP : MdNCP = 43 := by decide +kernel

theorem kNCM : MdNCM = 39 := by decide +kernel

theorem kPsiCanP : Nat.shiftRight (psiK false NSP NIP 120 9 5665569 1) (120 * 9) = 0 := by
  decide +kernel

theorem kPsiCanM : Nat.shiftRight (psiK true NSM NIM 136 8 4552225 1) (136 * 8) = 0 := by
  decide +kernel

@[expose] noncomputable def TGP (j : Nat) : Nat :=
  nIf(Nat.beq j 0, psiK false NSP NIP 120 9 5665569 1,
    nIf(Nat.beq j 1, psiK false NSP NIP 120 9 5665569 2, nIf(Nat.beq j 2, UP.S 9,
      nIf(Nat.beq j 3, psiK false NSP NIP 120 9 5665569 4, nIf(Nat.beq j 4, UP.S 10, UP.S 11)))))

theorem kLettersQ3 : allN 6 (fun j => andB (lettersK 17 (uWordsPlus.getD j []))
    (lettersK 17 (qWordsPlus.getD j []))) = true := by
  quickRfl

theorem kQ3 : q3OK 120 9 (fun k => UP.S (6 + k)) UP.S 12 ⟨PP.LR, PP.TRI, PP.BP, 6⟩ MdF MdFI 315
    MdFA MdFB (AP.S 8) (AP.SI 8) (fun k => wordC 360 9 OmP.S OmP.SI (uWordsPlus.getD k []))
    ⟨UP.LR, UP.TRI, UP.BP, 5⟩ (fun j => wordC 360 9 OmP.S OmP.SI (qWordsPlus.getD j []))
    TGP = true := by
  quickRfl

theorem flagA_bind : ∀ z < 120, flagA.getD z false = bit MdFA z := by decide +kernel

theorem flagB_bind : ∀ z < 120, flagB.getD z false = bit MdFB z := by decide +kernel

theorem kG8Can : Nat.shiftRight (AP.S 8) 3240 = 0 := by decide +kernel

theorem kUPRange : allN 12 (fun s => allN 120 fun z => Nat.blt (pg 9 (mask 9) (UP.S s) z) 120) =
    true := by
  quickRfl

theorem kSigRange : allN 6 (fun k => allN 120 fun z => Nat.blt (pg 9 (mask 9)
    (pc 360 9 (pc 360 9 (pc 360 9 (AP.S 8) (AP.S 8))
      (wordC 360 9 OmP.S OmP.SI (uWordsPlus.getD k []))) (pc 360 9 (AP.SI 8) (AP.SI 8))) z) 120) =
    true := by
  quickRfl

end CertificateChecks.KernelO8

end
