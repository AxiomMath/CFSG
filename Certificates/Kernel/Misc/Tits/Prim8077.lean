module

public import Certificates.Data.Kernel.Misc.TitsPrim
public import Certificates.Data.Kernel.Misc.TitsChain
public import CFSG.Certificates.Kernel.YModel.TextGenS
public import Certificates.Kernel.Sporadic.RawGenOrb
public import Certificates.Kernel.Misc.Tits.Outer8075
public import Certificates.Kernel.TitsW.Defs
public import CFSG.Quasithin.Recognition.CertDataTitsSimple
meta import CFSG.Quasithin.Recognition.CertDataTitsSimple
meta import CFSG.Sporadic.Schreier.TitsArrays
meta import Certificates.Data.CFSGNative.YGroups.ExactCheck
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

#ym_texts CertificateChecks.KernelMisc.TitsPCT CFSG.Quasithin.titsPairChainText 32 1
#ym_texts CertificateChecks.KernelMisc.TitsRtT CFSG.Quasithin.titsRootsText 32 1
#ks_chars CertificateChecks.KernelMisc.TitsTwC CFSG.Quasithin.titsTwText
#ks_chars CertificateChecks.KernelMisc.TitsHwC CFSG.Quasithin.titsHwText

public section

namespace CertificateChecks.KernelMisc.TitsPCT

open CFSG.KC.YModel CFSG.KC.TitsChain

@[expose] noncomputable def words : List (List Int) := linesWK (lget El) 32 F lines

end CertificateChecks.KernelMisc.TitsPCT

end

namespace CertificateChecks.KernelMisc.TitsPCT

open CFSG.Monster.B.Co2.Native

meta def abM : Array (Array Nat) :=
  let D := #[CFSG.Sporadic.Schreier.Tits.titsDerivedArrs[0]!,
    CFSG.Sporadic.Schreier.Tits.titsDerivedArrs[1]!]
  let ws := (CFSG.YGroups.ModelNative.textLines CFSG.Quasithin.titsAbWordsText).map
    CFSG.YGroups.ModelNative.parseInts
  #[wordA 1755 D (D.map (invCand 1755)) (ws.getD 0 []),
    wordA 1755 D (D.map (invCand 1755)) (ws.getD 1 [])]

meta def strongM : Array (Array Nat) :=
  (CFSG.YGroups.ModelNative.strongOf 1755 abM
    (CFSG.YGroups.ModelNative.chainWords CFSG.Quasithin.titsPairChainText)).1

meta def baseM : Array Nat := #[0, 3, 1, 5, 6, 12, 24]

end CertificateChecks.KernelMisc.TitsPCT

#ks_raworb CertificateChecks.KernelMisc.TitsPCh 1755 11 64 CertificateChecks.KernelMisc.TitsPCT.strongM
  CertificateChecks.KernelMisc.TitsPCT.baseM 2 CertificateChecks.KernelMisc.TitsPCT.words

public section

namespace CertificateChecks.KernelMisc.TitsPrim8077

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.YModel CFSG.KC.TitsChain CFSG.KC.TitsPrim
open CFSG.KC.TitsOuter CFSG.KC.LQT.Cov CertificateChecks.KernelTitsW CertificateChecks.KernelMisc

@[expose] noncomputable def abW : List (List Int) :=
  linesWK (CFSG.KC.YModel.lget TitsAbT.El) 32 TitsAbT.F TitsAbT.lines

@[expose] noncomputable def A : Nat := WD (abW.getD 0 [])

@[expose] noncomputable def B : Nat := WD (abW.getD 1 [])

@[expose] noncomputable def okP : Nat → List Int → List Int → Bool :=
  primOK 11 12 1755 5 0 TitsPCh.S TitsPCh.SI (labAt (TitsLbT.F 0)) (fieldAt 32 (TitsRtT.F 0))

theorem perms : allN 12 (fun j => permOK 1755 11 (mask 11) (1755 * 11) (TitsPCh.S j)
    (TitsPCh.SI j)) = true := by
  quickRfl

theorem letters : bAnd(lettersK 2 (abW.getD 0 []), lettersK 2 (abW.getD 1 [])) = true := by
  quickRfl

theorem sOK : bAnd(Nat.beq (TitsPCh.S 0) A, Nat.beq (TitsPCh.S 1) B) = true := by quickRfl

theorem walk : walkK 1755 okP ((linesK TitsTwC.chars).drop 1) ((linesK TitsHwC.chars).drop 1) 0 =
    true := by
  quickRfl

theorem cnt : ((List.range 5).map fun i =>
    ((List.range 1755).filter fun p => Nat.beq (labAt (TitsLbT.F 0) p % 5) i).length) =
    [1, 10, 80, 640, 1024] := by
  decide +kernel

theorem ordA : bAnd(Nat.beq (ppw A 2) pe, bIf(Nat.beq A pe, false, true)) = true := by quickRfl

theorem ordB : bAnd(Nat.beq (ppw B 3) pe, bIf(Nat.beq B pe, false, true)) = true := by quickRfl

theorem ordAB : bAnd(Nat.beq (ppw (pm A B) 13) pe, bIf(Nat.beq (pm A B) pe, false, true)) =
    true := by
  quickRfl

end CertificateChecks.KernelMisc.TitsPrim8077

end
