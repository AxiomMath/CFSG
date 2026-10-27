module

public import Certificates.Data.Kernel.Misc.SylKey
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanM12CoverData
public import CFSG.Sporadic.Mathieu.M12
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo
public import CFSG.Sporadic.Schreier.ImagePairs
public import CFSG.Sporadic.Schreier.M12Data

set_option maxRecDepth 400000

#kc_repo #kc_json_gz CertificateChecks.KernelSporSch.M12Cover9681 "Certificates/Kernel/SporSch/data/m12cover9681.json.gz" 104469 7063124725130788003
  (NT : Nat) (NIT : Nat) (RT : Nat) (E5 : List (Nat × Nat)) (E11 : List (Nat × Nat)) (R5 : Nat)
  (R11 : Nat) (X5 : List (List Nat × Nat)) (X11 : List (List Nat × Nat)) (WN : List (List Nat))
  (WR : List (List Nat))

public section

namespace CertificateChecks.KernelSporSch.M12Cover9681

open CFSG.KC.SylKey CFSG.AGLEmbedding.KFactProofs.M12Cover CFSG.Sporadic.Mathieu

@[expose] def gA : Nat := 92532767328531

@[expose] def gB : Nat := 180734465348391

@[expose] def gBI : Nat := 82837192188216

theorem pinG : (Nat.beq (cd m12gA) gA && Nat.beq (cd m12gB) gB && Nat.beq (cd m12gB⁻¹) gBI) =
    true := by
  quickRfl

theorem pinN : pinB NT m12CoverNorm 0 = true := by quickRfl

theorem pinNI : pinB NIT (m12CoverNorm.map (·⁻¹)) 0 = true := by quickRfl

theorem pinR : pinB RT (m12CoverReps.map (·.1)) 0 = true := by quickRfl

theorem lens : (Nat.beq m12CoverNorm.length 54 && Nat.beq m12CoverReps.length 80 &&
    Nat.beq E5.length 2376 && Nat.beq E11.length 1728 && Nat.beq X5.length 40 &&
    Nat.beq X11.length 55 && Nat.beq WN.length 54 && Nat.beq WR.length 80 && Nat.blt R5 80 &&
    Nat.blt R11 80) = true := by
  quickRfl

theorem wn : wB gA gB gBI NT WN 0 = true := by quickRfl

theorem wr : wB gA gB gBI RT WR 0 = true := by quickRfl

theorem e5 : allE 5 NT NIT RT E5 0 = true := by quickRfl

theorem e11 : allE 11 NT NIT RT E11 0 = true := by quickRfl

theorem o5 : ordB 5 (lk RT R5) = true := by quickRfl

theorem o11 : ordB 11 (lk RT R11) = true := by quickRfl

theorem x5 : nrmB gA gB gBI (lk RT R5) X5 0 = true := by quickRfl

theorem x11 : nrmB gA gB gBI (lk RT R11) X11 0 = true := by quickRfl

end CertificateChecks.KernelSporSch.M12Cover9681

end
