module

public import Certificates.Kernel.SporSch.Pair.GenCertK
public import Certificates.Kernel.SporSch.GenPerms
public import Certificates.Kernel.SporSch.PairJ3.GenCert
public import Certificates.Kernel.Sporadic.RawGen
public import CFSG.Sporadic.Schreier.PairHSCertInputs
meta import CFSG.Sporadic.Schreier.PairHSCertInputs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

meta def CertificateChecks.KernelSporSch.hsVA : Array (Array Nat) :=
  CFSG.Sporadic.Schreier.hsVectors.map List.toArray

#kss_perms CertificateChecks.KernelSporSch.PHSVT 1 CertificateChecks.KernelSporSch.hsVA

#ks_chars CertificateChecks.KernelSporSch.PHSV CFSG.Sporadic.Schreier.hsVectorsHex

#kss_perms CertificateChecks.KernelSporSch.PHS 12 CFSG.Sporadic.Schreier.hsStrongArrs

#ks_chars CertificateChecks.KernelSporSch.PHSText CFSG.Sporadic.Schreier.hsStrongHex

#ks_chars CertificateChecks.KernelSporSch.PHSSt CFSG.Sporadic.Schreier.hsStabText

#kss_pomdata CertificateChecks.KernelSporSch.PHSSt CFSG.Sporadic.Schreier.hsStabData

namespace CertificateChecks.KernelSporSch.PHSCert

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.SporSch
open CFSG.Sporadic.Schreier CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
open CertificateChecks.KernelSporSch

theorem vtab : hexTabK PHSV.chars 1 20 1 3850 PHSVT = true := by quickRfl

theorem vlt : allN 3850 (fun i => allN 20 (fun j => Nat.blt (pg 1 (mask 1) (PHSVT i) j) 2)) =
    true := by quickRfl

theorem tab : hexTabK PHSText.chars 4 3850 12 8 PHS = true := by quickRfl

theorem perm : allN 8 (fun j => permOK 3850 12 (mask 12) (3850 * 12) (PHS j)
    (pinvS 3850 12 (mask 12) (PHS j))) = true := by quickRfl

theorem tok : tokK PHSSt.chars (encOM PHSSt.R) = true := by quickRfl

theorem stab : stabK 3850 3848 [1, 960, 160, 90, 192, 1440, 240, 360, 120, 240, 15, 32]
    [1, 3, 4, 6, 7, 8, 36, 41, 93, 128, 158] PHSSt.R = true := by quickRfl

theorem vget (i : Nat) (hi : i < 3850) : hsVectors[i]! = (unpack 20 1 (PHSVT i)).toList :=
  PairGen.vec_get PHSV.eq vtab i hi

theorem arr_eq (j : Nat) (hj : j < 8) : hsStrongArrs[j]! = unpack 3850 12 (PHS j) := by
  have h := hexTabK_sound tab j hj
  rw [← PHSText.eq] at h
  rw [hsStrongArrs, getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn]
  exact h

theorem facts : hsCertOK = true := by
  have hst : hsStabData = PHSSt.R := PairGen.stab_eq PHSSt.eq tok
  obtain ⟨h7, h8, h9, h10, h11, h12⟩ := PairGen.stab_checks stab
  have hS : hsStrongArrs.size = 8 := by simp [hsStrongArrs]
  have hV : hsVectors.size = 3850 := PairGen.hexVectors_size _ _ _
  unfold hsCertOK hsCertOKWith
  rw [hst]
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨?_, PairGen.wfV_of vget vlt⟩, ?_⟩, PairGen.gens_ok hS arr_eq perm⟩, h7⟩, h8⟩, h9⟩,
    h10⟩, h11⟩, h12⟩
  · rw [hV]
    rfl
  · rw [hS]
    rfl

end CertificateChecks.KernelSporSch.PHSCert

end
