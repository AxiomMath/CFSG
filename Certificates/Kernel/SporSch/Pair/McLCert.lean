
module

public import Certificates.Kernel.SporSch.Pair.McLCheck
public import Certificates.Kernel.SporSch.Pair.GenCertK
public import Certificates.Kernel.SporSch.GenPerms
public import Certificates.Kernel.SporSch.PairJ3.GenCert
public import CFSG.Sporadic.Schreier.PairMcLCertInputs
meta import CFSG.Sporadic.Schreier.PairMcLCertInputs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

meta def CertificateChecks.KernelSporSch.mclVA : Array (Array Nat) :=
  CFSG.Sporadic.Schreier.mclVectors.map List.toArray

#kss_perms CertificateChecks.KernelSporSch.PMcLVT 4 CertificateChecks.KernelSporSch.mclVA

#ks_chars CertificateChecks.KernelSporSch.PMcLV CFSG.Sporadic.Schreier.mclVectorsHex

#ks_chars CertificateChecks.KernelSporSch.PMcLSt CFSG.Sporadic.Schreier.mclStabText

#kss_pomdata CertificateChecks.KernelSporSch.PMcLSt CFSG.Sporadic.Schreier.mclStabData

namespace CertificateChecks.KernelSporSch.PMcLCert

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.SporSch
open CFSG.Sporadic.Schreier CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
open CertificateChecks.KernelSporSch

theorem vtab : hexTabK PMcLV.chars 1 21 4 275 PMcLVT = true := by quickRfl

theorem vlt : allN 275 (fun i => allN 21 (fun j => Nat.blt (pg 4 (mask 4) (PMcLVT i) j) 3)) =
    true := by quickRfl

theorem tok : tokK PMcLSt.chars (encOM PMcLSt.R) = true := by quickRfl

theorem stab : stabK 275 273 [1, 112, 162] [1, 3] PMcLSt.R = true := by quickRfl

theorem vget (i : Nat) (hi : i < 275) : mclVectors[i]! = (unpack 21 4 (PMcLVT i)).toList :=
  PairGen.vec_get PMcLV.eq vtab i hi

theorem facts : mclCertOK = true := by
  have hst : mclStabData = PMcLSt.R := PairGen.stab_eq PMcLSt.eq tok
  obtain ⟨h7, h8, h9, h10, h11, h12⟩ := PairGen.stab_checks stab
  have hS : mclStrongArrs.size = 13 := by simp [mclStrongArrs]
  have hV : mclVectors.size = 275 := PairGen.hexVectors_size _ _ _
  unfold mclCertOK mclCertOKWith
  rw [hst]
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨?_, PairGen.wfV_of vget vlt⟩, ?_⟩,
    PairGen.gens_ok hS PMcLCheck.arr_eq PMcLCheck.perm⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩
  · rw [hV]
    rfl
  · rw [hS]
    rfl

end CertificateChecks.KernelSporSch.PMcLCert

end
