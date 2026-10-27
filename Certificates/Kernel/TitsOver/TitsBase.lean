module

public import CFSG.Certificates.Kernel.TitsOver.Base
public import CFSG.LocalAnalysis.StandardType.TitsGeneratorsBase
public import CFSG.Sporadic.Schreier.PairChain
public import CFSG.Certificates.NativeSchreierArrays
public import Certificates.Kernel.MaxD2.TitsD.Data
public import Certificates.Certificate2264
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelTitsOver

open CFSG.KC.Enum CFSG.KS CFSG.KS.PEnum CFSG.KS.TitsOver
open CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Tits

@[expose] def titsBase : List Nat := [0, 1, 5, 6, 24, 12]

theorem titsD_baseFaithful : BaseFaithful titsD titsBase := by
  have h := baseFaithful_of_valid titsQD_valid
  rw [titsQD_original] at h
  have hb : titsQD.base.toList = finList 1755 titsDerivedBase :=
    CFSG.Certificates.RawSchreierDatum.ofArrays_base_toList (n := 1755) (hn := by norm_num)
      (S := titsDerivedArrs) (k := 2) (hk := by rw [titsDerivedArrs_size]; norm_num)
      (base := finList 1755 titsDerivedBase) (hb := by decide)
      (W := wordsArr 2 13 titsDerivedDerivations)
  rw [hb] at h
  exact h

theorem pts_ok : allN 6 (fun s => bAnd(Nat.beq (titsBase[s]!)
    (r32 CertificateChecks.KernelMaxD2.TitsD.PT s),
    Nat.blt (r32 CertificateChecks.KernelMaxD2.TitsD.PT s) 1755)) = true := by quickRfl

theorem baseOK_tits : BaseOK 1755 6 (r32 CertificateChecks.KernelMaxD2.TitsD.PT) titsBase := by
  have h := PK.allN_iff.1 pts_ok
  refine ⟨fun s hs => Nat.blt_eq.mp (band_e' (h s hs)).2, fun x hx => ?_⟩
  obtain ⟨s, hs, rfl⟩ := List.getElem_of_mem hx
  have hs' : s < 6 := hs
  refine ⟨s, hs', ?_⟩
  have := Nat.eq_of_beq_eq_true (band_e' (h s hs')).1
  rw [← this, getElem!_pos titsBase s hs]
where
  band_e' {a b : Bool} (h : Bool.rec (motive := fun _ => Bool) false b a = true) :
      a = true ∧ b = true := CFSG.KS.MaxD2.band_e h

end CertificateChecks.KernelTitsOver

end
