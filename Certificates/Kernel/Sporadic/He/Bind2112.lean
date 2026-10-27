module

public import Certificates.Kernel.Sporadic.He.Chain2112
public import Certificates.Kernel.Sporadic.He.Stab2110
public import CFSG.Certificates.Kernel.Spor.PresCard
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.BfsPinSound
public import CFSG.Certificates.Kernel.BfsPinUnpack
public import Mathlib

public section

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelSpor.HeGenT CFSG.Sporadic.HeldB.heGenHex

#kmisc_hexflat CertificateChecks.KernelSpor.HeGenT CFSG.Sporadic.HeldB.heGenHex 4 8330 14 2

namespace CertificateChecks.KernelSpor.He2112

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin CFSG.KS.Pres
open CFSG.Sporadic.HeldB CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
open CFSG.Sporadic.Bridge CFSG.Sporadic.Bridge.TwoGen TauCeti

theorem strongOK : allN 9 (fun j => Nat.beq (HeText.F j) (HeC.S j)) = true := by
  quickRfl

theorem genOK : allN 2 (fun k => Nat.beq (HeGenT.F k) (HeC.S k)) = true := by
  quickRfl

theorem perm : allN 9 (fun j => permOK 8330 14 (mask 14) (8330 * 14) (HeC.S j) (HeC.SI j)) =
    true := by
  quickRfl

theorem baseOK : allN 5 (fun t => Nat.beq heBase.toArray[t]! (pg 14 (mask 14) HeC.BP t)) = true := by
  quickRfl

theorem strong_eq (j : Nat) (hj : j < 9) : heStrongArrs[j]! = unpack 8330 14 (HeC.S j) := by
  rw [heStrongArrs, getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn,
    HeText.heStrong_eq hj, Nat.eq_of_beq_eq_true (allN_spec strongOK j hj)]

theorem gen_eq (k : Nat) (hk : k < 2) : heGenArrs[k]! = unpack 8330 14 (HeC.S k) := by
  have h := CFSG.KC.Misc.HexFlat.hexTable_sound HeGenT.all k hk
  rw [← HeGenT.eq] at h
  rw [heGenArrs, getElem!_pos _ k (by simpa using hk), Array.getElem_ofFn]
  change hexTable 4 8330 (8330 * k) heGenHex = _
  rw [h, Nat.eq_of_beq_eq_true (allN_spec genOK k hk)]

theorem binds : Binds 8330 14 HeC.S 9 5 HeC.BP heStrongArrs heBase.toArray := by
  refine ⟨by norm_num, by norm_num, by norm_num, by simp [heStrongArrs], strong_eq,
    by simp [heBase], fun t ht => Nat.eq_of_beq_eq_true (allN_spec baseOK t ht)⟩

theorem gens_eq : heGenArrs = heStrongArrs.extract 0 2 := by
  apply Array.ext (by simp [heGenArrs, heStrongArrs])
  intro k h1 h2
  have hk : k < 2 := by simpa [heGenArrs] using h1
  rw [← getElem!_pos heGenArrs k h1, gen_eq k hk, Array.getElem_extract,
    ← getElem!_pos heStrongArrs (0 + k) (by simp [heStrongArrs]; omega), Nat.zero_add,
    strong_eq k (by omega)]

theorem words_eq : heWords = CFSG.Sporadic.Schreier.Co3.Native.wordsArr 2 9 derivs := by
  decide

end CertificateChecks.KernelSpor.He2112

end
