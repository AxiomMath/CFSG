
module

public import CFSG.Certificates.Kernel.SporSch.Co2MSound
public import CFSG.Certificates.Kernel.Spor.BindList
public import Certificates.Kernel.Sporadic.Co2.FVecs
public import CFSG.Sporadic.Co2Schreier.Arrays
public meta import CFSG.Sporadic.Co2Schreier.Arrays
public meta import CFSG.Sporadic.Co2Cert.FaithfulCheckInputs
meta import Certificates.Kernel.Misc.Perm.HexCmd
import CFSG.Certificates.Kernel.Common.Harness
public meta import CFSG.Certificates.InvariantMerge
public import CFSG.Certificates.Kernel.Spor.RawSound
public import CFSG.Certificates.NativeSchreierCard
import Certificates.Kernel.Misc.Perm.HexCmd

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.Co2M

open CFSG.Sporadic.Co2Cert CFSG.Sporadic.SmallF2.Native

meta def vecsArr : Array (Array Nat) := #[co2PackedVecs]

meta def seedRows : Array (Array Nat) :=
  #[transposeRows 22 co2RowsA, transposeRows 22 co2RowsB,
    transposeRows 22 (powRows 22 co2RowsB 4)]

end CertificateChecks.KernelSporSch.Co2M

#kmisc_packarrs CertificateChecks.KernelSporSch.Co2M.PV CertificateChecks.KernelSporSch.Co2M.vecsArr 22
#kmisc_packarrs CertificateChecks.KernelSporSch.Co2M.SR CertificateChecks.KernelSporSch.Co2M.seedRows 22
#kmisc_packarrs CertificateChecks.KernelSporSch.Co2M.AP CFSG.Sporadic.Co2Schreier.aArrs 12

namespace CertificateChecks.KernelSporSch.Co2M

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Co2M CFSG.KS.MatRep CFSG.RankThree.Native.F2
open CFSG.Sporadic.Co2Schreier CFSG.Sporadic.Co2Cert CertificateChecks.KernelSpor.Co2Faith

@[expose] noncomputable def aT : List (ℕ × ℕ) := [(SR 0, SR 0), (SR 1, SR 2)]

theorem vecs_ok : bindListK 2300 22 (PV 0) PL = true := by quickRfl

theorem aP_ok : allN 2 (fun k =>
    bindListK 2300 12 (AP k) (co2Rec.chain.generators.getD k [])) = true := by quickRfl

theorem seeds_ok : (bindK (PV 0) (AP 0) (SR 0) (SR 0) && bindK (PV 0) (AP 1) (SR 1) (SR 2)) =
    true := by quickRfl

theorem V_eq : co2PackedVecs = unpack 2300 22 (PV 0) := by
  rw [packed_eq]
  exact toArray_eq_of_bindListK vecs_ok

theorem V_size : co2PackedVecs.size = 2300 := size_ok

theorem V_get {i : ℕ} (hi : i < 2300) : co2PackedVecs[i]! = VG (PV 0) i := by
  rw [V_eq, CFSG.KC.Misc.PairCount.unpack_get hi]
  rfl

theorem good : Good 22 co2PackedVecs := by
  refine ⟨by norm_num, ?_, ?_⟩
  · rw [List.nodup_iff_injective_get]
    intro i j hij
    have hl : co2PackedVecs.toList.length = 2300 := by rw [Array.length_toList, V_size]
    have hi : i.val < 2300 := lt_of_lt_of_eq i.isLt hl
    have hj : j.val < 2300 := lt_of_lt_of_eq j.isLt hl
    have e : co2PackedVecs[i.val]! = co2PackedVecs[j.val]! := by
      rw [getElem!_pos _ _ (by rw [V_size]; exact hi), getElem!_pos _ _ (by rw [V_size]; exact hj)]
      simpa using hij
    exact Fin.ext ((packed_facts i hi).2.2 j hj e)
  · intro v hv
    obtain ⟨i, hi, rfl⟩ := Array.getElem_of_mem hv
    rw [← getElem!_pos _ i hi]
    exact (packed_facts i (by rwa [V_size] at hi)).1

theorem aArrs_size : aArrs.size = 2 := by
  have h : lenK (co2Rec.chain.generators.map List.length) = 2 := by decide +kernel
  rw [lenK_eq, List.length_map] at h
  simp [aArrs, co2OrigArrs, CFSG.Monster.B.Mathieu.ChainRecord.origArrs, h]

theorem aArrs_get {k : ℕ} (hk : k < 2) : aArrs[k]! = unpack 2300 12 (AP k) := by
  have hl : co2Rec.chain.generators.length = 2 := by
    have h : lenK (co2Rec.chain.generators.map List.length) = 2 := by decide +kernel
    rwa [lenK_eq, List.length_map] at h
  have e : aArrs[k]! = (co2Rec.chain.generators.getD k []).toArray := by
    unfold aArrs co2OrigArrs CFSG.Monster.B.Mathieu.ChainRecord.origArrs
    rw [getElem!_pos _ k (by simp [hl]; omega)]
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [hl]; omega : k < _)]
  rw [e]
  exact toArray_eq_of_bindListK (allN_spec aP_ok k hk)

theorem aRep : RepT 22 co2PackedVecs aArrs aT := by
  have hs := seeds_ok
  rw [Bool.and_eq_true] at hs
  refine ⟨by rw [aArrs_size]; rfl, fun k hk => ?_⟩
  have hk2 : k < 2 := hk
  rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl
  · exact bindK_sound good V_size (fun i hi => V_get hi) (aArrs_get hk2) hs.1
  · exact bindK_sound good V_size (fun i hi => V_get hi) (aArrs_get hk2) hs.2

end CertificateChecks.KernelSporSch.Co2M

end
