
module

public import Certificates.Kernel.SporSch.Ly.BS18009
public import CFSG.RankThree.Native.LySeedCheckInputs

public section

namespace CertificateChecks.KernelSporSch.LyNe

open CFSG.KC.Enum CFSG.KS CFSG.KC.Ord CFSG.KS.SporSch.LyM CFSG.KD.OrdLy
open CFSG.RankThree.Native CFSG.Sporadic.He.Native CFSG.Sporadic.LySchreier.Native
open CertificateChecks.KernelSporSch.LyBS CertificateChecks.KernelSporSch.LyBSF

local notation "U" X:max => unpackL 111 12 1332 X

theorem idM_get {i j : Nat} (hi : i < 111) (hj : j < 111) :
    ((idM 111)[i]!)[j]! = if i = j then 1 else 0 := by
  unfold idM
  rw [ofFn_get! _ hi, ofFn_get! _ hj]

theorem lyNeId_eq (X : Array (Array Nat)) : lyNeId X = diffMod5 X (idM 111) := by
  unfold lyNeId diffMod5
  apply Bool.eq_iff_iff.2
  simp only [List.any_eq_true, List.mem_range]
  refine ⟨fun ⟨i, hi, j, hj, h⟩ => ⟨i, hi, j, hj, ?_⟩, fun ⟨i, hi, j, hj, h⟩ => ⟨i, hi, j, hj, ?_⟩⟩
  · rw [idM_get hi hj]
    by_cases e : i = j <;> simp_all
  · rw [idM_get hi hj] at h
    by_cases e : i = j <;> simp_all

theorem neId {X : Nat} (hX : vld X = true) : lyNeId (U X) = !Nat.beq X ONE := by
  rw [lyNeId_eq, idE, diffMod5_eq consts (hv hX) (hv vOne)]

theorem powB {X : Nat} (hX : vld X = true) (e : Nat) :
    (powM 5 111 (U X) e == idM 111) = Nat.beq (powR 5 12 1332 111 8 L H CM RM ONE X e) ONE := by
  rw [(powM_eq consts (hv hX) e).1, idE, beqE (powM_eq consts (hv hX) e).2 vOne]

end CertificateChecks.KernelSporSch.LyNe

end
