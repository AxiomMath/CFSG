
module

public import Certificates.Kernel.Sporadic.Fi22.F1ModelK
public import Certificates.Kernel.Sporadic.Fi22.C3150
public import Certificates.Kernel.Sporadic.Fi22.C3039
public import Certificates.Kernel.Sporadic.Fi22.E2067
public import CFSG.Certificates.Kernel.BfsPinAlg
public import CFSG.Monster.B.Fischer.Fi22GraphCheckInputs
public import CFSG.Monster.B.Fischer.Fi22OrderCheckInputs
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.NormNum

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.Fi22F1M

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin
open CFSG.Monster.B.Fischer CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
open CertificateChecks.KernelSpor CertificateChecks.KernelSpor.Fi22X

theorem bool_false {b : Bool} (h : bIf(b, false, true) = true) : b = false := by
  cases b
  · rfl
  · exact absurd h (by decide)

theorem ne_of_beq_false {a b : Nat} (h : Nat.beq a b = false) : a ≠ b := fun e => by
  rw [e, Nat.beq_refl] at h
  exact absurd h (by decide)

theorem idA_eq' : idA 3510 = unpack 3510 12 (pidn 3510 12) := idA_eq (by decide +kernel)

theorem sift_eq {G : Nat} (hG : cn G = true) :
    siftA 3510 (rawLevels 3510 fi22StrongArrs fi22BaseArr) fi22BaseArr 0 (unpack 3510 12 G) =
      siftP G :=
  siftK_eq bindsP permP Fi22PC.hl rfl (hi_of hG) (range_of_canonK hG)

theorem orig_eq {k : Nat} (hk : k < 2) : fi22OrigArrs[k]! = unpack 3510 12 (Fi22CGT.F k) := by
  rw [fi22OrigArrs, getElem!_pos _ k (by simpa using hk), Array.getElem_ofFn]
  exact Fi22G.gen_eq hk

theorem facts3037 : fi22GraphOuterHex.length = 3 * 3510 ∧
    isInvA 3510 fi22GraphOuterArr (invCand 3510 fi22GraphOuterArr) = true := by
  refine ⟨?_, Fi22E2067.isInv_of go_eq permG⟩
  rw [Fi22GOT.eq, String.length_ofList]
  exact lenG

theorem facts3154 : eqA 3510 fi22GraphOuterArr (idA 3510) = false ∧
    eqA 3510 (compA 3510 fi22GraphOuterArr fi22GraphOuterArr) (idA 3510) = true ∧
    siftA 3510 (rawLevels 3510 fi22StrongArrs fi22BaseArr) fi22BaseArr 0 fi22GraphOuterArr =
      false ∧
    (∀ k < 2, siftA 3510 (rawLevels 3510 fi22StrongArrs fi22BaseArr) fi22BaseArr 0
      (compA 3510 fi22GraphOuterArr (compA 3510 fi22OrigArrs[k]! fi22GraphOuterArr)) = true) ∧
    (∀ p < 3510, p ≠ 0 → ∃ k < 3, ((fi22OuterStrong3510 3)[k]!)[p]! ≠ p) := by
  refine ⟨?_, ?_, ?_, fun k hk => ?_, fun p hp hp0 => ?_⟩
  · rw [go_eq, idA_eq', eqA_unpack cnG cnId]
    exact bool_false neId
  · rw [go_eq, comp_eq cnG cnG, idA_eq']
    exact eqA_of (cn_c cnG cnG) cnId sqId
  · rw [go_eq, sift_eq cnG]
    exact bool_false sGO
  · have ca := allN_spec cnA k hk
    rw [go_eq, orig_eq hk, comp_eq ca cnG, comp_eq cnG (cn_c ca cnG), sift_eq (cn_c cnG (cn_c ca cnG))]
    exact allN_spec sConj k hk
  · have h := allN_spec moved p hp
    have hb : Nat.beq p 0 = false := Bool.eq_false_iff.2 fun e => hp0 (Nat.eq_of_beq_eq_true e)
    rw [hb] at h
    have e : ∀ k < 3, ((fi22OuterStrong3510 3)[k]!)[p]! = pg 12 (mask 12) (Fi22M3.MS k) p :=
      fun k hk => by rw [Fi22C3150.outM_eq (by omega), Orb.unpack_get hp]
    cases h0 : Nat.beq (pg 12 (mask 12) (Fi22M3.MS 0) p) p
    · exact ⟨0, by norm_num, by rw [e 0 (by norm_num)]; exact ne_of_beq_false h0⟩
    rw [h0] at h
    cases h1 : Nat.beq (pg 12 (mask 12) (Fi22M3.MS 1) p) p
    · exact ⟨1, by norm_num, by rw [e 1 (by norm_num)]; exact ne_of_beq_false h1⟩
    rw [h1] at h
    refine ⟨2, by norm_num, ?_⟩
    rw [e 2 (by norm_num)]
    exact ne_of_beq_false (by simpa using h)

end CertificateChecks.KernelSpor.Fi22F1M

end
