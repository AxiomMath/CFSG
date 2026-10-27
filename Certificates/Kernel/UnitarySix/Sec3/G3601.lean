module

public import Certificates.Kernel.UnitarySix.Sec3.G3601Chk
public import Certificates.Kernel.UnitarySix.Sec3.Chains3601
public import Certificates.Kernel.UnitarySix.Sec3.G3600
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaNativeData

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelU6.Sec3

open CFSG.KC.U6Sec3 CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.Enum CFSG.Monster.B.Co2.Native
open CFSG.EvenSmallLie.UnitarySix.YamadaSec3 CFSG.RankThree.Native CFSG.KC.U6
open CFSG.Monster.B.Co2 (allLt_iff)

theorem eqA_wA {a b : List ℕ} (ha : ∀ k ∈ a, k < 18) (hb : ∀ k ∈ b, k < 18) :
    eqA 693 (wA a) (wA b) = Nat.beq (wK a) (wK b) := by
  rw [(wK_spec ha).1, (wK_spec hb).1, eq_unpack (wK_spec ha).2 (wK_spec hb).2]

theorem all_eqA {α : Type} {L : List α} {f g : α → List ℕ}
    (h18 : ∀ p ∈ L, (∀ k ∈ f p, k < 18) ∧ ∀ k ∈ g p, k < 18)
    (hk : (L.all fun p => Nat.beq (wK (f p)) (wK (g p))) = true) :
    (L.all fun p => eqA 693 (wA (f p)) (wA (g p))) = true := by
  refine List.all_eq_true.2 fun p hp => ?_
  rw [eqA_wA (h18 p hp).1 (h18 p hp).2]
  exact List.all_eq_true.1 hk p hp

theorem xId_k : xIdCheck = true :=
  all_eqA (L := xIds) (f := fun p => p.1) (g := fun p => p.2) (by decide +kernel) kXId

theorem commCheck_k {as bs : List (List ℕ)} (h18 : ∀ a ∈ as, ∀ b ∈ bs, ∀ k ∈ a ++ b, k < 18)
    (hk : (as.all fun a => bs.all fun b => Nat.beq (wK (a ++ b)) (wK (b ++ a))) = true) :
    commCheck as bs = true := by
  unfold commCheck
  refine List.all_eq_true.2 fun a ha => all_eqA (f := fun b => a ++ b) (g := fun b => b ++ a)
    (fun b hb => ⟨h18 a ha b hb, fun k hk' => h18 a ha b hb k (by simp at hk' ⊢; tauto)⟩)
    (List.all_eq_true.1 hk a ha)

theorem xComm_k : xCommCheck = true := by
  have hk := kXComm
  simp only [Bool.and_eq_true] at hk
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := hk
  unfold xCommCheck
  simp only [Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨commCheck_k (by decide +kernel) h1, commCheck_k (by decide +kernel) h2⟩, commCheck_k (by decide +kernel) h3⟩,
    commCheck_k (by decide +kernel) h4⟩, commCheck_k (by decide +kernel) h5⟩, commCheck_k (by decide +kernel) h6⟩,
    commCheck_k (by decide +kernel) h7⟩, commCheck_k (by decide +kernel) h8⟩

theorem prodCheck_k {f : List ℕ → List ℕ → List ℕ} {data : List (ℕ × List (List ℕ × List ℕ))}
    (h18 : ∀ p ∈ data, p.1 < 18 ∧ ∀ k ∈ prodWord f p.2, k < 18)
    (hk : (data.all fun p => Nat.beq (wK [p.1]) (wK (prodWord f p.2))) = true) :
    prodCheck f data = true := by
  unfold prodCheck
  exact all_eqA (L := data) (f := fun p => [p.1]) (g := fun p => prodWord f p.2)
    (fun p hp => ⟨fun k hk' => by rw [List.mem_singleton.1 hk']; exact (h18 p hp).1,
      (h18 p hp).2⟩) hk

theorem xWit_k : xWitCheck = true := by
  have hk := kXWit
  simp only [Bool.and_eq_true] at hk
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩ := hk
  unfold xWitCheck
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨prodCheck_k (by decide +kernel) h1, prodCheck_k (by decide +kernel) h2⟩,
    prodCheck_k (by decide +kernel) h3⟩, prodCheck_k (by decide +kernel) h4⟩, prodCheck_k (by decide +kernel) h5⟩,
    prodCheck_k (by decide +kernel) h6⟩, prodCheck_k (by decide +kernel) h7⟩, prodCheck_k (by decide +kernel) h8⟩,
    all_eqA (L := a3eData) (f := fun p => [p.1]) (g := fun p => cwW p.2.1 [4, 17] ++ p.2.2)
      (by decide +kernel) h9⟩

theorem xFix_k : xFixCheck = true := by
  have hk := kXF
  rw [Bool.and_eq_true] at hk
  unfold xFixCheck
  rw [Bool.and_eq_true]
  refine ⟨allLt_iff.2 fun p hp => ?_, List.all_eq_true.2 fun i hi => ?_⟩
  · rw [chA3_K.O_all]
    simp only [unpack_get hp]
    exact allN_spec hk.1 p hp
  · have hi' := List.mem_range.1 hi
    have h18 : ∀ k ∈ qF[i]!, k < 18 := by interval_cases i <;> decide
    have hf : fixF[i]! < 693 := by interval_cases i <;> decide
    rw [(wK_spec h18).1, unpack_get hf]
    exact List.all_eq_true.1 hk.2 i hi

theorem letterArrs_eq : ∀ k < 46,
    CFSG.EvenSmallLie.UnitarySix.letterArrs[k]! = unpack 693 10 (letK U.LT k) := by
  intro k hk
  have hs := letters_sound up_eq pos_eq tv_eq kLet k hk
  have hT := letterT_eq k
  rw [natAbs_succ_sub] at hT
  have e1 : CFSG.EvenSmallLie.UnitarySix.letterArrs[k]! =
      (CFSG.EvenSmallLie.UnitarySix.letterT k).map UInt32.toNat := by
    rw [CFSG.EvenSmallLie.UnitarySix.letterArrs, getElem!_pos _ k (by simpa using hk),
      Array.getElem_map, Array.getElem_range]
  rw [e1, hT]
  apply Array.ext (by simp [unpack, hs.1])
  intro p h1 h2
  have hp : p < 693 := by simpa [hs.1] using h1
  have := (hs.2.2 p hp).1
  unfold CFSG.Sporadic.Th.Native.ap at this
  rw [getElem!_pos _ p (by rw [hs.1]; exact hp)] at this
  simp only [Array.getElem_map, unpack, Array.getElem_ofFn]
  rw [this]
  unfold ap10 pg CFSG.KLie.CT.fget CFSG.KLie.CT.maskN CFSG.KLie.CT.pw2 mask
  have e : p.mul 10 = Nat.mul 10 p := Nat.mul_comm p 10
  rw [e]
  rfl

end CertificateChecks.KernelU6.Sec3
