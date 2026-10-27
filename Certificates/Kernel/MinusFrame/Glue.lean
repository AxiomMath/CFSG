module

public import Certificates.Kernel.MinusFrame.Checks
public import Certificates.Kernel.MinusEnum.Pin
public import CFSG.Certificates.Kernel.PermPinKSound
import CFSG.Certificates.Kernel.BfsPinUnpack
import CFSG.Certificates.Kernel.Spor.PackWord

public section

namespace CertificateChecks.KernelMinusFrame

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.PermPinK
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.RankThree.Native
open CFSG.OddTranspositions.PartThree CFSG.OddTranspositions.PartThree.MinusFrame
open CertificateChecks.KernelMinusEnum

theorem bindX : tArr () = unpack 65 7 (XT 0) ∧ xArr = unpack 65 7 (XT 1) ∧ t0Gens.size = 3 ∧
    ∀ k < 3, t0Gens[k]! = unpack 65 7 (XT (k + 2)) := by
  have h := kBindX
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  exact ⟨unpack_eq_of_bindArrK h1, unpack_eq_of_bindArrK h2, Nat.eq_of_beq_eq_true h3,
    fun k hk => unpack_eq_of_bindArrK (allN_spec h4 k hk)⟩

theorem canonX {k : Nat} (hk : k < 5) : canonK 65 7 (mask 7) (65 * 7) (XT k) = true :=
  allN_spec kCanonX k hk

theorem canonT' {i : Nat} (hi : i < 15600) : canonK 65 7 (mask 7) (65 * 7) (ME.T i) = true :=
  canonT i (by rw [nums.2]; exact hi)

theorem ptsList :
    (minusEnum ()).pts.toList = (List.range 15600).map fun i => unpack 65 7 (ME.T i) := by
  rw [minusEnum_pts]
  exact (pts_toList (N := ME.N) fun i => unpack 65 7 (ME.T i)).trans (by rw [nums.2])

theorem mem_E {x : Nat} (hx : canonK 65 7 (mask 7) (65 * 7) x = true)
    (hm : memK 15600 ME.T x = true) :
    (minusEnum ()).pts.toList.any (eqA 65 (unpack 65 7 x)) = true := by
  obtain ⟨j, hj, rfl⟩ := memK_spec hm
  rw [ptsList, List.any_eq_true]
  refine ⟨unpack 65 7 (ME.T j), List.mem_map.2 ⟨j, List.mem_range.2 hj, rfl⟩, ?_⟩
  rw [eqA_unpack hx hx, Nat.beq_refl]

theorem t0Sub : t0SubCheck (minusEnum ()) = true := by
  unfold t0SubCheck
  rw [List.all_eq_true]
  intro k hk
  rw [List.mem_range, bindX.2.2.1] at hk
  rw [bindX.2.2.2 k hk]
  exact mem_E (canonX (by omega)) (allN_spec kMemX (k + 1) (by omega))

theorem xMem : (minusEnum ()).pts.toList.any (eqA 65 xArr) = true := by
  rw [bindX.2.1]
  exact mem_E (canonX (by omega)) (allN_spec kMemX 0 (by omega))

theorem cent_lt : ∀ p ∈ centArr.toList, p < 65 := by decide

theorem cent_list : (List.finRange 15).map (fun i : Fin 15 => centArr[(i : ℕ)]!) = centArr.toList := by
  decide

theorem finRange_all (P : Nat) :
    ((List.finRange 15).all fun i : Fin 15 =>
      (unpack 65 7 P)[centArr[(i : ℕ)]!]! == centArr[(i : ℕ)]!) =
      centArr.toList.all (fun p => (unpack 65 7 P)[p]! == p) := by
  rw [← cent_list, List.all_map]
  rfl

theorem canonI : canonK 65 7 (mask 7) (65 * 7) (pidn 65 7) = true := by
  rw [← Nat.eq_of_beq_eq_true kT0]
  exact canonT' (by omega)

theorem stab : MinusFrame.stabCheck (minusEnum ()) = true := by
  unfold MinusFrame.stabCheck
  dsimp only
  rw [allLt_iff, minusEnum_pts, Array.size_ofFn, nums.2, bindX.1]
  intro k hk
  rw [getElem!_pos _ k (by rw [Array.size_ofFn]; exact hk), Array.getElem_ofFn]
  have hc := canonT' hk
  change (!((List.finRange 15).all fun i : Fin 15 =>
      (unpack 65 7 (ME.T k))[centArr[(i : ℕ)]!]! == centArr[(i : ℕ)]!) ||
    eqA 65 (unpack 65 7 (ME.T k)) (idA 65) || eqA 65 (unpack 65 7 (ME.T k)) (unpack 65 7 (XT 0))) =
      true
  rw [finRange_all, ← fixK_eq cent_lt, idA_eq kSz, eqA_unpack hc canonI,
    eqA_unpack hc (canonX (by omega))]
  rcases stabK_spec kStab k hk with h | h | h
  · rw [h]
    rfl
  · rw [h, Nat.beq_refl]
    simp
  · rw [h, Nat.beq_refl]
    simp

@[expose] noncomputable def cfilt : List Nat := (List.range 15600).filter fun j =>
  Nat.beq (pcomp 65 7 (mask 7) (ME.T j) (XT 0)) (pcomp 65 7 (mask 7) (XT 0) (ME.T j))

theorem card_hf : ∀ j ∈ List.range 15600,
    ((fun g => commutesA g (unpack 65 7 (XT 0))) ∘ fun i => unpack 65 7 (ME.T i)) j =
      Nat.beq (pcomp 65 7 (mask 7) (ME.T j) (XT 0)) (pcomp 65 7 (mask 7) (XT 0) (ME.T j)) := by
  intro j hj
  have hX := canonX (k := 0) (by omega)
  have hc := canonT' (List.mem_range.1 hj)
  simp only [Function.comp, commutesA]
  rw [compA_unpack hc hX, compA_unpack hX hc,
    eqA_unpack (canonK_pcomp hc hX) (canonK_pcomp hX hc)]

theorem card_c : centCnt 65 7 15600 ME.T (XT 0) = 240 := by
  have h := kCard
  generalize centCnt 65 7 15600 ME.T (XT 0) = c at h ⊢
  exact Nat.eq_of_beq_eq_true h

theorem card_hk : cfilt.length = 240 := by
  have h := centCnt_eq 65 7 15600 ME.T (XT 0)
  unfold cfilt
  rw [← h]
  exact card_c

theorem card_e1 : MinusFrame.cardCentralCheck (minusEnum ()) = (cfilt.length == 240) := by
  unfold MinusFrame.cardCentralCheck cfilt
  dsimp only
  rw [bindX.1, ptsList, List.filter_map, List.length_map, List.filter_congr card_hf]

theorem card : MinusFrame.cardCentralCheck (minusEnum ()) = true := by
  rw [card_e1, card_hk]
  rfl

end CertificateChecks.KernelMinusFrame

end
