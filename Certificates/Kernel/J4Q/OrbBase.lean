module

public import Certificates.Kernel.J4Q.LocVec
public import Certificates.Kernel.J4Q.VOrbData
public import Certificates.Kernel.J4Q.VOrbSq
public import CFSG.Certificates.Kernel.J4Q.RepVOrbB
public import CFSG.Sporadic.J4.QT2LocCntNative
public import CFSG.Sporadic.J4.QT2LocFixLNative
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Sporadic.J4.QTRankWitNative

@[expose] public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ4Q

open CFSG.KC.J4Q CFSG.KD.J4Q CFSG.KC.LQT.Syl CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT
  CFSG.Sporadic.J4.QT2

noncomputable def CH5 : List (List Nat) :=
  [O5_0, O5_1, O5_2, O5_3, O5_4, O5_5, O5_6, O5_7, O5_8, O5_9, O5_10, O5_11, O5_12, O5_13, O5_14]

noncomputable def CH6 : List (List Nat) :=
  [O6_0, O6_1, O6_2, O6_3, O6_4, O6_5, O6_6, O6_7, O6_8, O6_9, O6_10, O6_11, O6_12, O6_13, O6_14,
    O6_15, O6_16, O6_17, O6_18, O6_19, O6_20, O6_21, O6_22, O6_23, O6_24, O6_25, O6_26, O6_27]

noncomputable def SPC5 : List (List Nat) :=
  [S5_0, S5_1, S5_2, S5_3, S5_4, S5_5, S5_6, S5_7, S5_8, S5_9, S5_10, S5_11, S5_12, S5_13, S5_14]

noncomputable def SPC6 : List (List Nat) :=
  [S6_0, S6_1, S6_2, S6_3, S6_4, S6_5, S6_6, S6_7, S6_8, S6_9, S6_10, S6_11, S6_12, S6_13, S6_14,
    S6_15, S6_16, S6_17, S6_18, S6_19, S6_20, S6_21, S6_22, S6_23, S6_24, S6_25, S6_26, S6_27]

noncomputable def repK (ℓ : Nat) : Nat := pathVK rm one [A, B] (repPaths.getD ℓ []) (v2N rootV)

noncomputable def SQ5 : List (List Nat) :=
  [repK 5] :: [VQ5_0, VQ5_1, VQ5_2, VQ5_3, VQ5_4, VQ5_5, VQ5_6, VQ5_7, VQ5_8, VQ5_9, VQ5_10, VQ5_11,
    VQ5_12, VQ5_13, VQ5_14]

noncomputable def SQ6 : List (List Nat) :=
  [repK 6] :: [VQ6_0, VQ6_1, VQ6_2, VQ6_3, VQ6_4, VQ6_5, VQ6_6, VQ6_7, VQ6_8, VQ6_9, VQ6_10, VQ6_11,
    VQ6_12, VQ6_13, VQ6_14, VQ6_15, VQ6_16, VQ6_17, VQ6_18, VQ6_19, VQ6_20, VQ6_21, VQ6_22, VQ6_23,
    VQ6_24, VQ6_25, VQ6_26, VQ6_27]
noncomputable def LRs : List (List Nat) := [LR_0, LR_1, LR_2]

theorem lr_chk : andB (eqLK LR_0 (rowsOfJ rm L0)) (andB (eqLK LR_1 (rowsOfJ rm L1))
    (eqLK LR_2 (rowsOfJ rm L2))) = true := by quickRfl

theorem LRs_eq : LRs = [L0, L1, L2].map (rowsOfJ rm) := by
  have h := lr_chk
  simp only [andB_eq, Bool.and_eq_true] at h
  rw [LRs, eqLK_spec h.1, eqLK_spec h.2.1, eqLK_spec h.2.2]
  rfl

theorem forall_mem_of_getD {α : Type} {f : α → Bool} {d : α} {l : List α}
    (h : ∀ i < l.length, f (l.getD i d) = true) : ∀ x ∈ l, f x = true := by
  intro x hx
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hx
  have := h i hi
  rwa [List.getD_eq_getElem _ _ hi] at this

noncomputable def sizeK (cap : Nat) (CH SPC : List (List Nat)) : Bool :=
  andB (Nat.beq (CH.flatten.length + 1) cap) (andB (Nat.beq SPC.flatten.length cap)
    (andB (allR (CH.length - 1) fun i => Nat.beq (CH.getD i []).length 1024)
      (andB (CH.all fun ch => Nat.ble ch.length 1024) (SPC.all fun sc => Nat.ble sc.length 1024))))

theorem sorted_chunks {Pch SQ : List (List Nat)} {SP : List Nat} (hsq : SQ.length = Pch.length)
    (hin : ∀ i < Pch.length, andB (eqLK (sortN (Pch.getD i [])) (SQ.getD i []))
      (eqLK (diffS (SQ.getD i []) SP) []) = true) : Pch.map sortN = SQ := by
  refine List.ext_getElem (by rw [List.length_map, hsq]) (fun i hi1 hi2 => ?_)
  rw [List.length_map] at hi1
  have h := hin i hi1
  simp only [andB_eq, Bool.and_eq_true] at h
  rw [List.getElem_map, ← List.getD_eq_getElem _ [] hi1, ← List.getD_eq_getElem _ [] hi2]
  exact eqLK_spec h.1

theorem inSK_chunks {Pch SQ : List (List Nat)} {SP : List Nat}
    (hin : ∀ i < Pch.length, andB (eqLK (sortN (Pch.getD i [])) (SQ.getD i []))
      (eqLK (diffS (SQ.getD i []) SP) []) = true) :
    ∀ i < Pch.length, inSK (Pch.getD i []) SP = true := by
  intro i hi
  have h := hin i hi
  simp only [andB_eq, Bool.and_eq_true] at h
  exact inSK_of_sorted h.1 h.2

theorem spInK_chunks {Pch SQ SPC : List (List Nat)} (hsq : SQ.length = Pch.length)
    (hin : ∀ i < Pch.length, andB (eqLK (sortN (Pch.getD i [])) (SQ.getD i []))
      (eqLK (diffS (SQ.getD i []) SPC.flatten) []) = true)
    (hsp : ∀ i < SPC.length, eqLK (diffAll (SPC.getD i []) SQ) [] = true) :
    ∀ i < SPC.length, spInK (SPC.getD i []) Pch = true :=
  fun i hi => spInK_of_sorted (sorted_chunks hsq hin) (hsp i hi)

theorem orb_ok {ℓ cap bits : Nat} {CH SPC SQ : List (List Nat)} {P0 : List Nat}
    (hcap : cap < 2 ^ bits) (h32 : 4 * 2 ^ bits < 2 ^ 32) (hsize : sizeK cap CH SPC = true)
    (htree : ∀ i < CH.length, vtB rm (rep 1 128 1024) [L0, L1, L2] (vptsK rm (repK ℓ) CH.flatten)
      (CH.getD i []) (P0.getD i 0) (1 + 1024 * i) = true)
    (hsinc : sincK SPC.flatten 0 = true)
    (hsq : SQ.length = (pchK rm (repK ℓ) CH).length)
    (hin : ∀ i < (pchK rm (repK ℓ) CH).length,
      andB (eqLK (sortN ((pchK rm (repK ℓ) CH).getD i [])) (SQ.getD i []))
        (eqLK (diffS (SQ.getD i []) SPC.flatten) []) = true)
    (hsp : ∀ i < SPC.length, eqLK (diffAll (SPC.getD i []) SQ) [] = true)
    (hcl : ∀ i < (pchK rm (repK ℓ) CH).length,
      clB rm (rep 1 128 1024) [L0, L1, L2] ((pchK rm (repK ℓ) CH).getD i []) SPC.flatten = true) :
    vorbOK locTabs (pathVec (repPaths.getD ℓ [])) (vorbit locTabs (pathVec (repPaths.getD ℓ [])) cap bits)
      cap = true := by
  obtain ⟨hw, hv⟩ := pathVec_enc (repPaths.getD ℓ [])
  have hr : v2N (pathVec (repPaths.getD ℓ [])) = repK ℓ := hv
  simp only [sizeK, andB_eq, Bool.and_eq_true] at hsize
  obtain ⟨h1, h2, h3, h4, h5⟩ := hsize
  have hin' := inSK_chunks hin
  have hsp' := spInK_chunks hsq hin hsp
  rw [← hr] at htree hin' hsp' hcl
  exact vorbit_soundB hK (mats := locMats ()) (Ms := [L0, L1, L2]) (by simp [locMats, localWords])
    loc_gens hw hcap h32 LRs_eq (B := 1024) (by decide) (by decide) (Nat.eq_of_beq_eq_true h1)
    (fun i hi => Nat.eq_of_beq_eq_true (allR_spec h3 i (by omega)))
    (fun ch hch => Nat.le_of_ble_eq_true (List.all_eq_true.1 h4 ch hch)) htree hsinc
    (Nat.eq_of_beq_eq_true h2)
    (fun sc hsc => Nat.le_trans (Nat.le_of_ble_eq_true (List.all_eq_true.1 h5 sc hsc)) (by decide))
    (forall_mem_of_getD (f := fun pc => inSK pc SPC.flatten) hin')
    (forall_mem_of_getD (f := fun sc => spInK sc (pchK rm (v2N (pathVec (repPaths.getD ℓ []))) CH)) hsp')
    (forall_mem_of_getD (f := fun pc => clB rm (rep 1 128 1024) [L0, L1, L2] pc SPC.flatten) hcl)

end CertificateChecks.KernelJ4Q

end
