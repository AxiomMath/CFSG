module

public import CFSG.Certificates.Kernel.U6LinSound
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaN2Cert
import CFSG.Certificates.Kernel.U6LinProved
import CFSG.Certificates.Kernel.Common.EachUnfold
import CFSG.Certificates.Kernel.Common.ForallChunks
public import Mathlib

public section

namespace CertificateChecks.KernelU6

open CFSG.KC.U6F2 CFSG.KLie.CT CFSG.KC.Loop CFSG.KC.M1F2
open CFSG.EvenSmallLie.UnitarySix.YamadaPar (unpackN packN)
open CFSG.EvenSmallLie.UnitarySix.YamadaN2 (genABits h1Rels3 h1Fb9 cobFb9 urPair9 id9 zero9
  h1Check9W h1Ecols9 h1Qcols9)

@[expose] noncomputable def n2G : List ℕ :=
  [1210107565301461052048421, 1210107565310274333312035, 1210107565283860343358545,
    1210107565288249766315081, 1285739216161982708188673, 1323591935071603452544513,
    1210697872353209464394753, 1512339026942908422960129, 1229052677692326191039489,
    1238460661285174857696257, 1210407901336076916098049, 1361525934630777874547713]

@[expose] noncomputable def n2WL : List (List ℕ) :=
  [[0, 0], [1, 1], [2, 2], [3, 3], [4, 4], [5, 5], [6, 6], [7, 7], [8, 8], [9, 9], [10, 10],
    [11, 11], [0, 1, 0, 1], [0, 2, 0, 2], [0, 3, 0, 3], [1, 2, 1, 2], [1, 3, 1, 3], [0, 6, 0, 6, 2],
    [0, 7, 0, 7, 3], [0, 6, 7, 0, 7, 6, 3, 2], [1, 6, 1, 6, 3], [1, 7, 1, 7, 3, 2],
    [0, 8, 0, 8, 10], [0, 9, 0, 9, 11], [0, 8, 9, 0, 9, 8, 11, 10], [1, 8, 1, 8, 11],
    [1, 9, 1, 9, 11, 10], [2, 4, 2, 4, 6], [2, 5, 2, 5, 7], [2, 4, 5, 2, 5, 4, 7, 6],
    [3, 4, 3, 4, 7], [3, 5, 3, 5, 7, 6], [2, 10, 2, 10, 0], [2, 11, 2, 11, 1], [3, 10, 3, 10, 1],
    [3, 11, 3, 11, 1, 0], [4, 5, 4, 5], [4, 8, 4, 8], [4, 9, 4, 9], [5, 8, 5, 8],
    [4, 10, 4, 10, 8], [4, 11, 4, 11, 9], [6, 8, 6, 8, 4], [6, 9, 6, 9, 5]]

@[expose] noncomputable def h1Fb9K (v : ℕ) : ℕ :=
  orN 44 fun k => Nat.shiftLeft (Nat.shiftRight (urPairK 9 n2G
    ((List.range 12).map fun s => fget v s 81) (getLD [] n2WL k)) 81) (Nat.mul k 81)

@[expose] noncomputable def cobFb9K (v : ℕ) : ℕ :=
  orN 12 fun s => Nat.shiftLeft (Nat.xor (mulF 9 (getLD 0 n2G s) (fget v 0 81))
    (mulF 9 (fget v 0 81) (getLD 0 n2G s))) (Nat.mul s 81)

theorem n2G_spec : ∀ s < 12, packM 9 (genABits (Fin.ofNat 12 s)) = getLD 0 n2G s := by
  decide +kernel

theorem n2WL_eq : h1Rels3.map (List.map Fin.val) = n2WL := by
  decide +kernel

theorem urPair9_eq (C : Fin 12 → Array ℕ) (w : List (Fin 12)) :
    urPair9 C w = urPairG 9 id9 zero9 (fun s => genABits (Fin.ofNat 12 s))
      (fun s => C (Fin.ofNat 12 s)) (w.map Fin.val) := by
  induction w with
  | nil => rfl
  | cons s w ih =>
    simp only [urPair9, ih, List.map_cons, urPairG, Fin.ofNat_val_eq_self]

theorem cobFb9_eq (v : ℕ) : cobFb9 v = cobFb9K v := by
  rw [cobFb9, packN_eq_proved]
  refine orN_congr fun s hs => ?_
  rw [packM_bxor_proved, packM_bmul_proved, packM_bmul_proved,packM_unpackN_proved, n2G_spec s hs]

theorem h1Fb9_eq (v : ℕ) : h1Fb9 v = h1Fb9K v := by
  rw [h1Fb9, packN_eq_proved]
  refine orN_congr fun k hk => ?_
  have hw : ∀ s ∈ (h1Rels3.getD k []).map Fin.val, s < 12 := by
    intro s hs
    obtain ⟨t, -, rfl⟩ := List.mem_map.mp hs
    exact t.isLt
  have hW : getLD [] n2WL k = (h1Rels3.getD k []).map Fin.val := by
    rw [getLD_eq_getD, ← n2WL_eq, List.getD_eq_getElem?_getD, List.getElem?_map]
    rw [List.getD_eq_getElem?_getD]
    cases h1Rels3[k]? <;> rfl
  rw [urPair9_eq, hW, urPairK_eq_proved (I := id9) (Z := zero9)
    (gen := fun s => genABits (Fin.ofNat 12 s)) (C := fun s => unpackN 9 v (Fin.ofNat 12 s))
    (fun s hs => (n2G_spec s (hw s hs)).symm) ?_ (by decide +kernel) (by decide +kernel)]
  · rw [shiftRight_lor_shiftLeft (packM_lt_proved 9 _)]
  · intro s hs
    have h3 := hw s hs
    rw [Fin.val_ofNat, Nat.mod_eq_of_lt h3, packM_unpackN_proved, getLD_map_range _ _ h3]

@[expose] noncomputable def n2Seg (i : ℕ) : Bool :=
  idRowsSeg 972 ((List.range 81).map fun j => cobFb9K (2 ^ j)) h1Qcols9.toList
    ((List.range' (36 * i) 36).map fun l => h1Fb9K (2 ^ l)) ((h1Ecols9.toList.drop (36 * i)).take 36)
    (36 * i)

theorem h1Check9W_of (h : ∀ i < 27, n2Seg i = true) : h1Check9W = true := by
  rw [h1Check9W]
  refine certCheckWith_of_idRowsK_proved
    (F := (List.range (12 * (9 * 9))).map fun l => h1Fb9K (2 ^ l))
    (B := (List.range 81).map fun j => cobFb9K (2 ^ j))
    (fun l hl => by rw [getLD_map_range _ _ hl, h1Fb9_eq]) ?_ (by simp) (by decide +kernel)
    (idRowsK_of_segs_proved (c := 36) (k := 27) _ rfl h (by decide +kernel))
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [Array.toList_ofFn, List.getElem_ofFn, List.getElem_map, List.getElem_range,
    cobFb9_eq]

set_option maxRecDepth 100000

@[expose] noncomputable def n2SegF (i : Nat) : Bool := n2Seg i

#kc_each_unfold n2SegF 0 27 as CertificateChecks.KernelU6.n2Seg_

#kc_forall_chunks n2Seg_all (fun i => n2Seg i = true) 27 CertificateChecks.KernelU6.n2Seg_ 1

theorem h1Check9W_true : h1Check9W = true := h1Check9W_of n2Seg_all

end CertificateChecks.KernelU6
