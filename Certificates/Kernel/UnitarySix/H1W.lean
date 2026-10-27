module

public import CFSG.Certificates.Kernel.U6LinSound
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaParH1Cert
import CFSG.Certificates.Kernel.U6LinProved

public section

namespace CertificateChecks.KernelU6

open CFSG.KC.U6F2 CFSG.KLie.CT CFSG.KC.Loop CFSG.KC.M1F2
open CFSG.EvenSmallLie.UnitarySix.YamadaPar (genBits h1Rels h1Fb cobFb urPair unpackBlk packBlks
  unpackN packN id8 zero8 h1CheckW h1Ecols h1Qcols)

@[expose] noncomputable def h1G : List ℕ :=
  [9241564904308408833, 8855733356843802704, 577597671709812253]

@[expose] noncomputable def h1WL : List (List ℕ) := h1Rels.map (List.map Fin.val)

@[expose] noncomputable def h1FbK (v : ℕ) : ℕ :=
  orN 7 fun k => Nat.shiftLeft (Nat.shiftRight (urPairK 8 h1G
    [fget v 0 64, fget v 1 64, fget v 2 64] (getLD [] h1WL k)) 64) (Nat.mul k 64)

@[expose] noncomputable def cobFbK (v : ℕ) : ℕ :=
  orN 3 fun s => Nat.shiftLeft (Nat.xor (mulF 8 (getLD 0 h1G s) (fget v 0 64))
    (mulF 8 (fget v 0 64) (getLD 0 h1G s))) (Nat.mul s 64)

theorem h1G_spec : ∀ s < 3, packM 8 (genBits (Fin.ofNat 3 s)) = getLD 0 h1G s := by
  decide +kernel

theorem urPair_eq (C : Fin 3 → Array ℕ) (w : List (Fin 3)) :
    urPair C w = urPairG 8 id8 zero8 (fun s => genBits (Fin.ofNat 3 s))
      (fun s => C (Fin.ofNat 3 s)) (w.map Fin.val) := by
  induction w with
  | nil => rfl
  | cons s w ih =>
    simp only [urPair, ih, List.map_cons, urPairG, Fin.ofNat_val_eq_self]

theorem cobFb_eq (v : ℕ) : cobFb v = cobFbK v := by
  rw [cobFb, packBlks_eq, packN_eq_proved]
  refine orN_congr fun s hs => ?_
  rw [unpackBlk_eq, packM_bxor_proved, packM_bmul_proved, packM_bmul_proved,
    packM_unpackN_proved, h1G_spec s hs]

theorem h1Fb_eq (v : ℕ) : h1Fb v = h1FbK v := by
  rw [h1Fb, packBlks_eq, packN_eq_proved]
  refine orN_congr fun k hk => ?_
  have hw : ∀ s ∈ (h1Rels.getD k []).map Fin.val, s < 3 := by
    intro s hs
    obtain ⟨t, -, rfl⟩ := List.mem_map.mp hs
    exact t.isLt
  have hW : getLD [] h1WL k = (h1Rels.getD k []).map Fin.val := by
    rw [getLD_eq_getD, h1WL, List.getD_eq_getElem?_getD, List.getElem?_map]
    rw [List.getD_eq_getElem?_getD]
    cases h1Rels[k]? <;> rfl
  rw [urPair_eq, hW, urPairK_eq_proved (I := id8) (Z := zero8)
    (gen := fun s => genBits (Fin.ofNat 3 s)) (C := fun s => unpackBlk v (Fin.ofNat 3 s))
    (fun s hs => (h1G_spec s (hw s hs)).symm) ?_ (by decide +kernel) (by decide +kernel)]
  · rw [shiftRight_lor_shiftLeft (packM_lt_proved 8 _)]
  · intro s hs
    have h3 := hw s hs
    rw [unpackBlk_eq, Fin.val_ofNat, Nat.mod_eq_of_lt h3, packM_unpackN_proved]
    interval_cases s <;> rfl

theorem h1CheckW_true : h1CheckW = true := by
  rw [h1CheckW]
  refine certCheckWith_of_idRowsK_proved (F := (List.range (3 * 64)).map fun l => h1FbK (2 ^ l))
    (B := (List.range 64).map fun j => cobFbK (2 ^ j))
    (fun l hl => by rw [getLD_map_range _ _ hl, h1Fb_eq]) ?_ (by simp) (by decide +kernel) ?_
  · apply List.ext_getElem (by simp)
    intro i h1 h2
    simp only [Array.toList_ofFn, List.getElem_ofFn, List.getElem_map, List.getElem_range,
      cobFb_eq]
  · decide +kernel

end CertificateChecks.KernelU6
