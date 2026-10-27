module

public import Certificates.Kernel.J2Vert.Nonsplit300202
public import CFSG.Certificates.Kernel.J2VertKSound
import CFSG.Certificates.Kernel.Spor.RawOrbEval

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ2Vert.Nonsplit

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin CFSG.KC.J2VertK
open CFSG.Monster.B.Co2.Native CFSG.Quasithin.Background.Harris.R1.J2Vert
open CFSG.ComponentClassification.J2Cover

theorem hid : idA 315 = unpack 315 9 one := by
  have h := kId
  rw [bAnd_iff] at h
  exact (idK_sound h.2).symm

theorem cid : cn one = true := by
  have h := kId
  rw [bAnd_iff] at h
  exact h.1

theorem hB : ∀ k < 3, (#[autStrong[0]!, autStrong[1]!, outerArr] : Array (Array Nat)).getD k
    (idA 315) = unpack 315 9 (NB k) := by
  have h := kBind
  simp only [bAnd_iff] at h
  obtain ⟨h0, h1, h2⟩ := h
  intro k hk
  match k, hk with
  | 0, _ => exact unpack_eq_of_bindArrK h0
  | 1, _ => exact unpack_eq_of_bindArrK h1
  | 2, _ => exact unpack_eq_of_bindArrK h2

theorem gen {i : Nat} (hi : i < 8) : invEqK 315 9 (mask 9) (315 * 9) (NG i) (NGI i) = true ∧
    cn (NG i) = true ∧ cn (NGI i) = true := by
  have h := allN_spec kGen i hi
  simp only [bAnd_iff] at h
  exact h

theorem hG : ∀ l < 8, (rGenArrs 315 #[autStrong[0]!, autStrong[1]!, outerArr]).getD l (idA 315) =
    unpack 315 9 (NG l) := by
  intro l hl
  have e := (evalW_eq hB (fun k hk => allN_spec kCanonB k hk) hid cid (rWords.getD l [])).1
  rw [Nat.eq_of_beq_eq_true (allN_spec kWords l hl), ← e]
  unfold rGenArrs
  rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getElem?_map,
    List.getElem?_range hl]
  rfl

theorem tree : buildTab 315 (rGenArrs 315 #[autStrong[0]!, autStrong[1]!, outerArr]) tabR =
      (List.range (tabR.length + 1)).map (fun j => unpack 315 9 (NE j)) ∧
    ∀ j ≤ tabR.length, cK 315 9 (NE j) :=
  have h := (bAnd_iff (Nat.beq (NE 0) one) (treeK 315 9 8 NG NE tabR 0)).1 kTree
  buildTab_eq hG (fun l hl => (gen hl).2.1) hid cid (Nat.eq_of_beq_eq_true h.1) h.2

theorem lenR : tabR.length + 1 = 3840 := by decide

theorem facts :
    (relCheck 315 (rGenArrs 315 #[autStrong[0]!, autStrong[1]!, outerArr]) (vRels true) = true)
    ∧ (tabLower 315 (rGenArrs 315 #[autStrong[0]!, autStrong[1]!, outerArr]) tabR 3840 = true) :=
  ⟨relCheck_of hG (fun l hl => (gen hl).2.1) (fun l hl => (gen hl).2.2)
      (CFSG.KS.Raw.Orb.allN_iff.2 fun i hi => (gen hi).1) hid cid kRel,
    tabLower_of tree.1 tree.2 lenR kSort⟩

end CertificateChecks.KernelJ2Vert.Nonsplit

end
