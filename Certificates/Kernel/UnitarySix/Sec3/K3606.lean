module

public import Certificates.Kernel.UnitarySix.Sec3.K3606Chk
public import Certificates.Kernel.UnitarySix.Sec3.K3603
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelU6.Sec3

open CFSG.KC.U6Sec3 CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.Enum CFSG.Monster.B.Co2.Native
open CFSG.EvenSmallLie.UnitarySix.YamadaSec3 CFSG.RankThree.Native
open CFSG.EvenSmallLie.UnitarySix.YamadaHAut (dTab sTab d2Tab dsTab d2sTab)
open CFSG.Monster.B.Co2 (allLt_iff)

theorem dK_eq {q : ℕ} (hq : q < 6) {x : ℕ} (hx : x < 693) : (dArr[q]!)[x]! = dK q x := by
  have hd := dD_lt x hx
  have hs := sgK_lt x hx
  interval_cases q
  · have e : dArr[0]! = idA 693 := rfl
    rw [e, CFSG.Monster.B.Co2.idA_get hx]
    rfl
  · have e : dArr[1]! = dTab := rfl
    rw [e, dTab_eq x hx]
    rfl
  · have e : dArr[2]! = compA 693 dTab dTab := rfl
    rw [e, CFSG.Monster.B.Co2.compA_get hx, dTab_eq x hx, dTab_eq _ hd]
    rfl
  · have e : dArr[3]! = sTab := rfl
    rw [e, sTab_eq x hx]
    rfl
  · have e : dArr[4]! = compA 693 dTab sTab := rfl
    rw [e, CFSG.Monster.B.Co2.compA_get hx, sTab_eq x hx, dTab_eq _ hs]
    rfl
  · have e : dArr[5]! = compA 693 (compA 693 dTab dTab) sTab := rfl
    rw [e, CFSG.Monster.B.Co2.compA_get hx, sTab_eq x hx, CFSG.Monster.B.Co2.compA_get hs,
      dTab_eq _ hs, dTab_eq _ (dD_lt _ hs)]
    rfl

theorem dK_lt {q : ℕ} (hq : q < 6) {x : ℕ} (hx : x < 693) : dK q x < 693 := by
  have hd := dD_lt x hx
  have hs := sgK_lt x hx
  interval_cases q
  · exact hx
  · exact hd
  · exact dD_lt _ hd
  · exact hs
  · exact dD_lt _ hs
  · exact dD_lt _ (dD_lt _ hs)

theorem allLt_congrN {n : ℕ} {f g : ℕ → Bool} (h : ∀ p < n, f p = g p) : allLt n f = allN n g :=
  Bool.eq_iff_iff.2 (by
    rw [allLt_iff]
    exact ⟨fun h1 => allN_of_forall fun p hp => (h p hp) ▸ h1 p hp,
      fun h1 p hp => (h p hp).symm ▸ allN_spec h1 p hp⟩)

theorem anyWL_eq {W : List (List ℕ)} (hW : ∀ w ∈ W, ∀ k ∈ w, k < 18) (y : ℕ) {x : ℕ}
    (hx : x < 693) : (W.any fun w => y == (wA w)[x]!) = anyWL W y x := by
  induction W with
  | nil => rfl
  | cons w W ih =>
    rw [List.any_cons, wA_get (hW w List.mem_cons_self) hx,
      ih fun v hv => hW v (List.mem_cons_of_mem _ hv)]
    rfl

theorem z2sW_lt : ∀ w ∈ z2sW, ∀ k ∈ w, k < 18 := by decide

section

variable {L : List ℕ} (hL : ∀ t ∈ L, canonK 693 10 (mask 10) (693 * 10) t = true)
include hL

theorem c10_L : c10At (unpack 693 10 (prodL 693 10 (mask 10) L)) =
    allN 6 fun q => c10WK L q || (q == 0 && strictB (prodL 693 10 (mask 10) L) isId) := by
  unfold c10At
  refine allLt_congrN fun q hq => ?_
  rw [id_L hL]
  congr 1
  unfold c10Wit c10WK
  rw [chA1_K.O_any]
  have hl : chA1.gens.length = 9 := rfl
  rw [hl]
  refine range_any_congr fun j hj => ?_
  have hj' := PermK.canon (chA1_P j (hl ▸ hj))
  congr 1
  refine allLt_congrN fun p hp => ?_
  have h1 := dK_lt hq hp
  have h2 := canon_lt hj' hp
  dsimp only
  rw [strictB_eq, strictB_eq, unpack_get hp, dK_eq hq hp, prodL_get hL h1,
    unpack_get (ptL_lt hL h1), dK_eq hq h2, prodL_get hL (dK_lt hq h2), gz, hG 14 (by norm_num),
    unpack_get (canon_lt hj' (ptL_lt hL h1))]

theorem c8_L : c8At (unpack 693 10 (prodL 693 10 (mask 10) L)) =
    allN 6 fun q => q == 1 || q == 2 || c8WK L q ||
      (q == 0 && strictB (prodL 693 10 (mask 10) L) isId) := by
  unfold c8At
  refine allLt_congrN fun q hq => ?_
  rw [id_L hL]
  congr 2
  unfold c8WitL c8WK
  rw [chK1_K.O_any]
  have hl : chK1.gens.length = 5 := rfl
  rw [hl]
  refine range_any_congr fun j hj => ?_
  have hj' := PermK.canon (chK1_P j (hl ▸ hj))
  congr 1
  refine allLt_congrN fun p hp => ?_
  have h1 := dK_lt hq hp
  have h2 := canon_lt hj' hp
  have h3 := dK_lt hq h2
  rw [unpack_get hp, dK_eq hq h2, prodL_get hL h3, labA1_eq _ (ptL_lt hL h3), dK_eq hq hp,
    prodL_get hL h1, unpack_get (ptL_lt hL h1), labA1_eq _ (canon_lt hj' (ptL_lt hL h1))]

end

theorem z2sKeys_eq : (z2sW.map fun w => (wA w)[1]!) = z2sKeysLit := by
  rw [List.map_congr_left fun w hw => wA_get (z2sW_lt w hw) (by norm_num : 1 < 693), kZ2SKeys]

theorem z2sKey_L {L : List ℕ} (hL : ∀ t ∈ L, canonK 693 10 (mask 10) (693 * 10) t = true) :
    z2sKeyAt (unpack 693 10 (prodL 693 10 (mask 10) L)) = z2sKeyL L := by
  unfold z2sKeyAt z2sKeyL
  rw [prodL_get hL (by norm_num), id_L hL, z2sKeys_eq, memL_eq]

theorem labA1_k : labA1Check = true := by
  unfold labA1Check
  rw [Bool.and_eq_true]
  refine ⟨by decide, ?_⟩
  rw [chA1_K.O_all]
  refine List.all_eq_true.2 fun j hj => allLt_iff.2 fun p hp => ?_
  have hj' := PermK.canon (chA1_P j (List.mem_range.1 hj))
  rw [unpack_get hp, labA1_eq _ (canon_lt hj' hp), labA1_eq _ hp]
  exact allN_spec (List.all_eq_true.1 kLabA1 j hj) p hp

end CertificateChecks.KernelU6.Sec3
