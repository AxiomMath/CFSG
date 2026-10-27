module

public import Certificates.Kernel.UnitarySix.Sec3.K3603Chk
public import Certificates.Kernel.UnitarySix.Sec3.E3602
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelU6.Sec3

open CFSG.KC.U6Sec3 CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.Enum CFSG.Monster.B.Co2.Native
open CFSG.EvenSmallLie.UnitarySix.YamadaSec3 CFSG.RankThree.Native
open CFSG.EvenSmallLie.UnitarySix.YamadaPar CFSG.EvenSmallLie.UnitarySix.YamadaD

theorem findD_eq {α : Type} (f : α → Bool) (g : α → ℕ) : ∀ T : List α,
    ((T.find? f).map g).getD 0 = List.rec (motive := fun _ => ℕ) 0
      (fun t _ ih => Bool.rec ih (g t) (f t)) T
  | [] => rfl
  | t :: T => by
    rw [List.find?_cons]
    cases h : f t
    · simp only [findD_eq f g T]
      rw [h]
    · simp only [Option.map_some, Option.getD_some]
      rw [h]

theorem kWA_eqK (a : Array ℕ) : kWA a = kWK a[3]! a[1]! := by
  unfold kWA kWK
  exact findD_eq (fun p => p.1 == a[3]! && p.2.1 == a[1]!) (fun p => p.2.2) a4KeyTab

theorem kWK_lt : ∀ x < 693, ∀ y < 693, kWK x y < 16 := by
  intro x _ y _
  unfold kWK
  have h : ∀ T : List (ℕ × ℕ × ℕ), (∀ t ∈ T, t.2.2 < 16) →
      List.rec (motive := fun _ => ℕ) 0
        (fun t _ ih => Bool.rec ih t.2.2 (t.1 == x && t.2.1 == y)) T < 16 := by
    intro T
    induction T with
    | nil => intro _; norm_num
    | cons t T ih =>
      intro hT
      cases hb : (t.1 == x && t.2.1 == y)
      · simp only [hb]
        exact ih fun s hs => hT s (List.mem_cons_of_mem _ hs)
      · simp only [hb]
        exact hT t List.mem_cons_self
  exact h a4KeyTab (by decide)

theorem coordNWit_lt : ∀ v, ∀ k ∈ coordNWit v, k < 18 := by
  intro v k hk
  unfold coordNWit at hk
  rw [List.mem_filterMap] at hk
  obtain ⟨i, hi, he⟩ := hk
  have hi' := List.mem_range.1 hi
  split_ifs at he
  · rw [Option.some_inj] at he
    rw [← he]
    interval_cases i <;> decide

theorem coordWWit_lt : ∀ v, ∀ k ∈ coordWWit v, k < 18 := by
  intro v k hk
  unfold coordWWit at hk
  rw [List.mem_filterMap] at hk
  obtain ⟨i, hi, he⟩ := hk
  have hi' := List.mem_range.1 hi
  split_ifs at he
  · rw [Option.some_inj] at he
    rw [← he]
    interval_cases i <;> decide

theorem kNA_wA {w : List ℕ} (hw : ∀ k ∈ w, k < 18) : kNA (wA w) = pgP (ptW w 1) := by
  rw [kNA, wA_get hw (by norm_num), pt1_eq _ (by
    rw [← wA_get hw (by norm_num)]
    exact (rep_wA tabs_k w hw).lt (by norm_num))]

theorem coordNGen_k : coordNGenCheck = true := by
  have hk := kNGen
  rw [Bool.and_eq_true] at hk
  unfold coordNGenCheck
  rw [Bool.and_eq_true, Bool.and_eq_true]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [kNA, hidA, unpack_get (by norm_num), pt1_eq _ (canon_lt hid (by norm_num))]
    exact hk.1
  · refine Array.all_eq_true'.2 fun x hx => ?_
    obtain ⟨i, hi, rfl⟩ := Array.getElem_of_mem hx
    have hs : pt1Mask.size = 693 := by decide +kernel
    rw [← getElem!_pos pt1Mask i hi, pt1_eq i (hs ▸ hi)]
    exact decide_eq_true (pt1_lt i (hs ▸ hi))
  · refine List.all_eq_true.2 fun v hv => ?_
    rw [kNA_wA (coordNWit_lt v)]
    exact List.all_eq_true.1 hk.2 v hv

theorem coordWGen_k : coordWGenCheck = true := by
  unfold coordWGenCheck
  refine List.all_eq_true.2 fun v hv => ?_
  rw [kWA_eqK, wA_get (coordWWit_lt v) (by norm_num), wA_get (coordWWit_lt v) (by norm_num)]
  exact List.all_eq_true.1 kWGen v hv

section

variable {L : List ℕ} (hL : ∀ t ∈ L, canonK 693 10 (mask 10) (693 * 10) t = true)
include hL

theorem kNA_L : kNA (unpack 693 10 (prodL 693 10 (mask 10) L)) = pgP (ptL 10 (mask 10) L 1) := by
  rw [kNA, prodL_get hL (by norm_num), pt1_eq _ (ptL_lt hL (by norm_num))]

theorem conj_get {g gi : ℕ} (hg : PermK g gi = true) {p : ℕ} (hp : p < 693) :
    (conjA 693 (unpack 693 10 g) (unpack 693 10 (prodL 693 10 (mask 10) L)))[p]! =
      pg 10 (mask 10) g (ptL 10 (mask 10) L (pg 10 (mask 10) gi p)) := by
  have hX := prodL_canon hL
  rw [conj_unpack hg hX, unpack_get hp, comp_get (PermK.canon hg) (canon_comp hX
    (PermK.canon_inv hg)) hp, comp_get hX (PermK.canon_inv hg) hp, ← unpack_get
    (canon_lt (PermK.canon_inv hg) hp), prodL_get hL (canon_lt (PermK.canon_inv hg) hp)]

theorem kWA_L : kWA (unpack 693 10 (prodL 693 10 (mask 10) L)) = kWL L := by
  rw [kWA_eqK, prodL_get hL (by norm_num), prodL_get hL (by norm_num)]
  rfl

theorem coordW_L : coordWAt (unpack 693 10 (prodL 693 10 (mask 10) L)) = coordWL L := by
  have hkw : kWL L < 16 :=
    kWK_lt _ (ptL_lt hL (by norm_num : 3 < 693)) _ (ptL_lt hL (by norm_num : 1 < 693))
  have hl : chLam.gens.length = 3 := rfl
  have h3 : ((List.range 3).all fun j =>
      kWA (conjA 693 chLam.O[j]! (unpack 693 10 (prodL 693 10 (mask 10) L))) ==
        bmulVec 4 4 (wedgeGensW.getD j #[]) (kWA (unpack 693 10 (prodL 693 10 (mask 10) L)))) =
      (List.range 3).all fun j =>
        kWK (pg 10 (mask 10) (CLam.S j) (ptL 10 (mask 10) L (pg 10 (mask 10) (CLam.SI j) 3)))
          (pg 10 (mask 10) (CLam.S j) (ptL 10 (mask 10) L (pg 10 (mask 10) (CLam.SI j) 1))) ==
          pg 10 (mask 10) sec3WW (16 * j + kWL L) := by
    refine range_all_congr fun j hj => ?_
    have hj3 : j < chLam.gens.length := hl ▸ hj
    have hP := chLam_P j hj3
    rw [← chLam_K.hO j hj3, kWA_eqK, conj_get hL hP (by norm_num), conj_get hL hP (by norm_num),
      kWA_L hL, wW_eq j hj _ hkw]
  unfold coordWAt coordWL
  rw [h3, kWA_L hL, id_L hL, strictB_eq, strictB_eq]

end

theorem coordWPair_L {L L' : List ℕ} (hL : ∀ t ∈ L, canonK 693 10 (mask 10) (693 * 10) t = true)
    (hL' : ∀ t ∈ L', canonK 693 10 (mask 10) (693 * 10) t = true) :
    coordWPairAt (unpack 693 10 (prodL 693 10 (mask 10) L))
      (unpack 693 10 (prodL 693 10 (mask 10) L')) = coordWPairL L L' := by
  unfold coordWPairAt coordWPairL
  rw [kWA_eqK, CFSG.Monster.B.Co2.compA_get (by norm_num), CFSG.Monster.B.Co2.compA_get
    (by norm_num), prodL_get hL' (i := 3) (by norm_num), prodL_get hL' (i := 1) (by norm_num),
    prodL_get hL (ptL_lt hL' (by norm_num)), prodL_get hL (ptL_lt hL' (by norm_num)),
    kWA_L hL, kWA_L hL']
  rfl

end CertificateChecks.KernelU6.Sec3
