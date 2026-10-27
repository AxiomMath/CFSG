module

public import Certificates.Kernel.J4Q.ZFrDefs
public import CFSG.Certificates.Kernel.J4Q.RepPack
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ4Q

open CFSG.KC.J4Q CFSG.KD.J4Q CFSG.QuasithinUnique.A5 CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.QT2

theorem zfAll_congr {α : Type} {f g : α → Bool} : ∀ {l : List α}, (∀ x ∈ l, f x = g x) →
    l.all f = l.all g
  | [], _ => rfl
  | x :: l, h => by
    rw [List.all_cons, List.all_cons, h x List.mem_cons_self,
      zfAll_congr fun y hy => h y (List.mem_cons_of_mem _ hy)]

theorem zfFlatMap_congr {α β : Type} {f g : α → List β} : ∀ {l : List α}, (∀ x ∈ l, f x = g x) →
    l.flatMap f = l.flatMap g
  | [], _ => rfl
  | x :: l, h => by
    rw [List.flatMap_cons, List.flatMap_cons, h x List.mem_cons_self,
      zfFlatMap_congr fun y hy => h y (List.mem_cons_of_mem _ hy)]

theorem zfFilter_congr {α : Type} {p q : α → Bool} : ∀ {l : List α}, (∀ x ∈ l, p x = q x) →
    l.filter p = l.filter q
  | [], _ => rfl
  | x :: l, h => by
    rw [List.filter_cons, List.filter_cons, h x List.mem_cons_self,
      zfFilter_congr fun y hy => h y (List.mem_cons_of_mem _ hy)]

theorem zgb_chk : ((List.range 3).all fun g => unpackP (ZGB.getD g 0) == zcGenTabs.getD g []) = true := by
  decide

theorem zgb_eq {g : Nat} (hg : g < 3) : unpackP (ZGB.getD g 0) = zcGenTabs.getD g [] :=
  beq_iff_eq.1 (List.all_eq_true.1 zgb_chk g (List.mem_range.2 hg))

theorem zidb_eq : unpackP ZIDB = idT := by decide

theorem zfSeqB_eq : ∀ s : List Nat, (∀ g ∈ s, g < 3) → unpackP (zfSeqB s) = zfSeqT s
  | [], _ => zidb_eq
  | g :: s, hs => by
    change unpackP (compB (ZGB.getD g 0) (zfSeqB s)) = compT (zcGenTabs.getD g []) (zfSeqT s)
    rw [compB_sound, zgb_eq (hs g List.mem_cons_self),
      zfSeqB_eq s fun x hx => hs x (List.mem_cons_of_mem _ hx)]

theorem comm_eqB (p q : Nat) :
    (compT (unpackP p) (unpackP q) == compT (unpackP q) (unpackP p)) = (compB p q == compB q p) := by
  rw [← compB_sound, ← compB_sound]
  apply Bool.eq_iff_iff.2
  rw [beq_iff_eq, beq_iff_eq]
  exact ⟨fun h => unpackP_inj (compB_lt _ _) (compB_lt _ _) h, fun h => by rw [h]⟩

theorem zfCons_eqB (VsB bs : List Nat) (P : Nat) :
    zfCons (VsB.map unpackP) bs (unpackP P) = zfConsB VsB bs P := by
  unfold zfCons zfConsB
  refine zfAll_congr fun bj _ => zfAll_congr fun bl _ => ?_
  rw [List.all_map]
  refine zfAll_congr fun v _ => ?_
  simp only [Function.comp_apply, actB_sound]

theorem zfBtGo_eqB (TsB VsB : List Nat) :
    ∀ (C : List (List (List Nat))) (base bs : List Nat) (P : Nat) (tup : List Nat),
      (∀ lv ∈ C, ∀ s ∈ lv, ∀ g ∈ s, g < 3) →
      zfBtGo (TsB.map unpackP) (VsB.map unpackP) C base bs (unpackP P) tup =
        zfBtGoB TsB VsB C base bs P tup
  | [], base, bs, P, tup, _ => by
    have e : ((TsB.map unpackP).all fun T => compT (unpackP P) T == compT T (unpackP P)) =
        TsB.all (fun T => compB P T == compB T P) := by
      rw [List.all_map]
      exact zfAll_congr fun T _ => comm_eqB P T
    simp only [zfBtGo, zfBtGoB, e]
  | lv :: C, b :: base, bs, P, tup, hs => by
    simp only [zfBtGo, zfBtGoB]
    refine zfFlatMap_congr fun t _ => ?_
    have hst : ∀ g ∈ lv.getD t [], g < 3 := by
      intro g hg
      by_cases ht : t < lv.length
      · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht, Option.getD_some] at hg
        exact hs lv List.mem_cons_self _ (List.getElem_mem ht) g hg
      · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega), Option.getD_none] at hg
        simp at hg
    have e : compT (unpackP P) (zfSeqT (lv.getD t [])) = unpackP (compB P (zfSeqB (lv.getD t []))) := by
      rw [compB_sound, zfSeqB_eq _ hst]
    rw [e, zfCons_eqB, zfBtGo_eqB TsB VsB C base (bs ++ [b]) _ (t :: tup)
      (fun l hl => hs l (List.mem_cons_of_mem _ hl))]
  | _ :: _, [], _, _, _, _ => by simp [zfBtGo, zfBtGoB]

theorem zfBt_eqB {Ts : List (List Nat)} {TsB VsB : List Nat} (hT : Ts = TsB.map unpackP)
    (hV : zfVs Ts = VsB.map unpackP) {C : List (List (List Nat))} (base : List Nat)
    (hs : ∀ lv ∈ C, ∀ s ∈ lv, ∀ g ∈ s, g < 3) :
    zfBt Ts C base = zfBtGoB TsB VsB C base [] ZIDB [] := by
  unfold zfBt
  rw [hV, ← zidb_eq, hT, zfBtGo_eqB TsB VsB C base [] ZIDB [] hs]

theorem zfMasks_eqB (TsB d : List Nat) (hl : TsB.length = 4) :
    zfMasks (TsB.map unpackP) d = zfMasksB TsB d := by
  unfold zfMasks zfMasksB
  refine zfFilter_congr fun c _ => ?_
  refine zfAll_congr fun i hi => ?_
  have hi' : i < TsB.length := by rw [hl]; exact List.mem_range.1 hi
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hi', Option.map_some,
    Option.getD_some, List.getD_eq_getElem?_getD (l := TsB), List.getElem?_eq_getElem hi',
    Option.getD_some, actB_sound]

end CertificateChecks.KernelJ4Q

end
