module

public import CFSG.Certificates.Kernel.KeyTreeSound
import all Certificates.Data.SmithD6Model
public import Certificates.Kernel.SmithD6Ea.Glue

set_option maxRecDepth 100000

public section

namespace CertificateChecks.SmithD6Ea

open CFSG.SmithD6 CFSG.KC.KeyTree CFSG.KD.SmithD6 CFSG.KD.SmithD6Stab CFSG.KD.SmithD6Nc
  CFSG.KD.SmithD6ST CFSG.KD.SmithD6Ea CFSG.KD.SmithD6Reps CertificateChecks.SmithD6Stab
  CertificateChecks.SmithD6Nc CertificateChecks.SmithD6Trees

theorem baseK_memB : ∀ x ∈ eaBaseK, lineTree.memB x = true := by decide +kernel

theorem bases_eq : ea7Bases = eaBaseK.map posK := by decide +kernel

theorem base_facts {t : Nat} (ht : t < 5) :
    lineTree.memB (eaBaseK.getD t 0) = true ∧ posK (eaBaseK.getD t 0) = ea7Bases[t]! := by
  obtain rfl | rfl | rfl | rfl | rfl : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 := by omega
  all_goals decide +kernel

theorem memB_of_rtg {t x v : Nat} (hx : lineTree.memB x = true)
    (h : Relation.ReflTransGen (fun a b => ∃ g, eaEdge t g a b = true) x v) :
    lineTree.memB v = true := by
  induction h with
  | refl => exact hx
  | tail _ hst _ =>
    obtain ⟨g, hg⟩ := hst
    unfold eaEdge at hg
    simp only [Bool.and_eq_true] at hg
    exact hg.1.2

theorem edge_facts {t g a b : Nat} (h : eaEdge t g a b = true) :
    lineTree.memB g = true ∧ eaInYK (eaBaseK.take t) g = true ∧ lineTree.memB a = true ∧
      lineTree.memB b = true ∧ imgN g a = b := by
  unfold eaEdge at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

section Model

variable (hK : lineKeys.toList = J.lineKeysC.flatten)
  (hL : ∀ u w, u < 4096 → w < 4096 → lineTree.memB (4096 * u + w) = true →
    lineIdx u w < 365211 ∧ linePair (lineIdx u w) = (u, w))
  (hI : ∀ u w, lineIdx u w < 365211 → lineKeys[lineIdx u w]! = 4096 * u + w)
include hK hL hI

theorem edge_img {g a b : Nat} (hg : lineTree.memB g = true) (ha : lineTree.memB a = true)
    (hb : lineTree.memB b = true) (himg : imgN g a = b) : tvImg (posK g) (posK a) = posK b := by
  obtain ⟨hgl, hgk⟩ := key_of_memB hg
  obtain ⟨hal, hak⟩ := key_of_memB ha
  have hgb : g < 16777216 := by
    have := key_lt hgl
    rwa [hgk] at this
  have hab : a < 16777216 := by
    have := key_lt hal
    rwa [hak] at this
  rw [imgN_eq] at himg
  have hok : imgOK g a = true := imgOK_of hgb hab (by rw [himg]; exact hb)
  have e := (tvImg_eq hK hL hg ha hok).1
  rw [e, himg]

theorem base_fix {g x : Nat} (hg : lineTree.memB g = true) (hx : x ∈ eaBaseK) :
    (tvImg (posK g) (posK x) == posK x) = (imgN g x == x) := by
  obtain ⟨hgl, hgk⟩ := key_of_memB hg
  obtain ⟨hxl, hxk⟩ := key_of_memB (baseK_memB x hx)
  rw [tvImg_beq hK hL hI hgl hxl, hgk, hxk, ← imgN_eq, beqN]

theorem edge_inY {t g : Nat} (hg : lineTree.memB g = true)
    (hy : eaInYK (eaBaseK.take t) g = true) : ea7InY (ea7Bases.take t) (posK g) = true := by
  obtain ⟨hgl, hgk⟩ := key_of_memB hg
  unfold eaInYK at hy
  rw [Bool.and_eq_true] at hy
  have hX : ea7InX (posK g) = true := by
    rw [ea7InX_eq hK hL hI, hgk, hy.1, decide_eq_true hgl]
    rfl
  have hall : ((ea7Bases.take t).all fun b => tvImg (posK g) b == b) = true := by
    rw [bases_eq, ← List.map_take, List.all_eq_true]
    intro y hy'
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy'
    rw [base_fix hK hL hI hg (List.mem_of_mem_take hx)]
    exact List.all_eq_true.1 hy.2 x hx
  unfold ea7InY
  rw [hX, hall]
  rfl

theorem ea7Chain_of_pinned : ∀ t < 5, ∃ S : List Nat, S.length = ea7Sizes[t]! ∧ S.Nodup ∧
    ∀ x ∈ S, x < 365211 ∧ Relation.ReflTransGen
      (fun a b => ∃ q, ea7InY (ea7Bases.take t) q = true ∧ tvImg q a = b) ea7Bases[t]! x := by
  intro t ht
  have hok : eaLvOK t = true ∧ ea7Sizes[t]! = ea7Sizes.getD t 0 := by
    obtain rfl | rfl | rfl | rfl | rfl : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 := by omega
    exacts [⟨lv0_ok, rfl⟩, ⟨lv1_ok, rfl⟩, ⟨lv2_ok, rfl⟩, ⟨lv3_ok, rfl⟩, ⟨lv4_ok, rfl⟩]
  obtain ⟨hok, hsz⟩ := hok
  have hbase := base_facts ht
  unfold eaLvOK at hok
  simp only [Bool.and_eq_true, beq_iff_eq] at hok
  obtain ⟨⟨hlen, hinc⟩, hreach⟩ := hok
  have hR := reach_sound (reachK_all hreach)
  have hpw := (eaIncr_sound _ _ hinc).2
  have hmem : ∀ r ∈ (JEA.eaLv.getD t []).map eaRec, lineTree.memB r.1 = true ∧
      Relation.ReflTransGen (fun a b => ∃ q, ea7InY (ea7Bases.take t) q = true ∧ tvImg q a = b)
        ea7Bases[t]! (posK r.1) := by
    intro r hr
    obtain ⟨x, hx, hxr⟩ := hR r hr
    have hx' : x = eaBaseK.getD t 0 := by simpa using hx
    subst hx'
    refine ⟨memB_of_rtg hbase.1 hxr, ?_⟩
    rw [← hbase.2]
    generalize r.1 = v at hxr ⊢
    induction hxr with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hst ih =>
      obtain ⟨g, hg⟩ := hst
      obtain ⟨h1, h2, h3, h4, h5⟩ := edge_facts hg
      exact Relation.ReflTransGen.tail ih
        ⟨posK g, edge_inY hK hL hI h1 h2, edge_img hK hL hI h1 h3 h4 h5⟩
  refine ⟨((JEA.eaLv.getD t []).map eaRec).map (fun r => posK r.1), ?_, ?_, ?_⟩
  · rw [List.length_map, hlen, hsz]
  · have e : ((JEA.eaLv.getD t []).map eaRec).map (fun r => posK r.1) =
        (((JEA.eaLv.getD t []).map eaRec).map (·.1)).map posK := by
      simp only [List.map_map]
      rfl
    rw [e]
    refine List.Nodup.map_on ?_ (hpw.imp Nat.ne_of_lt)
    intro a ha b hb hab
    obtain ⟨ra, hra, rfl⟩ := List.mem_map.1 ha
    obtain ⟨rb, hrb, rfl⟩ := List.mem_map.1 hb
    exact posK_inj (hmem ra hra).1 (hmem rb hrb).1 hab
  · intro x hx
    obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hx
    exact ⟨(key_of_memB (hmem r hr).1).1, (hmem r hr).2⟩

end Model

end CertificateChecks.SmithD6Ea

end
