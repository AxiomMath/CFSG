module

public import Certificates.Kernel.U52.PtLnChk
public import CFSG.Certificates.Kernel.U52.PtLnSound
public import Certificates.Kernel.U52.GlueX
import CFSG.Certificates.Kernel.Misc.HexFlatSound
import CFSG.Certificates.Kernel.Misc.ArrBind
import CFSG.Certificates.Kernel.Spor.HexText
import CFSG.Certificates.Kernel.Spor.PcompFacts

public section

set_option maxRecDepth 400000

namespace CFSG.KC.U52PL

open CFSG.ASVolI CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Misc.ArrEnum CertificateChecks.KernelU52
  CertificateChecks.KernelU52G

private theorem beq_t {a b : Nat} : Nat.beq a b = true ↔ a = b :=
  ⟨Nat.eq_of_beq_eq_true, fun h => h ▸ Nat.beq_refl a⟩

private theorem chars_rec : ∀ cs : List Char,
    List.rec (motive := fun _ => Bool) true
      (fun c _ ih => bAnd(Nat.blt (Char.toNat c) (nat_lit 58), ih)) cs = true →
    ∀ c ∈ cs, c.toNat < 58
  | [], _, c, hc => absurd hc List.not_mem_nil
  | d :: cs, h, c, hc => by
    dsimp only at h
    rw [bAnd_iff] at h
    rcases List.mem_cons.1 hc with rfl | hc
    · exact Nat.blt_eq.mp h.1
    · exact chars_rec cs h.2 c hc

theorem chars_facts : PtsT.chars.length = 825 ∧ ∀ c ∈ PtsT.chars, c.toNat < 58 := by
  have h := chars_ok
  unfold charsK at h
  rw [bAnd_iff] at h
  exact ⟨beq_t.1 h.1, chars_rec _ h.2⟩

theorem byte_lt {m : Nat} (hm : m < 825) :
    (burnsideF48t_u52PtStr.toUTF8.get! m).toNat < 58 := by
  obtain ⟨hlen, hall⟩ := chars_facts
  have hch : ∀ k < 825, (PtsT.chars[k]!).toNat < 58 := fun k hk => by
    have hk' : k < PtsT.chars.length := by rw [hlen]; exact hk
    exact hall _ (by rw [getElem!_pos PtsT.chars k hk']; exact List.getElem_mem hk')
  have hc : ∀ k < 825, k < PtsT.chars.length ∧ (PtsT.chars[k]!).toNat < 128 := fun k hk =>
    ⟨by rw [hlen]; exact hk, by have := hch k hk; omega⟩
  rw [PtsT.eq, String.toUTF8_eq_toByteArray, String.toByteArray_ofList,
    CFSG.KS.HexText.utf8_get _ 825 hc m hm, UInt8.toNat_ofNat']
  have := hch m hm
  rw [Nat.mod_eq_of_lt (by omega)]
  exact this

private theorem bytes_get (b : ByteArray) (n : Nat) : b[n]! = b.get! n := by
  rcases b with ⟨bs⟩
  by_cases h : n < bs.size
  · rw [getElem!_pos (ByteArray.mk bs) n h]
    change bs[n] = bs[n]!
    rw [getElem!_pos bs n h]
  · rw [getElem!_neg (ByteArray.mk bs) n h]
    change default = bs[n]!
    rw [getElem!_neg bs n h]

theorem pts_eq {k : Nat} (hk : k < 165) : (burnsideF48t_u52Pt ())[k]! = unpack 5 2 (PtsT.F k) := by
  have hT := CFSG.KC.Misc.HexFlat.hexTable_sound PtsT.all k hk
  rw [← PtsT.eq] at hT
  unfold burnsideF48t_u52Pt
  rw [getElem!_pos _ k (by simpa using hk)]
  apply Array.ext (by simp [unpack])
  intro j h1 h2
  have hj : j < 5 := by simpa using h1
  simp only [Array.getElem_map, Array.getElem_range, unpack, Array.getElem_ofFn]
  have e := congrArg (fun a => a[j]!) hT
  simp only at e
  rw [CFSG.KS.WordF.getElem!_unpack, if_pos hj,
    getElem!_pos _ j (by simpa [CFSG.Monster.B.Co2.Native.hexTable] using hj)] at e
  simp only [CFSG.Monster.B.Co2.Native.hexTable, Array.getElem_ofFn,
    CFSG.Monster.B.Co2.Native.hexAt, CFSG.Monster.B.Co2.Native.hexVal, Nat.one_mul, Nat.add_zero,
    Nat.zero_mul, Nat.zero_add] at e
  have hl := byte_lt (m := 5 * k + j) (by omega)
  rw [bytes_get]
  rw [if_pos hl] at e
  rw [e]

theorem lns_eq {l : Nat} (hl : l < 297) : burnsideF48t_u52LnPts[l]! = unpack 5 8 (LP l) :=
  arrBind_sound (allN_spec lp_bind l hl)

theorem u_eq {k : Nat} (hk : k < 6) : burnsideF48t_u52U[k]! = unpack 5 2 (UP k) :=
  arrBind_sound (allN_spec up_bind k hk)

theorem pt_size : (burnsideF48t_u52Pt ()).size = 165 := by
  simp [burnsideF48t_u52Pt]

theorem ln_size : burnsideF48t_u52LnPts.size = 297 := by
  decide +kernel

theorem g_size : (burnsideF48t_u52Gens ()).size = 6 := by
  decide +kernel

theorem g_get {k : Nat} (hk : k < 6) {x : Nat} (hx : x < 462) :
    ((burnsideF48t_u52Gens ())[k]!)[x]! = pg 9 (mask 9) (CX.S k) x := by
  rw [g_eq k hk, CFSG.KS.WordF.getElem!_unpack, if_pos hx]

theorem pts_small : ∀ p ∈ burnsideF48t_u52Pt (), p.size = 5 ∧ ∀ x ∈ p, x < 4 := by
  intro p hp
  obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.1 hp
  have hi' : i < 165 := pt_size ▸ hi
  rw [← getElem!_pos _ i hi, pts_eq hi']
  refine ⟨unpack_size5 _ _, fun x hx => ?_⟩
  obtain ⟨j, hj, rfl⟩ := Array.mem_iff_getElem.1 hx
  have hj' : j < 5 := by simpa [unpack] using hj
  rw [← getElem!_pos _ j hj, unpack_f2 _ hj']
  exact f2_lt _ _

theorem pts_ne : ∀ i < 165, ∀ j < 165, i ≠ j → ∀ l ∈ [1, 2, 3],
    (burnsideF48t_u52Pt ())[i]! ≠ burnsideF48t_u52Scale l (burnsideF48t_u52Pt ())[j]! := by
  intro i hi j hj hij l hl he
  have hl4 : l < 4 := by simp at hl; omega
  have hl0 : 0 < l := by simp at hl; omega
  obtain ⟨hn, hinj⟩ := ptsK_spec pts_ok
  rw [pts_eq hi, pts_eq hj, scale_eq hl4] at he
  have e := CFSG.KS.WordF.unpack_inj (n := 5) (w := 2) (P := PtsT.F i) (Q := scK l (PtsT.F j))
    (by norm_num) (ptNorm_spec (hn i hi)).1 (scK_canon l _) he
  have hs : ptNorm (scK l (PtsT.F j)) = true := e ▸ hn i hi
  have h1 := scale_spec hl4 hl0 (hn j hj) hs
  subst h1
  rw [scK_one (ptNorm_spec (hn j hj)).1] at e
  exact hij (hinj i hi j hj e)

private theorem ln_inc {l : Nat} (hl : l < 297) :
    LP l >>> 40 = 0 ∧ (∀ a b, a < b → b < 5 → f8 (LP l) a < f8 (LP l) b) ∧
      ∀ a < 5, f8 (LP l) a < 165 := by
  obtain ⟨h0, h01, h12, h23, h34, h4⟩ := lnInc_spec ((lnsK_spec lns_ok).1 l hl)
  refine ⟨h0, fun a b hab hb => ?_, fun a ha => ?_⟩
  · interval_cases b <;> interval_cases a <;> omega
  · interval_cases a <;> omega

theorem lns_small : ∀ L ∈ burnsideF48t_u52LnPts, L.size = 5 ∧ (∀ p ∈ L, p < 165) ∧
    ∀ a < 5, ∀ b < 5, a ≠ b → L[a]! ≠ L[b]! := by
  intro L hL
  obtain ⟨l, hl, rfl⟩ := Array.mem_iff_getElem.1 hL
  have hl' : l < 297 := ln_size ▸ hl
  rw [← getElem!_pos _ l hl, lns_eq hl']
  obtain ⟨-, hinc, hlt⟩ := ln_inc hl'
  refine ⟨unpack_size5 _ _, fun p hp => ?_, fun a ha b hb hab => ?_⟩
  · obtain ⟨a, ha, rfl⟩ := Array.mem_iff_getElem.1 hp
    have ha' : a < 5 := by simpa [unpack] using ha
    rw [← getElem!_pos _ a ha, unpack_f8 _ ha']
    exact hlt a ha'
  · rw [unpack_f8 _ ha, unpack_f8 _ hb]
    rcases Nat.lt_or_gt_of_ne hab with h | h
    · exact Nat.ne_of_lt (hinc a b h hb)
    · exact Nat.ne_of_gt (hinc b a h ha)

private theorem sorted5 {x y : Nat → Nat} (hx : ∀ a b, a < b → b < 5 → x a < x b)
    (hy : ∀ a b, a < b → b < 5 → y a < y b) (h : ∀ a < 5, ∃ b < 5, y b = x a) :
    ∀ a < 5, x a = y a := by
  have mono : ∀ {i i' bi bi' : Nat}, i < i' → i' < 5 → bi < 5 → y bi = x i → y bi' = x i' →
      bi < bi' := by
    intro i i' bi bi' hii' hi' hbi ei ei'
    by_contra hc
    have hle : bi' ≤ bi := by omega
    have hx' := hx i i' hii' hi'
    rcases Nat.lt_or_eq_of_le hle with hlt | heq
    · have := hy bi' bi hlt hbi
      omega
    · subst heq
      omega
  obtain ⟨b0, hb0, e0⟩ := h 0 (by norm_num)
  obtain ⟨b1, hb1, e1⟩ := h 1 (by norm_num)
  obtain ⟨b2, hb2, e2⟩ := h 2 (by norm_num)
  obtain ⟨b3, hb3, e3⟩ := h 3 (by norm_num)
  obtain ⟨b4, hb4, e4⟩ := h 4 (by norm_num)
  have m01 := mono (by norm_num) (by norm_num) hb0 e0 e1
  have m12 := mono (by norm_num) (by norm_num) hb1 e1 e2
  have m23 := mono (by norm_num) (by norm_num) hb2 e2 e3
  have m34 := mono (by norm_num) (by norm_num) hb3 e3 e4
  intro a ha
  interval_cases a
  · rw [← e0, show b0 = 0 by omega]
  · rw [← e1, show b1 = 1 by omega]
  · rw [← e2, show b2 = 2 by omega]
  · rw [← e3, show b3 = 3 by omega]
  · rw [← e4, show b4 = 4 by omega]

theorem lns_ne : ∀ l < 297, ∀ l' < 297, l ≠ l' →
    ∃ p ∈ burnsideF48t_u52LnPts[l]!, p ∉ burnsideF48t_u52LnPts[l']! := by
  intro l hl l' hl' hll'
  by_contra hcon
  push Not at hcon
  rw [lns_eq hl, lns_eq hl'] at hcon
  apply hll'
  apply (lnsK_spec lns_ok).2 l hl l' hl'
  obtain ⟨h0, hinc, -⟩ := ln_inc hl
  obtain ⟨h0', hinc', -⟩ := ln_inc hl'
  have hsub : ∀ a < 5, ∃ b < 5, f8 (LP l') b = f8 (LP l) a := by
    intro a ha
    have hm : f8 (LP l) a ∈ unpack 5 8 (LP l) := by
      rw [← unpack_f8 _ ha, getElem!_pos _ a (by rw [unpack_size5]; exact ha)]
      exact Array.getElem_mem _
    obtain ⟨b, hb, eb⟩ := Array.mem_iff_getElem.1 (hcon _ hm)
    have hb' : b < 5 := by simpa [unpack] using hb
    exact ⟨b, hb', by rw [← unpack_f8 _ hb', getElem!_pos _ b hb, eb]⟩
  have he := sorted5 hinc hinc' hsub
  exact CFSG.KS.PF.eq_of_fields (n := 5) (w := 8) (by norm_num) h0 h0' fun a ha => he a ha

theorem gen_pt : ∀ k < 6, ∀ i < 165, ((burnsideF48t_u52Gens ())[k]!)[i]! < 165 ∧
    ∃ l ∈ [1, 2, 3], burnsideF48t_u52TV burnsideF48t_u52U[k]! (burnsideF48t_u52Pt ())[i]! =
      burnsideF48t_u52Scale l (burnsideF48t_u52Pt ())[((burnsideF48t_u52Gens ())[k]!)[i]!]! := by
  intro k hk i hi
  obtain ⟨hlt, he⟩ := genPt_spec ((gensK_spec gens_ok).1 k hk i hi)
  rw [g_get hk (by omega)]
  refine ⟨hlt, ?_⟩
  have hnj := (ptsK_spec pts_ok).1 _ hlt
  rw [← he] at hnj
  obtain ⟨ex, hl0, hl4⟩ := norm_spec (tvK_canon _ _) hnj
  refine ⟨leadK (tvK (UP k) (PtsT.F i)), by simp only [List.mem_cons, List.not_mem_nil]; omega, ?_⟩
  rw [u_eq hk, pts_eq hi, pts_eq hlt, tv_eq, scale_eq hl4, ← he, ← ex]

theorem gen_ln : ∀ k < 6, ∀ l < 297, 165 ≤ ((burnsideF48t_u52Gens ())[k]!)[165 + l]! ∧
    ((burnsideF48t_u52Gens ())[k]!)[165 + l]! < 462 ∧
    (∀ p ∈ burnsideF48t_u52LnPts[l]!, ((burnsideF48t_u52Gens ())[k]!)[p]! ∈
      burnsideF48t_u52LnPts[((burnsideF48t_u52Gens ())[k]!)[165 + l]! - 165]!) ∧
    (∀ q ∈ burnsideF48t_u52LnPts[((burnsideF48t_u52Gens ())[k]!)[165 + l]! - 165]!,
      ∃ p ∈ burnsideF48t_u52LnPts[l]!, ((burnsideF48t_u52Gens ())[k]!)[p]! = q) := by
  intro k hk l hl
  obtain ⟨h1, h2, hf, hb⟩ := genLn_spec ((gensK_spec gens_ok).2 k hk l hl)
  rw [g_get hk (by omega)]
  have hm : pg 9 (mask 9) (CX.S k) (165 + l) - 165 < 297 := by omega
  rw [lns_eq hl, lns_eq hm]
  obtain ⟨-, -, hlt⟩ := ln_inc hl
  refine ⟨h1, h2, fun p hp => ?_, fun q hq => ?_⟩
  · obtain ⟨a, ha, rfl⟩ := Array.mem_iff_getElem.1 hp
    have ha' : a < 5 := by simpa [unpack] using ha
    rw [← getElem!_pos _ a ha, unpack_f8 _ ha', g_get hk (by have := hlt a ha'; omega)]
    obtain ⟨b, hb5, eb⟩ := hf a ha'
    rw [← eb, ← unpack_f8 _ hb5, getElem!_pos _ b (by rw [unpack_size5]; exact hb5)]
    exact Array.getElem_mem _
  · obtain ⟨b, hb', rfl⟩ := Array.mem_iff_getElem.1 hq
    have hb5 : b < 5 := by simpa [unpack] using hb'
    obtain ⟨a, ha5, ea⟩ := hb b hb5
    refine ⟨f8 (LP l) a, ?_, ?_⟩
    · rw [← unpack_f8 _ ha5, getElem!_pos _ a (by rw [unpack_size5]; exact ha5)]
      exact Array.getElem_mem _
    · rw [g_get hk (by have := hlt a ha5; omega), ea, ← unpack_f8 _ hb5, getElem!_pos _ b hb']

theorem iso : ∀ k < 6, (∀ j < 5, (burnsideF48t_u52U[k]!)[j]! < 4) ∧
    burnsideF48t_u52Dot (burnsideF48t_u52Bar burnsideF48t_u52U[k]!) burnsideF48t_u52U[k]! = 0 := by
  intro k hk
  rw [u_eq hk]
  obtain ⟨-, hd⟩ := isoK_spec iso_ok hk
  exact ⟨fun j hj => by rw [unpack_f2 _ hj]; exact f2_lt _ _, by rw [dot_bar_eq, hd]⟩

end CFSG.KC.U52PL

end
