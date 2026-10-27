module

public import Certificates.Kernel.Tits8074.Data
public import Certificates.Kernel.Tits8074.Cent
public import Certificates.Kernel.Tits8074.Letters
public import Certificates.Kernel.Misc.Tits.Strong8077
public import Certificates.Certificate8077
public import CFSG.Certificates.Kernel.Tits8074Spec
public import CFSG.Quasithin.Recognition.CertTitsPair
public import CFSG.Certificates.SchreierChainOrder
public import CFSG.Certificates.SchreierChainOrderStabilizers
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelT8074

open CFSG.KC.Tits8074 CFSG.Quasithin CFSG.Certificates CFSG.Monster.B.Co2 Equiv
open CertificateChecks.KernelMisc

noncomputable abbrev P : Subgroup (Perm (Fin 1755)) := titsPairQ.originalSubgroup

@[expose] noncomputable def sg (k : Nat) : Perm (Fin 1755) := permOfArr 1755 titsPairStrong[k]!

@[expose] noncomputable def gl (c : Nat) : Perm (Fin 1755) :=
  if c % 2 = 0 then sg (c / 2) else (sg (c / 2))⁻¹

theorem L_eq (c : Nat) :
    L c = if c % 2 = 0 then TitsPCh.S (c / 2) else TitsPCh.SI (c / 2) := by
  unfold L
  have e1 : Nat.land c 1 = c % 2 := Nat.and_one_is_mod c
  have e2 : Nat.shiftRight c 1 = c / 2 := (Nat.shiftRight_eq_div_pow c 1).trans (by norm_num)
  rw [e1, e2]
  rcases Nat.mod_two_eq_zero_or_one c with h | h
  · rw [h, if_pos rfl]
    rfl
  · rw [h, if_neg (by decide)]
    rfl

theorem prep_sg {j : Nat} (hj : j < 12) :
    CFSG.KS.Raw.Orb.PRep 1755 11 (TitsPCh.S j) (sg j) ∧
      CFSG.KS.Raw.Orb.PRep 1755 11 (TitsPCh.SI j) (sg j)⁻¹ :=
  CFSG.KS.Raw.Orb.prep_PS CertificateChecks.TitsStrong8077.binds TitsPrim8077.perms hj

theorem xor_div : ∀ c < 24, Nat.xor c 1 / 2 = c / 2 ∧ (Nat.xor c 1 % 2 = 0 ↔ ¬ c % 2 = 0) := by
  decide

theorem hL : LRep L gl := by
  refine ⟨fun c hc x => ?_, fun c hc => ?_⟩
  · have hc2 : c / 2 < 12 := by omega
    unfold ap
    rw [L_eq]
    unfold gl
    split_ifs
    · exact (prep_sg hc2).1 x
    · exact (prep_sg hc2).2 x
  · obtain ⟨h1, h2⟩ := xor_div c hc
    unfold gl
    rw [h1]
    by_cases h : c % 2 = 0
    · rw [if_neg (fun h' => (h2.1 h') h), if_pos h]
    · rw [if_pos (h2.2 h), if_neg h, inv_inv]

theorem sg_mem {k : Nat} (hk : k < 12) : sg k ∈ P := by
  have h : sg k ∈ titsPairQ.strong.toList := by
    change sg k ∈ (Vector.ofFn fun j : Fin titsPairStrong.size =>
      permOfArr 1755 titsPairStrong[(j : ℕ)]!).toList
    rw [Vector.toList_ofFn, List.mem_ofFn]
    exact ⟨⟨k, by rw [CertificateChecks.TitsStrong8077.strong_get.1]; exact hk⟩, rfl⟩
  have e : P = titsPairQ.levelSubgroup 0 :=
    (titsPairQ.levelSubgroup_zero_eq_original titsPairQ_valid).symm
  rw [e]
  exact Subgroup.subset_closure (by rw [Set.mem_setOf_eq, RawSchreierDatum.levelGenerators_zero]; exact h)

theorem gl_mem {c : Nat} (hc : c < 24) : gl c ∈ P := by
  unfold gl
  split_ifs
  · exact sg_mem (by omega)
  · exact P.inv_mem (sg_mem (by omega))

theorem wv_mem : ∀ {w : List Nat}, (∀ c ∈ w, c < 24) → wv gl w ∈ P
  | [], _ => by rw [wv_nil]; exact P.one_mem
  | c :: w, hw => by
    rw [wv_cons]
    exact P.mul_mem (gl_mem (hw c (List.mem_cons_self ..)))
      (wv_mem fun d hd => hw d (List.mem_cons_of_mem c hd))

theorem gl_zero : gl 0 = titsPermA := by
  change permOfArr 1755 titsPairStrong[0]! = _
  rw [titsPairStrong_zero]
  rfl

theorem gl_two : gl 2 = titsPermB := by
  change permOfArr 1755 titsPairStrong[1]! = _
  rw [titsPairStrong_one]
  rfl

theorem bs_lt : ∀ p ∈ bs, p < 1755 := by decide

theorem codes_of : ∀ c < 24, c ∈ codes := by decide

theorem eq_of_base {x y : Perm (Fin 1755)} (hx : x ∈ P) (hy : y ∈ P)
    (h : ∀ q : Fin 1755, (q : ℕ) ∈ bs → x q = y q) : x = y := by
  have := titsPair_baseFaithful (x⁻¹ * y) (P.mul_mem (P.inv_mem hx) hy) (fun q hq => by
    rw [Perm.mul_apply, ← h q hq]
    exact Perm.inv_eq_iff_eq.2 rfl)
  exact inv_mul_eq_one.1 this

theorem lw_spec {w : List Nat} (h : lw w = true) : ∀ c ∈ w, c < 24 :=
  fun c hc => Nat.le_of_ble_eq_true (allL_spec h c hc)

theorem lws_spec {W : List (List Nat)} (h : lws W = true) : ∀ u ∈ W, ∀ c ∈ u, c < 24 :=
  fun u hu => lw_spec (allL_spec h u hu)

theorem ws_facts : (∀ c ∈ aw, c < 24) ∧ (∀ u ∈ r2, ∀ c ∈ u, c < 24) ∧
    (∀ u ∈ r3, ∀ c ∈ u, c < 24) ∧ (∀ u ∈ r4, ∀ c ∈ u, c < 24) ∧ (∀ u ∈ r5, ∀ c ∈ u, c < 24) ∧
    (∀ u ∈ r6, ∀ c ∈ u, c < 24) ∧ (∀ u ∈ hw, ∀ c ∈ u, c < 24) ∧ (∀ u ∈ tg, ∀ c ∈ u, c < 24) ∧
    (∀ u ∈ cw, ∀ c ∈ u, c < 24) ∧ zc < 24 ∧ sc < 24 := by
  have h := ws
  simp only [band_true] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
  exact ⟨lw_spec h1, lws_spec h2, lws_spec h3, lws_spec h4, lws_spec h5, lws_spec h6,
    lws_spec h7, lws_spec h8, lws_spec h9, Nat.le_of_ble_eq_true h10, Nat.le_of_ble_eq_true h11⟩

theorem ap_fin {c : Nat} (hc : c < 24) (q : Fin 1755) : ap L c q = (gl c q : ℕ) := hL.1 c hc q

theorem ev_fin {w : List Nat} (hw : ∀ c ∈ w, c < 24) (q : Fin 1755) :
    ev L w q = (wv gl w q : ℕ) := ev_eq hL w hw q

theorem base_take (i : Nat) (q : Fin 1755) :
    q ∈ titsPairQ.base.toList.take i ↔ (q : ℕ) ∈ bs.take i := by
  have e : bs.take i = (titsPairQ.base.toList.take i).map Fin.val := by
    rw [List.map_take, titsPairQ_base]
    rfl
  rw [e]
  exact (List.mem_map_of_injective Fin.val_injective).symm

theorem level_mem_iff {i : Nat} (hi : i ≤ 7) (g : Perm (Fin 1755)) :
    g ∈ titsPairQ.levelSubgroup i ↔ g ∈ P ∧ ∀ q : Fin 1755, (q : ℕ) ∈ bs.take i → g q = q := by
  rw [titsPairQ.levelSubgroup_eq_pointwise_stabilizer titsPairQ_valid i hi, Subgroup.mem_inf,
    mem_fixingSubgroup_iff]
  refine and_congr Iff.rfl ⟨fun h q hq => h q ((base_take i q).2 hq), fun h q hq => ?_⟩
  exact h q ((base_take i q).1 hq)

theorem level_gen {i : Nat} {s : Perm (Fin 1755)} (hs : s ∈ titsPairQ.levelGenerators i) :
    ∃ c < 24, gl c = s ∧ ∀ q : Fin 1755, (q : ℕ) ∈ bs.take i → s q = q := by
  obtain ⟨hs1, hs2⟩ := (titsPairQ.mem_levelGenerators_iff i s).1 hs
  change s ∈ (Vector.ofFn fun j : Fin titsPairStrong.size =>
    permOfArr 1755 titsPairStrong[(j : ℕ)]!).toList at hs1
  rw [Vector.toList_ofFn, List.mem_ofFn] at hs1
  obtain ⟨⟨j, hj⟩, rfl⟩ := hs1
  rw [CertificateChecks.TitsStrong8077.strong_get.1] at hj
  refine ⟨2 * j, by omega, ?_, fun q hq => hs2 q ((base_take i q).2 hq)⟩
  unfold gl
  rw [if_pos (by omega), show 2 * j / 2 = j by omega]
  rfl

theorem fix_nat {c : Nat} (hc : c < 24) {pre : List Nat} (hpre : ∀ p ∈ pre, p < 1755)
    (h : ∀ q : Fin 1755, (q : ℕ) ∈ pre → gl c q = q) : ∀ p ∈ pre, ap L c p = p := by
  intro p hp
  have := ap_fin hc ⟨p, hpre p hp⟩
  rw [h ⟨p, hpre p hp⟩ hp] at this
  exact this

theorem fix_fin {c : Nat} (hc : c < 24) {pre : List Nat} (h : ∀ p ∈ pre, ap L c p = p) :
    ∀ q : Fin 1755, (q : ℕ) ∈ pre → gl c q = q := by
  intro q hq
  apply Fin.ext
  rw [← ap_fin hc q]
  exact h q hq

theorem wv_fix {pre : List Nat} : ∀ {u : List Nat}, (∀ c ∈ u, c < 24) →
    (∀ c ∈ u, ∀ p ∈ pre, ap L c p = p) → ∀ q : Fin 1755, (q : ℕ) ∈ pre → wv gl u q = q
  | [], _, _, q, _ => by rw [wv_nil, Perm.one_apply]
  | c :: u, hu, hf, q, hq => by
    rw [wv_cons, Perm.mul_apply,
      wv_fix (fun d hd => hu d (List.mem_cons_of_mem c hd))
        (fun d hd => hf d (List.mem_cons_of_mem c hd)) q hq]
    exact fix_fin (hu c (List.mem_cons_self ..)) (hf c (List.mem_cons_self ..)) q hq

theorem inv_maps {O : Set (Fin 1755)} {g : Perm (Fin 1755)} (h : ∀ x ∈ O, g x ∈ O) :
    ∀ x ∈ O, g⁻¹ x ∈ O := by
  intro x hx
  have hb := ((Set.toFinite O).injOn_iff_bijOn_of_mapsTo (f := g) h).1 (g.injective.injOn)
  obtain ⟨y, hy, e⟩ := hb.surjOn hx
  have e' : g⁻¹ (g y) = y := Perm.inv_eq_iff_eq.2 rfl
  rw [← e, e']
  exact hy

theorem cover_step {i : Nat} (hi : i < 7) {R : List (List Nat)} {bp : Fin 1755}
    (hbp : bs.take (i + 1) = bs.take i ++ [(bp : ℕ)]) (hR : orbK L R (bs.take i) bp = true)
    (hRl : ∀ u ∈ R, ∀ c ∈ u, c < 24) (h1 : [] ∈ R) {g : Perm (Fin 1755)}
    (hg : g ∈ titsPairQ.levelSubgroup i) :
    ∃ u ∈ R, wv gl u ∈ titsPairQ.levelSubgroup i ∧
      (wv gl u)⁻¹ * g ∈ titsPairQ.levelSubgroup (i + 1) := by
  have hpre : ∀ p ∈ bs.take i, p < 1755 := fun p hp => bs_lt p (List.mem_of_mem_take hp)
  obtain ⟨hR1, hR2⟩ := orbK_spec hR
  let O : Set (Fin 1755) := {x | ∃ u ∈ R, (x : ℕ) = ev L u bp}
  have hgen : ∀ s ∈ titsPairQ.levelGenerators i, ∀ x ∈ O, s x ∈ O := by
    intro s hs x ⟨u, hu, hx⟩
    obtain ⟨c, hc, rfl, hfix⟩ := level_gen hs
    obtain ⟨v, hv, e⟩ := hR2 u hu c (codes_of c hc) (fix_nat hc hpre hfix)
    exact ⟨v, hv, by rw [← ap_fin hc, hx, e]⟩
  have hall : ∀ x ∈ O, g x ∈ O := by
    induction hg using Subgroup.closure_induction with
    | mem s hs => exact hgen s hs
    | one => exact fun x hx => hx
    | mul a b _ _ ha hb => exact fun x hx => ha _ (hb x hx)
    | inv a _ ha => exact inv_maps ha
  obtain ⟨u, hu, e⟩ := hall bp ⟨[], h1, rfl⟩
  have hgu : g bp = wv gl u bp := Fin.ext (by rw [e, ev_fin (hRl u hu)])
  have hwu : wv gl u ∈ titsPairQ.levelSubgroup i :=
    (level_mem_iff (by omega) _).2 ⟨wv_mem (hRl u hu), wv_fix (hRl u hu) (hR1 u hu)⟩
  refine ⟨u, hu, hwu, (level_mem_iff (by omega) _).2 ⟨P.mul_mem (P.inv_mem
    ((level_mem_iff (by omega) _).1 hwu).1) ((level_mem_iff (by omega) _).1 hg).1, ?_⟩⟩
  intro q hq
  rw [hbp, List.mem_append, List.mem_singleton] at hq
  rw [Perm.mul_apply, Perm.inv_eq_iff_eq]
  rcases hq with hq | hq
  · rw [((level_mem_iff (by omega) _).1 hg).2 q hq, ((level_mem_iff (by omega) _).1 hwu).2 q hq]
  · rw [show q = bp from Fin.ext hq, hgu]

theorem r_nil : [] ∈ r2 ∧ [] ∈ r3 ∧ [] ∈ r4 ∧ [] ∈ r5 ∧ [] ∈ r6 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> exact List.mem_of_getElem? (i := 0) (by rfl)

theorem cover {g : Perm (Fin 1755)} (hg : g ∈ titsPairQ.levelSubgroup 2) :
    ∃ u₂ ∈ r2, ∃ u₃ ∈ r3, ∃ u₄ ∈ r4, ∃ u₅ ∈ r5, ∃ u₆ ∈ r6,
      g = wv gl u₂ * wv gl u₃ * wv gl u₄ * wv gl u₅ * wv gl u₆ := by
  obtain ⟨-, l2, l3, l4, l5, l6, -, -, -, -, -⟩ := ws_facts
  obtain ⟨n2, n3, n4, n5, n6⟩ := r_nil
  obtain ⟨u₂, h₂, -, g3⟩ := cover_step (bp := 1) (by norm_num) rfl orb2 l2 n2 hg
  obtain ⟨u₃, h₃, -, g4⟩ := cover_step (bp := 5) (by norm_num) rfl orb3 l3 n3 g3
  obtain ⟨u₄, h₄, -, g5⟩ := cover_step (bp := 6) (by norm_num) rfl orb4 l4 n4 g4
  obtain ⟨u₅, h₅, -, g6⟩ := cover_step (bp := 12) (by norm_num) rfl orb5 l5 n5 g5
  obtain ⟨u₆, h₆, -, g7⟩ := cover_step (bp := 24) (by norm_num) rfl orb6 l6 n6 g6
  have h7 : titsPairQ.levelSubgroup 7 = ⊥ := titsPairQ.levelSubgroup_terminal_eq_bot titsPairQ_valid
  rw [h7, Subgroup.mem_bot] at g7
  refine ⟨u₂, h₂, u₃, h₃, u₄, h₄, u₅, h₅, u₆, h₆, ?_⟩
  have e1 := inv_mul_eq_one.1 g7
  have e2 := inv_mul_eq_iff_eq_mul.1 e1.symm
  have e3 := inv_mul_eq_iff_eq_mul.1 e2
  have e4 := inv_mul_eq_iff_eq_mul.1 e3
  have e5 := inv_mul_eq_iff_eq_mul.1 e4
  rw [e5]
  group

theorem card_level2 : Nat.card (titsPairQ.levelSubgroup 2) = 1024 := by
  rw [titsPairQ.level_card_eq_orbit_product titsPairQ_valid 2 (by decide)]
  have e : ((List.finRange titsPairQ.baseCount).drop 2).map
      (fun j => Nat.card (titsPairQ.orbitPoints j)) =
      ((List.finRange titsPairQ.baseCount).drop 2).map
        (fun j => [1755, 10, 8, 2, 8, 4, 2].getD j.val 0) := by
    refine List.map_congr_left fun j _ => ?_
    rw [← titsPairQ.orbitSize_eq_card, titsPairQ_orbitSize]
  rw [e]
  decide

end CertificateChecks.KernelT8074

end
