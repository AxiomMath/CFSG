module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SporadicPermutesPackage
public import CFSG.Sporadic.Fi23.Classes
public import CFSG.Certificates.Kernel.Fi23Nine.Sound
public import Certificates.Kernel.Fi23Nine.For
public import Certificates.Kernel.Fi23Nine.Chk
public import Certificates.Kernel.Fi23Cov.Words
public import Certificates.Kernel.Fi23S.Letters

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelFi23Nine

open scoped Pointwise
open CFSG.Sporadic.Fi23 CFSG.Sporadic.Th CFSG.Perm CFSG.KC.Fi23K CFSG.KC.Fi23Nine
open CFSG.Sporadic.Fi23.Native CFSG.Sporadic.Th.Native CFSG.Perm.Native
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.KD.Fi23Nine (spD sp lgF_ok spF_ok eF_ok fF_ok xyF_ok okE)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

noncomputable abbrev DD : ℕ → ℕ := CFSG.KD.Fi23Nine.D

noncomputable abbrev GG : ℕ → ℕ := CFSG.KD.Fi23K.G

noncomputable abbrev HH : ℕ → ℕ := CFSG.KD.Fi23S.H

noncomputable abbrev rZ : ℤ → ℕ := CFSG.KD.Fi23Nine.regZ

theorem LS_eq : LS = sylLetters (chainLetters CFSG.KD.Fi23K.orbLit) := by
  change sylLetters (chainLetters orb) = _
  rw [CFSG.KD.Fi23Cov.orb_eq]

theorem LS_size' : LS.size = 42 := by
  rw [LS_eq]
  exact CertificateChecks.KernelFi23S.syl_TR.1

theorem tb_syl {l : ℕ} (hl : l < 42) {x : ℕ} (hx : x < 31671) :
    tb HH l x = idx 31671 (pairG sylG l) x := by
  have h1 := ((CertificateChecks.KernelFi23S.syl_TR.2 l hl).2 x hx).1
  have h2 := rep_LS_all l (by rw [LS_size']; exact hl) x hx
  rw [LS_eq] at h2
  rw [← h2, h1]
  rfl

theorem syl_mem {l : ℕ} (hl : l < 42) : pairG sylG l ∈ slvl 0 :=
  lG_mem (mem_levelLetters_zero.2 (by rw [LS_size']; exact hl))

theorem slvl_le {P : Subgroup J} (h : ∀ l < 42, pairG sylG l ∈ P) : slvl 0 ≤ P := by
  change Subgroup.closure _ ≤ P
  rw [Subgroup.closure_le]
  rintro _ ⟨l, hl, rfl⟩
  exact h l (by rw [← LS_size']; exact levelLetters_lt hl)

theorem wv_word : ∀ w : List ℤ, (∀ z ∈ w, z.toNat < 24) → ∀ x < 31671,
    wv GG (w.map rZ) x = idx 31671 (wordG jG w) x
  | [], _, x, _ => by
    rw [List.map_nil, wv_nil]
    unfold wordG
    rw [List.map_nil, List.prod_nil, idx_one]
  | z :: w, h, x, hx => by
    have hz := h z List.mem_cons_self
    have hw : ∀ z ∈ w, z.toNat < 24 := fun z' hz' => h z' (List.mem_cons_of_mem z hz')
    rw [List.map_cons, wv_cons, wv_word w hw x hx]
    have e : wordG jG (z :: w) = jG z * wordG jG w := by
      unfold wordG
      rw [List.map_cons, List.prod_cons]
    rw [e, idx_mul]
    exact CFSG.KD.Fi23Cov.tb_chain hz (idx_lt _ hx)

theorem wl_facts : (∀ z ∈ nineCWord, z.toNat < 24) ∧ (∀ z ∈ nineXWord, z.toNat < 24) ∧
    (∀ z ∈ nineYWord, z.toNat < 24) ∧ ∀ j < 3, ∀ z ∈ nineHWords.toList.getD j [], z.toNat < 24 := by
  decide +kernel

theorem idx_inv_idx (g : J) {x : ℕ} : idx 31671 g⁻¹ (idx 31671 g x) = x := by
  rw [← idx_mul, inv_mul_cancel, idx_one]

theorem eq_of_idx {g : J} {p q : Fin 31671} (h : idx 31671 g p.val = q.val) : g • p = q :=
  Fin.ext (by rw [smul_val_eq_idx]; exact h)

theorem eq_one_of_base {g : J} (h : ∀ b < 6, idx 31671 g b = b) : g = 1 := by
  apply sep
  intro t ht
  have hs : chainQ.size = 6 := rfl
  rw [hs] at ht
  have e : chainQ[t]! = t := by
    interval_cases t <;> rfl
  rw [e]
  exact h t ht

theorem forAt_all {q : ℕ} (hq : q < 31671) : forAt HH DD q = true := by
  have key : ∀ s < 8, CFSG.KD.Fi23Nine.forF s = true := by
    intro s hs
    interval_cases s
    exacts [CFSG.KD.Fi23Nine.forF0, CFSG.KD.Fi23Nine.forF1, CFSG.KD.Fi23Nine.forF2,
      CFSG.KD.Fi23Nine.forF3, CFSG.KD.Fi23Nine.forF4, CFSG.KD.Fi23Nine.forF5,
      CFSG.KD.Fi23Nine.forF6, CFSG.KD.Fi23Nine.forF7]
  have h : forSl HH DD (q / 4096 * 4096) 4096 = true := key (q / 4096) (by omega)
  exact forSl_spec h (by omega) (by omega) hq

theorem spF_facts : cK GG DD (nineCWord.map rZ) sp = true ∧ spD 0 = spD 21 ∧ spD 1 = spD 22 ∧
    spD 2 = spD 24 ∧ rootOf (fD DD 0 (spD 23)) = 1 ∧
    (∀ j < 4, rootOf (fD DD 0 (spD (24 + j))) = 2) ∧ clK HH [spD 21] = true ∧
    clK HH [spD 22, spD 23] = true ∧ clK HH [spD 24, spD 25, spD 26, spD 27] = true := by
  have h := spF_ok
  unfold CFSG.KD.Fi23Nine.spF at h
  simp only [CFSG.KS.Raw.Orb.bAnd_eq, Bool.and_eq_true] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  exact ⟨h1, beq_true h2, beq_true h3, beq_true h4, beq_true h5,
    fun j hj => beq_true (CFSG.KS.Raw.Orb.allN_iff.1 h6 j hj), h7, h8, h9⟩

theorem okE_spec {z : ℕ} (h : okE z = true) :
    z < 24 ∧ tb GG (52 + z) 0 = 0 ∧ tb GG (52 + z) 1 = 1 := by
  unfold okE at h
  simp only [CFSG.KS.Raw.Orb.bAnd_eq, Bool.and_eq_true] at h
  exact ⟨blt_true h.1, beq_true h.2.1, beq_true h.2.2⟩

theorem eF_facts :
    trK (fun z x => tb GG (52 + z) x) okE DD 995 nineE 693 = true ∧ srtK DD 995 1017 693 = true := by
  have h := eF_ok
  unfold CFSG.KD.Fi23Nine.eF at h
  rw [CFSG.KS.Raw.Orb.bAnd_eq, Bool.and_eq_true] at h
  exact h

noncomputable abbrev hR (j : ℕ) : List ℕ := (nineHWords.toList.getD j []).map rZ

theorem fF_facts :
    (∀ j < 3, wv GG (hR j) 0 = 0 ∧ wv GG (hR j) 1 = 1 ∧ wv GG (hR j) nineE = nineE) ∧
    trK (fun j x => wv GG (hR j) x) (fun j => Nat.blt j 3) DD 1039 nineF 180 = true ∧
    srtK DD 1039 1045 180 = true := by
  have h := fF_ok
  unfold CFSG.KD.Fi23Nine.fF at h
  simp only [CFSG.KS.Raw.Orb.bAnd_eq, Bool.and_eq_true] at h
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun j hj => ?_, h2, h3⟩
  have h' := CFSG.KS.Raw.Orb.allN_iff.1 h1 j hj
  simp only [Bool.and_eq_true] at h'
  exact ⟨beq_true h'.1, beq_true h'.2.1, beq_true h'.2.2⟩

abbrev q0 : Fin 31671 := ⟨0, by norm_num⟩

abbrev q1 : Fin 31671 := ⟨1, by norm_num⟩

abbrev qe : Fin 31671 := ⟨28381, by norm_num⟩

abbrev qf : Fin 31671 := ⟨8514, by norm_num⟩

abbrev O2 : Finset (Fin 31671) := {q1, qe}

abbrev O4 : Finset (Fin 31671) :=
  {⟨8514, by norm_num⟩, ⟨12009, by norm_num⟩, ⟨15862, by norm_num⟩, ⟨20635, by norm_num⟩}

theorem mem_O2 {p : Fin 31671} : p ∈ O2 ↔ p.val ∈ [1, nineE] := by
  simp [O2, nineE, Fin.ext_iff]

theorem mem_O4 {p : Fin 31671} : p ∈ O4 ↔ p.val ∈ nineO4 := by
  simp [O4, nineO4, Fin.ext_iff]

theorem card_O2 : O2.card = 2 := by decide

theorem card_O4 : O4.card = 4 := by decide

theorem q0_notMem_O2 : q0 ∉ O2 := by decide

theorem q0_notMem_O4 : q0 ∉ O4 := by decide

theorem O4_notMem_O2 : ∀ p ∈ O4, p ∉ O2 := by
  intro p hp
  simp only [O4, Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl <;> decide

theorem q1_mem_O2 : q1 ∈ O2 := by decide

theorem qe_mem_O2 : qe ∈ O2 := by decide

theorem qf_mem_O4 : qf ∈ O4 := by decide

theorem q1_ne_qe : q1 ≠ qe := by decide

noncomputable abbrev cE : J := wordG jG nineCWord

theorem c_pt (j : ℕ) (hj : j < 7) {p : ℕ} (hp : ∀ h : j < sp.length, sp[j] = p) (hp' : p < 31671) :
    (cE • (⟨p, hp'⟩ : Fin 31671)).val = spD (21 + j) := by
  have hl : j < sp.length := hj
  rw [smul_val_eq_idx, ← wv_word nineCWord wl_facts.1 p hp', ← hp hl]
  exact cK_spec spF_facts.1 j hl

theorem c_q0 : (cE • q0).val = spD 21 := c_pt 0 (by norm_num) (fun _ => rfl) _
theorem c_q1 : (cE • q1).val = spD 22 := c_pt 1 (by norm_num) (fun _ => rfl) _
theorem c_qe : (cE • qe).val = spD 23 := c_pt 2 (by norm_num) (fun _ => rfl) _
theorem c_f0 : (cE • (⟨8514, by norm_num⟩ : Fin 31671)).val = spD 24 :=
  c_pt 3 (by norm_num) (fun _ => rfl) _
theorem c_f1 : (cE • (⟨12009, by norm_num⟩ : Fin 31671)).val = spD 25 :=
  c_pt 4 (by norm_num) (fun _ => rfl) _
theorem c_f2 : (cE • (⟨15862, by norm_num⟩ : Fin 31671)).val = spD 26 :=
  c_pt 5 (by norm_num) (fun _ => rfl) _
theorem c_f3 : (cE • (⟨20635, by norm_num⟩ : Fin 31671)).val = spD 27 :=
  c_pt 6 (by norm_num) (fun _ => rfl) _

theorem forest : ∀ (d q : ℕ) (hq : q < 31671), depOf (fD DD 0 q) = d → ∀ i,
    rootOf (fD DD 0 q) = i → ∃ hr : spD i < 31671, ∃ g ∈ slvl 0,
      g • (⟨spD i, hr⟩ : Fin 31671) = ⟨q, hq⟩
  | 0, q, hq, hd, i, hi => by
    have h := (forAt_spec (forAt_all hq)).2.1 hd
    rw [hi] at h
    have hr : spD i < 31671 := by
      change fD DD 1051 i < 31671
      rw [← h]
      exact hq
    refine ⟨hr, 1, Subgroup.one_mem _, ?_⟩
    rw [one_smul]
    exact Fin.ext h.symm
  | d + 1, q, hq, hd, i, hi => by
    obtain ⟨hl, hp, he, hr, hdp⟩ := (forAt_spec (forAt_all hq)).2.2 (by rw [hd]; omega)
    obtain ⟨hr', g, hg, hgq⟩ := forest d _ hp (by rw [hdp, hd]; omega) i (hr.trans hi)
    refine ⟨hr', pairG sylG (letOf (fD DD 0 q)) * g, Subgroup.mul_mem _ (syl_mem hl) hg, ?_⟩
    rw [mul_smul, hgq]
    apply eq_of_idx
    rw [← tb_syl hl hp]
    exact he

theorem mem_orbit_root (q : Fin 31671) :
    ∃ hr : spD (rootOf (fD DD 0 q.val)) < 31671,
      q ∈ MulAction.orbit (slvl 0) (⟨spD (rootOf (fD DD 0 q.val)), hr⟩ : Fin 31671) := by
  obtain ⟨hr, g, hg, h⟩ := forest _ q.val q.isLt rfl _ rfl
  exact ⟨hr, ⟨g, hg⟩, h⟩

theorem same_root {p q : Fin 31671} (h : rootOf (fD DD 0 p.val) = rootOf (fD DD 0 q.val)) :
    p ∈ MulAction.orbit (slvl 0) q := by
  obtain ⟨hp, mp⟩ := mem_orbit_root p
  obtain ⟨hq, mq⟩ := mem_orbit_root q
  have e : (⟨spD (rootOf (fD DD 0 p.val)), hp⟩ : Fin 31671) =
      ⟨spD (rootOf (fD DD 0 q.val)), hq⟩ := Fin.ext (congrArg spD h)
  rw [MulAction.orbit_eq_iff.2 mq, ← e]
  exact mp

theorem mem_root {q : Fin 31671} {r : Fin 31671} (h : spD (rootOf (fD DD 0 q.val)) = r.val) :
    q ∈ MulAction.orbit (slvl 0) r := by
  obtain ⟨hp, mp⟩ := mem_orbit_root q
  have e : (⟨spD (rootOf (fD DD 0 q.val)), hp⟩ : Fin 31671) = r := Fin.ext h
  rw [← e]
  exact mp

theorem le_card_of_incr {S : Set (Fin 31671)} {m : ℕ} (f : ℕ → ℕ) (hlt : ∀ j < m, f j < 31671)
    (hinc : ∀ j, j + 1 < m → f j < f (j + 1))
    (hmem : ∀ j (hj : j < m), (⟨f j, hlt j hj⟩ : Fin 31671) ∈ S) : m ≤ Nat.card S := by
  have hmono : ∀ i j, i < j → j < m → f i < f j := by
    intro i j hij hj
    induction j with
    | zero => omega
    | succ j ih =>
      rcases Nat.lt_succ_iff_lt_or_eq.1 hij with h | rfl
      · exact lt_trans (ih h (by omega)) (hinc j hj)
      · exact hinc i hj
  let F : Fin m → S := fun j => ⟨⟨f j, hlt j j.2⟩, hmem j j.2⟩
  have hF : Function.Injective F := by
    intro a b hab
    have e : f a = f b := congrArg (fun x : S => x.1.val) hab
    by_contra hne
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with h | h
    · exact absurd e (ne_of_lt (hmono _ _ h b.2))
    · exact absurd e (ne_of_gt (hmono _ _ h a.2))
  have := Nat.card_le_card_of_injective F hF
  simpa using this

theorem eight_le (q : Fin 31671) (h3 : 3 ≤ rootOf (fD DD 0 q.val)) :
    8 ≤ Nat.card (MulAction.orbit (slvl 0) q) := by
  have hi21 : rootOf (fD DD 0 q.val) < 21 := (forAt_spec (forAt_all q.isLt)).1
  have hlg := fun {k} (hk : k < 144) => lgK_spec lgF_ok hk
  refine le_card_of_incr (fun j => fD DD 990 (8 * (rootOf (fD DD 0 q.val) - 3) + j))
    (fun j hj => (hlg (by omega)).1) (fun j hj => (hlg (by omega)).2.2 (by omega))
    (fun j hj => same_root ?_)
  rw [(hlg (by omega)).2.1]
  omega

noncomputable abbrev uSyl : Subgroup J := (slvl 0).map (MulAut.conj cE⁻¹).toMonoidHom

theorem conj_smul (t : J) (p : Fin 31671) :
    (MulAut.conj cE⁻¹).toMonoidHom t • p = cE⁻¹ • t • cE • p := by
  change (MulAut.conj cE⁻¹) t • p = _
  rw [MulAut.conj_apply, inv_inv, mul_smul, mul_smul]

theorem mem_orbitU {p x : Fin 31671} :
    x ∈ MulAction.orbit uSyl p ↔ cE • x ∈ MulAction.orbit (slvl 0) (cE • p) := by
  constructor
  · rintro ⟨⟨u, hu⟩, rfl⟩
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.1 hu
    refine ⟨⟨t, ht⟩, ?_⟩
    change t • cE • p = cE • ((MulAut.conj cE⁻¹).toMonoidHom t • p)
    rw [conj_smul, smul_inv_smul]
  · rintro ⟨⟨t, ht⟩, h⟩
    refine ⟨⟨(MulAut.conj cE⁻¹).toMonoidHom t, Subgroup.mem_map_of_mem _ ht⟩, ?_⟩
    change (MulAut.conj cE⁻¹).toMonoidHom t • p = x
    change t • cE • p = cE • x at h
    rw [conj_smul, h, inv_smul_smul]

theorem card_orbitU (p : Fin 31671) :
    Nat.card (MulAction.orbit uSyl p) = Nat.card (MulAction.orbit (slvl 0) (cE • p)) :=
  Nat.card_congr ((MulAction.toPerm cE : Equiv.Perm (Fin 31671)).subtypeEquiv fun _ => mem_orbitU)

theorem card_uSyl : Nat.card uSyl = 262144 := by
  rw [Subgroup.card_map_of_injective (by exact (MulAut.conj cE⁻¹).injective), card_slvl_zero]

theorem isSylowTwoOf_uSyl :
    CFSG.QuasithinUnique.IsSylowTwoOf uSyl ⊤ := by
  refine ⟨le_top, IsPGroup.of_card (n := 18) (by rw [card_uSyl]; norm_num), ?_⟩
  have hc : Nat.card (uSyl.subgroupOf ⊤) = Nat.card uSyl :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_top : uSyl ≤ ⊤)).toEquiv
  have hmul : Nat.card (uSyl.subgroupOf ⊤) * (uSyl.subgroupOf ⊤).index =
      Nat.card (⊤ : Subgroup J) := Subgroup.card_mul_index (H := uSyl.subgroupOf ⊤)
  rw [Subgroup.card_top, hc, card_uSyl, card_J] at hmul
  have hidx : (uSyl.subgroupOf ⊤).index = 15600091832325 := by omega
  rw [hidx]
  norm_num

theorem smul_eq_of_subset {g : J} {F : Finset (Fin 31671)}
    (h : ∀ a ∈ F, g • a ∈ F) : g • F = F :=
  Finset.eq_of_subset_of_card_le (fun b hb => by
    obtain ⟨a, ha, rfl⟩ := Finset.mem_smul_finset.1 hb
    exact h a ha) (by rw [Finset.card_smul_finset])

theorem stabT {L : List ℕ} (hL : clK HH L = true) {S : Finset (Fin 31671)}
    (hS : ∀ a : Fin 31671, a ∈ S ↔ a.val ∈ L) : ∀ t ∈ slvl 0, t • S = S := by
  have hle : slvl 0 ≤ MulAction.stabilizer J S := slvl_le fun l hl => by
    rw [MulAction.mem_stabilizer_iff]
    refine smul_eq_of_subset fun a ha => ?_
    rw [hS] at ha ⊢
    rw [smul_val_eq_idx, ← tb_syl hl a.isLt]
    exact (clK_iff _ _).1 hL l hl _ ha
  exact fun t ht => MulAction.mem_stabilizer_iff.1 (hle ht)

theorem stab_c {L : List ℕ} (hL : clK HH L = true) {F : Finset (Fin 31671)}
    (hF : ∀ a : Fin 31671, a ∈ cE • F ↔ a.val ∈ L) : ∀ u ∈ uSyl, u • F = F := by
  intro u hu
  obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.1 hu
  have h := stabT hL hF t ht
  change (MulAut.conj cE⁻¹) t • F = F
  rw [MulAut.conj_apply, inv_inv, mul_smul, mul_smul, h, inv_smul_smul]

theorem orbitT_sub {L : List ℕ} (hL : clK HH L = true) {S : Finset (Fin 31671)}
    (hS : ∀ a : Fin 31671, a ∈ S ↔ a.val ∈ L) {s x : Fin 31671} (hs : s ∈ S)
    (hx : x ∈ MulAction.orbit (slvl 0) s) : x ∈ S := by
  obtain ⟨⟨t, ht⟩, rfl⟩ := hx
  have h := stabT hL hS t ht
  change t • s ∈ S
  rw [← h]
  exact Finset.smul_mem_smul_finset hs

theorem cS0 (a : Fin 31671) : a ∈ cE • ({q0} : Finset (Fin 31671)) ↔ a.val ∈ [spD 21] := by
  rw [Finset.smul_finset_singleton, Finset.mem_singleton, Fin.ext_iff, c_q0, List.mem_singleton]

theorem cS2 (a : Fin 31671) : a ∈ cE • O2 ↔ a.val ∈ [spD 22, spD 23] := by
  rw [Finset.smul_finset_insert, Finset.smul_finset_singleton, Finset.mem_insert,
    Finset.mem_singleton, Fin.ext_iff, Fin.ext_iff, c_q1, c_qe]
  simp

theorem cS4 (a : Fin 31671) : a ∈ cE • O4 ↔ a.val ∈ [spD 24, spD 25, spD 26, spD 27] := by
  rw [Finset.smul_finset_insert, Finset.smul_finset_insert, Finset.smul_finset_insert,
    Finset.smul_finset_singleton, Finset.mem_insert, Finset.mem_insert, Finset.mem_insert,
    Finset.mem_singleton, Fin.ext_iff, Fin.ext_iff, Fin.ext_iff, Fin.ext_iff, c_f0, c_f1, c_f2,
    c_f3]
  simp

theorem le_card_orbit {K : Subgroup J} {x : Fin 31671} {F : Finset (Fin 31671)}
    (h : ∀ a ∈ F, a ∈ MulAction.orbit K x) : F.card ≤ Nat.card (MulAction.orbit K x) := by
  rw [Nat.card_coe_set_eq, ← Set.ncard_coe_finset]
  exact Set.ncard_le_ncard (fun a ha => h a ha) (Set.toFinite _)

theorem root_cO4 : ∀ b ∈ O4, rootOf (fD DD 0 (cE • b).val) = 2 := by
  have h := spF_facts.2.2.2.2.2.1
  intro b hb
  simp only [O4, Finset.mem_insert, Finset.mem_singleton] at hb
  rcases hb with rfl | rfl | rfl | rfl
  · rw [c_f0]
    exact h 0 (by norm_num)
  · rw [c_f1]
    exact h 1 (by norm_num)
  · rw [c_f2]
    exact h 2 (by norm_num)
  · rw [c_f3]
    exact h 3 (by norm_num)

theorem orbit_cases (p : Fin 31671) :
    p = q0 ∨ (p ∈ O2 ∧ 2 ≤ Nat.card (MulAction.orbit uSyl p)) ∨
      (p ∈ O4 ∧ 4 ≤ Nat.card (MulAction.orbit uSyl p)) ∨
      8 ≤ Nat.card (MulAction.orbit uSyl p) := by
  obtain ⟨f1, f2, f3, f4, f5, -, f7, f8, f9⟩ := spF_facts
  rw [card_orbitU]
  have hi21 : rootOf (fD DD 0 (cE • p).val) < 21 := (forAt_spec (forAt_all (cE • p).isLt)).1
  rcases (by omega : rootOf (fD DD 0 (cE • p).val) = 0 ∨ rootOf (fD DD 0 (cE • p).val) = 1 ∨
      rootOf (fD DD 0 (cE • p).val) = 2 ∨ 3 ≤ rootOf (fD DD 0 (cE • p).val)) with h | h | h | h
  · left
    have hm := mem_root (q := cE • p) (r := cE • q0) (by rw [h, c_q0, f2])
    have := orbitT_sub f7 cS0 (Finset.smul_mem_smul_finset (Finset.mem_singleton_self q0)) hm
    rw [Finset.smul_mem_smul_finset_iff, Finset.mem_singleton] at this
    exact this
  · right; left
    have hm := mem_root (q := cE • p) (r := cE • q1) (by rw [h, c_q1, f3])
    refine ⟨?_, ?_⟩
    · have := orbitT_sub f8 cS2 (Finset.smul_mem_smul_finset q1_mem_O2) hm
      exact (Finset.smul_mem_smul_finset_iff cE).1 this
    · rw [MulAction.orbit_eq_iff.2 hm, ← card_O2, ← Finset.card_smul_finset cE O2]
      refine le_card_orbit fun a ha => ?_
      obtain ⟨b, hb, rfl⟩ := Finset.mem_smul_finset.1 ha
      rcases Finset.mem_insert.1 hb with rfl | hb
      · exact MulAction.mem_orbit_self _
      · rw [Finset.mem_singleton.1 hb]
        exact mem_root (by rw [c_qe, f5, c_q1, f3])
  · right; right; left
    have hm := mem_root (q := cE • p) (r := cE • qf) (by rw [h, c_f0, f4])
    refine ⟨?_, ?_⟩
    · have := orbitT_sub f9 cS4 (Finset.smul_mem_smul_finset qf_mem_O4) hm
      exact (Finset.smul_mem_smul_finset_iff cE).1 this
    · rw [MulAction.orbit_eq_iff.2 hm, ← card_O4, ← Finset.card_smul_finset cE O4]
      refine le_card_orbit fun a ha => ?_
      obtain ⟨b, hb, rfl⟩ := Finset.mem_smul_finset.1 ha
      exact mem_root (by rw [root_cO4 b hb, c_f0, f4])
  · right; right; right
    exact eight_le _ h

theorem card_orbit_le_card {H : Subgroup J}
    {A : Finset (Fin 31671)} (hA : ∀ u ∈ H, u • A = A) {p : Fin 31671} (hp : p ∈ A) :
    Nat.card (MulAction.orbit H p) ≤ A.card := by
  rw [Nat.card_coe_set_eq, ← Set.ncard_coe_finset]
  refine Set.ncard_le_ncard ?_ (Set.toFinite _)
  rintro _ ⟨⟨u, hu⟩, rfl⟩
  have h : u • p ∈ u • A := Finset.smul_mem_smul_finset hp
  rw [hA u hu] at h
  exact h

theorem eq_q0_of_fixed {p : Fin 31671}
    (hp : ∀ u ∈ uSyl, u • p = p) : p = q0 := by
  have h1 : Nat.card (MulAction.orbit uSyl p) ≤ 1 := by
    have h := card_orbit_le_card (H := uSyl) (A := {p})
      (fun u hu => by rw [Finset.smul_finset_singleton, hp u hu]) (Finset.mem_singleton_self p)
    rwa [Finset.card_singleton] at h
  rcases orbit_cases p with h | ⟨-, h⟩ | ⟨-, h⟩ | h
  · exact h
  all_goals omega

theorem eq_O2 {A : Finset (Fin 31671)}
    (hA : ∀ u ∈ uSyl, u • A = A) (hc : A.card = 2) (h0 : q0 ∉ A) : A = O2 := by
  refine Finset.eq_of_subset_of_card_le (fun p hp => ?_) (by rw [hc, card_O2])
  have hle := card_orbit_le_card hA hp
  rcases orbit_cases p with h | ⟨h, -⟩ | ⟨-, h⟩ | h
  · subst h
    exact absurd hp h0
  · exact h
  all_goals omega

theorem eq_O4 {A : Finset (Fin 31671)}
    (hA : ∀ u ∈ uSyl, u • A = A) (hc : A.card = 4) (h0 : q0 ∉ A) (h2 : ∀ p ∈ A, p ∉ O2) :
    A = O4 := by
  refine Finset.eq_of_subset_of_card_le (fun p hp => ?_) (by rw [hc, card_O4])
  have hle := card_orbit_le_card hA hp
  rcases orbit_cases p with h | ⟨h, -⟩ | ⟨h, -⟩ | h
  · subst h
    exact absurd hp h0
  · exact absurd h (h2 p hp)
  · exact h
  · omega

abbrev x₀ : Fin 31671 × Finset (Fin 31671) × Finset (Fin 31671) := (q0, O2, O4)

theorem smul_x₀ (g : J) : g • x₀ = (g • q0, g • O2, g • O4) := rfl

theorem mem_stab_iff {g : J} :
    g ∈ MulAction.stabilizer J x₀ ↔ g • q0 = q0 ∧ g • O2 = O2 ∧ g • O4 = O4 := by
  rw [MulAction.mem_stabilizer_iff, smul_x₀, Prod.mk.injEq, Prod.mk.injEq]

theorem fix_x₀ : ∀ u ∈ uSyl, u • x₀ = x₀ := by
  obtain ⟨-, -, -, -, -, -, f7, f8, f9⟩ := spF_facts
  intro u hu
  rw [← MulAction.mem_stabilizer_iff, mem_stab_iff]
  refine ⟨?_, stab_c f8 cS2 u hu, stab_c f9 cS4 u hu⟩
  have h := stab_c f7 cS0 u hu
  rw [Finset.smul_finset_singleton, Finset.singleton_inj] at h
  exact h

theorem uniq_x₀ (d : J)
    (hd : ∀ u ∈ uSyl, u • (d • x₀) = d • x₀) : d • x₀ = x₀ := by
  have hd' : ∀ u ∈ uSyl, u • d • q0 = d • q0 ∧ u • d • O2 = d • O2 ∧ u • d • O4 = d • O4 := by
    intro u hu
    have h := hd u hu
    simp only [Prod.smul_mk, Prod.mk.injEq] at h
    exact h
  have h0 : d • q0 = q0 := eq_q0_of_fixed fun u hu => (hd' u hu).1
  have h0A : ∀ {F : Finset (Fin 31671)}, q0 ∉ F → q0 ∉ d • F := by
    intro F hF hmem
    rw [← h0, Finset.smul_mem_smul_finset_iff] at hmem
    exact hF hmem
  have h2 : d • O2 = O2 :=
    eq_O2 (fun u hu => (hd' u hu).2.1) (by rw [Finset.card_smul_finset, card_O2])
      (h0A q0_notMem_O2)
  have h4 : d • O4 = O4 := by
    refine eq_O4 (fun u hu => (hd' u hu).2.2) (by rw [Finset.card_smul_finset, card_O4])
      (h0A q0_notMem_O4) fun p hp hp2 => ?_
    obtain ⟨a, ha, rfl⟩ := Finset.mem_smul_finset.1 hp
    rw [← h2, Finset.smul_mem_smul_finset_iff] at hp2
    exact O4_notMem_O2 a ha hp2
  rw [smul_x₀, h0, h2, h4]

theorem card_lvl_two : Nat.card (lvl 2) = 36787322880 := by
  rw [chain_facts'.2.2 2 (by rw [chainBase_size]; norm_num), chainBase_size]
  rw [show Finset.Ico 2 6 = {2, 3, 4, 5} by decide]
  rw [Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_insert (by decide), Finset.prod_singleton,
    tree_size_of (l := 2) rfl, tree_size_of (l := 3) rfl, tree_size_of (l := 4) rfl,
    tree_size_of (l := 5) rfl]
  norm_num

theorem mem_lvl_two {g : J} (h0 : g • q0 = q0) (h1 : g • q1 = q1) : g ∈ lvl 2 := by
  have hl1 : g ∈ lvl 1 :=
    (lvl_one_iff g).1 (by rw [idx_of_lt g (by norm_num)]; exact congrArg Fin.val h0)
  exact (chain_facts'.2.1 1 (by rw [chainBase_size]; norm_num) g hl1).1
    (by rw [chainBase_one, idx_of_lt g (by norm_num)]; exact congrArg Fin.val h1)

theorem tree_mem {A : ℕ → ℕ → ℕ} {ok : ℕ → Bool} {o r n : ℕ} {K : Subgroup J}
    {hr : r < 31671} (ht : trK A ok DD o r n = true)
    (hA : ∀ z, ok z = true → ∃ g ∈ K, ∀ x < 31671, A z x = idx 31671 g x) :
    ∀ k < n, ∃ h : ptOf (fD DD o k) < 31671,
      (⟨ptOf (fD DD o k), h⟩ : Fin 31671) ∈ MulAction.orbit K (⟨r, hr⟩ : Fin 31671) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    obtain ⟨h1, h2, h3⟩ := trK_spec ht hk
    refine ⟨h1, ?_⟩
    by_cases hk0 : k = 0
    · have e : (⟨ptOf (fD DD o k), h1⟩ : Fin 31671) = ⟨r, hr⟩ := Fin.ext (h2 hk0)
      rw [e]
      exact MulAction.mem_orbit_self _
    · obtain ⟨hpa, hok, hmap⟩ := h3 hk0
      obtain ⟨hpt, hm⟩ := ih _ hpa (lt_trans hpa hk)
      obtain ⟨g, hg, hgA⟩ := hA _ hok
      have e : g • (⟨ptOf (fD DD o (nodeOf (fD DD o k))), hpt⟩ : Fin 31671) =
          ⟨ptOf (fD DD o k), h1⟩ := eq_of_idx (by rw [← hgA _ hpt]; exact hmap)
      rw [← e]
      exact orbit_smul_mem g hg hm

theorem le_card_tree {A : ℕ → ℕ → ℕ} {ok : ℕ → Bool} {o s r n : ℕ} {K : Subgroup J}
    {hr : r < 31671} (ht : trK A ok DD o r n = true) (hs : srtK DD o s n = true)
    (hA : ∀ z, ok z = true → ∃ g ∈ K, ∀ x < 31671, A z x = idx 31671 g x) :
    n ≤ Nat.card (MulAction.orbit K (⟨r, hr⟩ : Fin 31671)) := by
  have hT := tree_mem (hr := hr) ht hA
  have hlt : ∀ j < n, ptOf (fD DD s j) < 31671 := fun j hj => by
    obtain ⟨hm, he, -⟩ := srtK_spec hs hj
    rw [← he]
    exact (hT _ hm).1
  refine le_card_of_incr (fun j => ptOf (fD DD s j)) hlt (fun j hj => (srtK_spec hs
    (by omega)).2.2 hj) (fun j hj => ?_)
  obtain ⟨hm, he, -⟩ := srtK_spec hs hj
  obtain ⟨h1, h2⟩ := hT _ hm
  have e : (⟨ptOf (fD DD o (nodeOf (fD DD s j))), h1⟩ : Fin 31671) =
      ⟨ptOf (fD DD s j), hlt j hj⟩ := Fin.ext he
  rw [← e]
  exact h2

theorem card_orbit_e : 693 ≤ Nat.card (MulAction.orbit (lvl 2) qe) := by
  obtain ⟨ht, hs⟩ := eF_facts
  refine le_card_tree (hr := by decide) ht hs fun z hz => ?_
  obtain ⟨hz24, h0, h1⟩ := okE_spec hz
  refine ⟨pairG gs z, mem_lvl_two (eq_of_idx ?_) (eq_of_idx ?_), fun x hx =>
    CFSG.KD.Fi23Cov.tb_chain hz24 hx⟩
  · rw [← CFSG.KD.Fi23Cov.tb_chain hz24 (by norm_num)]
    exact h0
  · rw [← CFSG.KD.Fi23Cov.tb_chain hz24 (by norm_num)]
    exact h1

noncomputable abbrev hE (j : ℕ) : J := wordG jG (nineHWords.toList.getD j [])

theorem wv_hR {j : ℕ} (hj : j < 3) {x : ℕ} (hx : x < 31671) :
    wv GG (hR j) x = idx 31671 (hE j) x :=
  wv_word _ (wl_facts.2.2.2 j hj) x hx

theorem card_orbit_f :
    180 ≤ Nat.card (MulAction.orbit (lvl 2 ⊓ MulAction.stabilizer J qe : Subgroup J) qf) := by
  obtain ⟨hfix, ht, hs⟩ := fF_facts
  refine le_card_tree (hr := by decide) ht hs fun j hj => ?_
  have hj3 : j < 3 := blt_true hj
  obtain ⟨h0, h1, he⟩ := hfix j hj3
  refine ⟨hE j, ⟨mem_lvl_two (eq_of_idx ?_) (eq_of_idx ?_), eq_of_idx ?_⟩,
    fun x hx => wv_hR hj3 hx⟩
  · rw [← wv_hR hj3 (by norm_num)]
    exact h0
  · rw [← wv_hR hj3 (by norm_num)]
    exact h1
  · rw [← wv_hR hj3 (by decide)]
    exact he

theorem card_stab_le : Nat.card (MulAction.stabilizer J x₀) ≤ 2359296 := by
  set S := MulAction.stabilizer J x₀ with hS
  set S1 := S ⊓ MulAction.stabilizer J q1 with hS1
  set K4 := S1 ⊓ MulAction.stabilizer J qf with hK4
  set H2 := lvl 2 ⊓ MulAction.stabilizer J qe with hH2
  set K4' := H2 ⊓ MulAction.stabilizer J qf with hK4'
  have e1 := card_eq_orbit_mul S S1 q1 inf_le_left (fun l hl => hl.2) fun h hh hf => ⟨hh, hf⟩
  have e2 := card_eq_orbit_mul S1 K4 qf inf_le_left (fun l hl => hl.2) fun h hh hf => ⟨hh, hf⟩
  have e3 := card_eq_orbit_mul (lvl 2) H2 qe inf_le_left (fun l hl => hl.2)
    fun h hh hf => ⟨hh, hf⟩
  have e4 := card_eq_orbit_mul H2 K4' qf inf_le_left (fun l hl => hl.2) fun h hh hf => ⟨hh, hf⟩
  have o1 : Nat.card (MulAction.orbit S q1) ≤ 2 := by
    rw [← card_O2]
    exact card_orbit_le_card (fun u hu => (mem_stab_iff.1 hu).2.1) q1_mem_O2
  have o2 : Nat.card (MulAction.orbit S1 qf) ≤ 4 := by
    rw [← card_O4]
    exact card_orbit_le_card (fun u hu => (mem_stab_iff.1 (Subgroup.mem_inf.1 hu).1).2.2)
      qf_mem_O4
  have hK : K4 ≤ K4' := by
    rintro g ⟨⟨hgS, hg1⟩, hgf⟩
    obtain ⟨hg0, hg2, -⟩ := mem_stab_iff.1 hgS
    have hg1' : g • q1 = q1 := hg1
    refine ⟨⟨mem_lvl_two hg0 hg1', ?_⟩, hgf⟩
    have hmem : g • qe ∈ O2 := by
      rw [← hg2]
      exact Finset.smul_mem_smul_finset qe_mem_O2
    rcases Finset.mem_insert.1 hmem with h | h
    · exact absurd (smul_left_cancel g (h.trans hg1'.symm)) (Ne.symm q1_ne_qe)
    · exact Finset.mem_singleton.1 h
  have hH2c : Nat.card H2 ≤ 53084160 := by
    rw [card_lvl_two] at e3
    have hb : 693 * Nat.card H2 ≤ 36787322880 := by
      rw [e3]
      exact Nat.mul_le_mul_right _ card_orbit_e
    omega
  have hK4c : Nat.card K4' ≤ 294912 := by
    have hb : 180 * Nat.card K4' ≤ 53084160 := by
      calc 180 * Nat.card K4' ≤ Nat.card (MulAction.orbit H2 qf) * Nat.card K4' :=
            Nat.mul_le_mul_right _ card_orbit_f
        _ = Nat.card H2 := e4.symm
        _ ≤ 53084160 := hH2c
    omega
  have hk := Subgroup.card_le_of_le hK
  have hS' : Nat.card S ≤ 2 * Nat.card S1 := by
    rw [e1]
    exact Nat.mul_le_mul_right _ o1
  have hS1' : Nat.card S1 ≤ 4 * Nat.card K4 := by
    rw [e2]
    exact Nat.mul_le_mul_right _ o2
  omega

noncomputable abbrev xr : J := wordG jG nineXWord

noncomputable abbrev yr : J := wordG jG nineYWord

noncomputable abbrev xElt : J := xr ^ 2

noncomputable abbrev yElt : J := yr ^ 4

theorem itW_pow {w : List ℤ} (hw : ∀ z ∈ w, z.toNat < 24) : ∀ (e x : ℕ), x < 31671 →
    itW GG (w.map rZ).reverse e x = idx 31671 (wordG jG w ^ e) x
  | 0, x, _ => by rw [itW_zero, pow_zero, idx_one]
  | e + 1, x, hx => by
    rw [itW_succ, wf_reverse, wv_word w hw x hx, itW_pow hw e _ (idx_lt _ hx), pow_succ, idx_mul]

theorem xy_facts :
    (∀ b < 6, idx 31671 (xr ^ 6) b = b ∧ idx 31671 (yr ^ 12) b = b ∧
      idx 31671 xElt (idx 31671 yElt b) = idx 31671 yElt (idx 31671 xElt b)) ∧
    idx 31671 xElt 0 = 0 ∧ idx 31671 yElt 0 = 0 ∧
    (∀ a ∈ [1, nineE], idx 31671 xElt a ∈ [1, nineE]) ∧
    (∀ a ∈ [1, nineE], idx 31671 yElt a ∈ [1, nineE]) ∧
    (∀ a ∈ nineO4, idx 31671 xElt a ∈ nineO4) ∧ (∀ a ∈ nineO4, idx 31671 yElt a ∈ nineO4) ∧
    idx 31671 xElt 2 ≠ 2 ∧ idx 31671 yElt 2 ≠ 2 ∧ idx 31671 yElt 2 ≠ idx 31671 xElt 2 ∧
    idx 31671 yElt 2 ≠ idx 31671 xElt (idx 31671 xElt 2) := by
  have h := xyK_spec (G := GG) (xw := (nineXWord.map rZ).reverse)
    (yw := (nineYWord.map rZ).reverse) (s2 := [1, nineE]) (s4 := nineO4) xyF_ok
  have hx := itW_pow wl_facts.2.1
  have hy := itW_pow wl_facts.2.2.1
  have l2 : ∀ a ∈ [1, nineE], a < 31671 := by decide
  have l4 : ∀ a ∈ nineO4, a < 31671 := by decide
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
  refine ⟨fun b hb => ?_, ?_, ?_, fun a ha => ?_, fun a ha => ?_, fun a ha => ?_, fun a ha => ?_,
    ?_, ?_, ?_, ?_⟩
  · obtain ⟨a1, a2, a3⟩ := h1 b hb
    have hb' : b < 31671 := by omega
    rw [hx 6 b hb'] at a1
    rw [hy 12 b hb'] at a2
    rw [hy 4 b hb', hx 2 b hb', hx 2 _ (idx_lt _ hb'), hy 4 _ (idx_lt _ hb')] at a3
    exact ⟨a1, a2, a3⟩
  · rw [← hx 2 0 (by norm_num)]
    exact h2
  · rw [← hy 4 0 (by norm_num)]
    exact h3
  · rw [← hx 2 a (l2 a ha)]
    exact h4 a ha
  · rw [← hy 4 a (l2 a ha)]
    exact h5 a ha
  · rw [← hx 2 a (l4 a ha)]
    exact h6 a ha
  · rw [← hy 4 a (l4 a ha)]
    exact h7 a ha
  · rw [← hx 2 2 (by norm_num)]
    exact h8
  · rw [← hy 4 2 (by norm_num)]
    exact h9
  · rw [← hx 2 2 (by norm_num), ← hy 4 2 (by norm_num)]
    exact h10
  · rw [← hx 2 (idx 31671 xElt 2) (idx_lt _ (by norm_num)), ← hx 2 2 (by norm_num),
      ← hy 4 2 (by norm_num)]
    exact h11

theorem fix_of_idx {g : J} (h0 : idx 31671 g 0 = 0)
    (h2 : ∀ a ∈ [1, nineE], idx 31671 g a ∈ [1, nineE])
    (h4 : ∀ a ∈ nineO4, idx 31671 g a ∈ nineO4) : g • x₀ = x₀ := by
  rw [← MulAction.mem_stabilizer_iff, mem_stab_iff]
  refine ⟨eq_of_idx h0, smul_eq_of_subset fun a ha => ?_, smul_eq_of_subset fun a ha => ?_⟩
  · rw [mem_O2] at ha ⊢
    rw [smul_val_eq_idx]
    exact h2 a.val ha
  · rw [mem_O4] at ha ⊢
    rw [smul_val_eq_idx]
    exact h4 a.val ha

theorem x_fix : xElt • x₀ = x₀ :=
  fix_of_idx xy_facts.2.1 xy_facts.2.2.2.1 xy_facts.2.2.2.2.2.1

theorem y_fix : yElt • x₀ = x₀ :=
  fix_of_idx xy_facts.2.2.1 xy_facts.2.2.2.2.1 xy_facts.2.2.2.2.2.2.1

theorem x_cube : xElt ^ 3 = 1 := by
  rw [← pow_mul]
  exact eq_one_of_base fun b hb => (xy_facts.1 b hb).1

theorem y_cube : yElt ^ 3 = 1 := by
  rw [← pow_mul]
  exact eq_one_of_base fun b hb => (xy_facts.1 b hb).2.1

theorem x_ne_one : xElt ≠ 1 := by
  intro h
  apply xy_facts.2.2.2.2.2.2.2.1
  rw [h, idx_one]

theorem y_ne_one : yElt ≠ 1 := by
  intro h
  apply xy_facts.2.2.2.2.2.2.2.2.1
  rw [h, idx_one]

theorem xy_comm : xElt * yElt = yElt * xElt := by
  have h : (yElt * xElt)⁻¹ * (xElt * yElt) = 1 := eq_one_of_base fun b hb => by
    rw [idx_mul, idx_mul, (xy_facts.1 b hb).2.2, ← idx_mul yElt xElt, idx_inv_idx]
  rw [inv_mul_eq_one] at h
  exact h.symm

theorem y_notMem_zpowers : yElt ∉ Subgroup.zpowers xElt := by
  refine CFSG.RankThree.Asc83Table.not_mem_zpowers_of_ne x_cube y_ne_one (fun hyx => ?_)
    (fun hyx => ?_)
  · apply xy_facts.2.2.2.2.2.2.2.2.2.1
    rw [hyx]
  · apply xy_facts.2.2.2.2.2.2.2.2.2.2
    rw [hyx, pow_two, idx_mul]

theorem card_E9 : Nat.card (Subgroup.closure ({xElt, yElt} : Set J)) = 9 :=
  CFSG.RankThree.Asc83Table.card_closure_pair_eq_nine x_cube y_cube xy_comm x_ne_one
    y_notMem_zpowers

theorem card_stab :
    Nat.card (MulAction.stabilizer J x₀) = 9 * Nat.card uSyl := by
  have hU : uSyl ≤ MulAction.stabilizer J x₀ := fun u hu => fix_x₀ u hu
  have hQ : Subgroup.closure ({xElt, yElt} : Set J) ≤ MulAction.stabilizer J x₀ := by
    rw [Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact x_fix
    · exact y_fix
  have d1 := Subgroup.card_dvd_of_le hU
  have d2 := Subgroup.card_dvd_of_le hQ
  rw [card_uSyl] at d1
  rw [card_E9] at d2
  have d := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 9 262144) d2 d1
  have hpos : 0 < Nat.card (MulAction.stabilizer J x₀) := Nat.card_pos
  have hle := card_stab_le
  rw [card_uSyl]
  obtain ⟨k, hk⟩ := d
  rw [hk] at hpos hle ⊢
  omega

theorem package744108 : InnerIndexNinePackage ↥J :=
  innerIndexNinePackage_of_unique_fixed isSylowTwoOf_uSyl fix_x₀ uniq_x₀ card_stab x_fix y_fix
    x_cube y_cube xy_comm x_ne_one y_notMem_zpowers

end CertificateChecks.KernelFi23Nine

end
