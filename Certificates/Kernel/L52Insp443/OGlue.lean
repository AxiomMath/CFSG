module

public import Certificates.Kernel.L52Insp443.InvChk
public import Certificates.Kernel.L52Insp443.TabChk
public import CFSG.Certificates.Kernel.L52Insp443.InvSound
public import CFSG.Literature.GL52Counts
public import CFSG.Certificates.Kernel.L52Insp443.Norm

public section

set_option maxRecDepth 20000

namespace CertificateChecks.KernelL52I

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.Misc.GLM CFSG.KC.L52I CFSG.SectionRank.QTK.Insp443.L52
  CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Literature.GL52 CFSG.Quasithin.KGC31.Native
  CFSG.Quasithin.KGC31 CFSG.SectionRank.QTK.Insp443.PermKit.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native CFSG.KC.KGC31P

theorem f2_of_tabsK {c : List ℕ} {T : List Table} (h : tabsK c T = true) :
    List.Forall₂ (fun T y => Rep 31 T (glPerm y)) T (c.map gD) ∧ ∀ b ∈ c, unitK b = true := by
  obtain ⟨h1, h2⟩ := forall₂_of_tabsK h
  exact ⟨List.forall₂_map_right_iff.mpr (List.forall₂_map_right_iff.mp h1), h2⟩

theorem f2_cands : ∀ {Ts : List (List Table)} {CS : List (List ℕ)}, CS.length = Ts.length →
    (∀ j < Ts.length, tabsK (CS.getD j []) (Ts.getD j []) = true) →
    List.Forall₂ (List.Forall₂ fun T y => Rep 31 T (glPerm y)) Ts (CS.map (List.map gD)) ∧
      ∀ c ∈ CS, ∀ b ∈ c, unitK b = true
  | [], [], _, _ => ⟨List.Forall₂.nil, by simp⟩
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | T :: Ts, c :: CS, hl, h => by
    obtain ⟨h1, h2⟩ := f2_of_tabsK (h 0 (by simp))
    obtain ⟨ih1, ih2⟩ := f2_cands (Ts := Ts) (CS := CS) (by simpa using hl)
      (fun j hj => h (j + 1) (by simp [hj]))
    refine ⟨List.Forall₂.cons h1 ih1, fun d hd => ?_⟩
    rcases List.mem_cons.mp hd with rfl | hd
    · exact h2
    · exact ih2 d hd

theorem codes_eq1 : ∀ {c : List ℕ}, (∀ b ∈ c, unitK b = true) →
    (c.map gD).map (fun g : G => mcode (g : Mat)) = c
  | [], _ => rfl
  | b :: c, hu => by
    rw [List.map_cons, List.map_cons, mcode_gD (hu b List.mem_cons_self),
      codes_eq1 fun d hd => hu d (List.mem_cons_of_mem _ hd)]

theorem codes_eq : ∀ {CS : List (List ℕ)}, (∀ c ∈ CS, ∀ b ∈ c, unitK b = true) →
    CS = (CS.map (List.map gD)).map (List.map fun g : G => mcode (g : Mat))
  | [], _ => rfl
  | c :: CS, hu => by
    rw [List.map_cons, List.map_cons, codes_eq1 (hu c List.mem_cons_self),
      ← codes_eq fun d hd => hu d (List.mem_cons_of_mem _ hd)]

theorem cands_facts {i : ℕ} (h : ch725108t i = true) :
    List.Forall₂ (List.Forall₂ fun T y => Rep 31 T (glPerm y)) ([cands5, cands7].getD i [])
        ((O.cs.getD i []).map (List.map gD)) ∧
      O.cs.getD i [] =
        ((O.cs.getD i []).map (List.map gD)).map (List.map fun g : G => mcode (g : Mat)) := by
  unfold ch725108t letL at h
  obtain ⟨h1, h2⟩ := and2 h
  obtain ⟨hc, hu⟩ := f2_cands (Nat.eq_of_beq_eq_true h1)
    (fun j hj => (allK_iff _ _).mp h2 j (List.mem_range.mpr hj))
  exact ⟨hc, codes_eq hu⟩

theorem x_facts {i : ℕ} (h : ch725108x i = true) (hP : 0 < (ch725108pt.getD i (0, #[])).1) :
    ∃ x : G, Rep 31 (ch725108pt.getD i (0, #[])).2 (glPerm x) ∧
      orderOf x = (ch725108pt.getD i (0, #[])).1 ∧
      (O.px.getD i []).length = (ch725108pt.getD i (0, #[])).1 ∧
      (O.qx.getD i []).length = (ch725108pt.getD i (0, #[])).1 ∧
      ∀ j < (ch725108pt.getD i (0, #[])).1, (O.px.getD i []).getD j 0 = mcode ((x ^ j : G) : Mat) ∧
        (O.qx.getD i []).getD j 0 = mcode ((x⁻¹ ^ j : G) : Mat) := by
  unfold ch725108x at h
  simp only [letL, letB_l52] at h
  generalize (ch725108pt.getD i (0, #[])).1 = p at h hP ⊢
  generalize (ch725108pt.getD i (0, #[])).2 = T at h ⊢
  generalize O.px.getD i [] = ps at h ⊢
  generalize O.qx.getD i [] = qs at h ⊢
  obtain ⟨h0, r⟩ := and2 h
  obtain ⟨hst, r⟩ := and2 r
  obtain ⟨hpl, r⟩ := and2 r
  obtain ⟨hql, r⟩ := and2 r
  obtain ⟨hinv, r⟩ := and2 r
  obtain ⟨hord, r⟩ := and2 r
  obtain ⟨hu, htab⟩ := and2 r
  have hx : mcode ((gD (ps.getD 1 0) : G) : Mat) = ps.getD 1 0 := mcode_gD hu
  have hpc := pow_codes (m := p - 1) (x := gD (ps.getD 1 0)) (Nat.eq_of_beq_eq_true h0)
    (fun j hj => Nat.eq_of_beq_eq_true ((allK_iff _ _).mp hst j (List.mem_range.mpr hj))) hx
    (fun j hj => Nat.eq_of_beq_eq_true
      (and2 ((allK_iff _ _).mp hinv j (List.mem_range.mpr (by omega)))).1)
    (fun j hj => (and2 ((allK_iff _ _).mp hinv j (List.mem_range.mpr (by omega)))).2)
  refine ⟨gD (ps.getD 1 0), ?_, ?_, Nat.eq_of_beq_eq_true hpl, Nat.eq_of_beq_eq_true hql,
    fun j hj => hpc j (by omega)⟩
  · rw [← hx] at htab
    exact rep_of_tabK htab
  · rw [← hx] at hord
    exact (ordK_iff _ hP).mp hord

theorem inv_len : O.inv.length = 28 := by decide +kernel

theorem inv_ne : ∀ k < 28, O.inv.getD k [] ≠ [] := by decide +kernel

theorem inv_blocks : ∀ k < 28, ch725108i k = true := by
  intro k hk
  interval_cases k
  exacts [ch725108i0, ch725108i1, ch725108i2, ch725108i3, ch725108i4, ch725108i5, ch725108i6,
    ch725108i7, ch725108i8, ch725108i9, ch725108i10, ch725108i11, ch725108i12, ch725108i13,
    ch725108i14, ch725108i15, ch725108i16, ch725108i17, ch725108i18, ch725108i19, ch725108i20,
    ch725108i21, ch725108i22, ch725108i23, ch725108i24, ch725108i25, ch725108i26, ch725108i27]

theorem inv_nodup : O.inv.flatten.Nodup := by
  refine nodup_flatten_of_blocks O.inv (fun k hk => ?_) (fun k hk => inv_ne k (inv_len ▸ hk))
  have h := inv_blocks k (inv_len ▸ hk)
  unfold ch725108i at h
  exact (and2 h).1

theorem one_of_mem {c : ℕ} (hc : c ∈ O.inv.flatten) : ch725108one c = true := by
  obtain ⟨l, hl, hcl⟩ := List.mem_flatten.mp hc
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hl
  have h := inv_blocks k (inv_len ▸ hk)
  unfold ch725108i at h
  rw [← List.getD_eq_getElem _ [] hk] at hcl
  exact (allK_iff _ _).mp (and2 h).2 c hcl

theorem foldr_len : ∀ Ls : List (List ℕ),
    List.foldr (fun L acc => Nat.add (List.length L) acc) (nat_lit 0) Ls = Ls.flatten.length
  | [] => rfl
  | L :: Ls => by
    rw [List.foldr_cons, foldr_len Ls, List.flatten_cons, List.length_append]
    rfl

theorem inv_count : O.inv.flatten.length = 6975 := by
  rw [← foldr_len]
  exact Nat.eq_of_beq_eq_true ch725108n0

theorem mem_inv {g : G} (hg : orderOf g = 2) :
    mcode (g : Mat) ∈ O.inv.flatten :=
  mem_of_card (fun g : G => mcode (g : Mat)) kG_inj (fun g : G => orderOf g = 2) inv_nodup
    (fun c hc => invo_exists (and2 (one_of_mem hc)).1) (by rw [card_order_two, inv_count]) hg

theorem inv_tab {t : Table} (ht : t ∈ orderTables glCert 2) :
    ∃ h : G, Rep 31 t (glPerm h) ∧ orderOf h = 2 := by
  obtain ⟨π, hπ, hr⟩ := exists_rep_of_mem (forall₂_orderTables (by norm_num) glCert
    (by norm_num)) ht
  rw [List.mem_reverse, List.mem_filter, decide_eq_true_iff] at hπ
  obtain ⟨g, rfl⟩ := (mem_glCert_iff _).1 ((mem_enumeration_iff glCert glCert_valid _).1 hπ.1)
  exact ⟨g, hr, by rw [← orderOf_injective glPerm glPerm_injective g]; exact hπ.2⟩

theorem orb_of {i : ℕ}
    (hx : ch725108x i = true) (hP : (ch725108pt.getD i (0, #[])).1.Prime)
    {cands : List (List Table)} {C : List (List G)}
    (hc : List.Forall₂ (List.Forall₂ fun T y => Rep 31 T (glPerm y)) cands C)
    (hcs : O.cs.getD i [] = C.map (List.map fun g : G => mcode (g : Mat)))
    (hone : ∀ c ∈ O.inv.flatten,
      orbOneK (O.px.getD i []) (O.qx.getD i []) (O.cs.getD i []) c = true) :
    orbCheck 31 (ch725108pt.getD i (0, #[])).1 (orderTables glCert 2)
      (powTabs 31 (ch725108pt.getD i (0, #[])).2 (ch725108pt.getD i (0, #[])).1) cands = true := by
  obtain ⟨x, hX, hord, hpl, hql, hcodes⟩ := x_facts hx hP.pos
  refine orbCheck_of glPerm glPerm_injective hP hX (by rw [← hord]; exact pow_orderOf_eq_one x)
    hc fun t ht => ?_
  obtain ⟨h, hr, h2⟩ := inv_tab ht
  refine ⟨h, hr, ?_⟩
  have e := orbOneK_eq (fun g : G => mcode (g : Mat)) kG_one kG_mul kG_inj (h := h) hP.one_lt hpl
    hql (fun j hj => (hcodes j hj).1) (fun j hj => (hcodes j hj).2) hcs
  rw [← e]
  exact hone _ (mem_inv h2)

theorem t_all : ∀ z < 7, tabsK (D.zB.getD z []) (e16.getD z []) = true := by
  intro z hz
  interval_cases z
  exacts [ch725109t0, ch725109t1, ch725109t2, ch725109t3, ch725109t4, ch725109t5, ch725109t6]

theorem u_all : ∀ w < 2, ch725109u w = true := by
  intro w hw
  interval_cases w
  exacts [ch725109u0, ch725109u1]

theorem rep_of_mem {c : List ℕ} {Ts : List Table} {T : Table}
    (h : List.Forall₂ (Rep 31) Ts (c.map fun u => glPerm (gD u))) (hT : T ∈ Ts) :
    ∃ g : G, Rep 31 T (glPerm g) := by
  obtain ⟨π, hπ, hr⟩ := exists_rep_of_mem h hT
  obtain ⟨u, -, rfl⟩ := List.mem_map.mp hπ
  exact ⟨gD u, hr⟩

theorem rep_of_mem_getD {L : List (List Table)} {T : Table} {n : ℕ} (hl : L.length = n)
    (hf : ∀ k < n, ∃ c : List ℕ, tabsK c (L.getD k []) = true) (hT : T ∈ L.flatten) :
    ∃ g : G, Rep 31 T (glPerm g) := by
  obtain ⟨l, hl', hTl⟩ := List.mem_flatten.mp hT
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hl'
  rw [← List.getD_eq_getElem _ [] hk] at hTl
  obtain ⟨c, hc⟩ := hf k (hl ▸ hk)
  exact rep_of_mem (forall₂_of_tabsK hc).1 hTl

theorem memL_base : memL = ([x5T, x7T, x31T] ++ e16.flatten ++ e64a0.flatten ++ e64a1.flatten ++
    (List.range 2).flatMap fun w => diagT 31 (e64a0.getD w []) (e64a1.getD w [])).dedup := rfl

theorem rep_x (i : ℕ) (hx : ch725108x i = true) (hP : 0 < (ch725108pt.getD i (0, #[])).1) :
    ∃ g : G, Rep 31 (ch725108pt.getD i (0, #[])).2 (glPerm g) := by
  obtain ⟨x, hX, -⟩ := x_facts hx hP
  exact ⟨x, hX⟩

theorem memL_rep : ∀ T ∈ memL, ∃ g : G, Rep 31 T (glPerm g) := by
  intro T hT
  rw [memL_base, List.mem_dedup] at hT
  simp only [List.mem_append, List.mem_cons, List.mem_flatMap, List.mem_range,
    List.not_mem_nil, or_false] at hT
  rcases hT with ((((rfl | rfl | rfl) | hT) | hT) | hT) | ⟨w, hw, hT⟩
  · exact rep_x 0 ch725108x0 (by decide)
  · exact rep_x 1 ch725108x1 (by decide)
  · exact rep_x 2 ch725108x2 (by decide)
  · exact rep_of_mem_getD (n := 7) rfl (fun k hk => ⟨_, t_all k hk⟩) hT
  · exact rep_of_mem_getD (n := 2) rfl (fun k hk => ⟨_, (and2 (u_all k hk)).1⟩) hT
  · exact rep_of_mem_getD (n := 2) rfl (fun k hk => ⟨_, (and2 (u_all k hk)).2⟩) hT
  · obtain ⟨u0, u1⟩ := and2 (u_all w hw)
    have h0 := forall₂_of_tabsK u0
    have h1 := forall₂_of_tabsK u1
    rw [diagT.eq_1] at hT
    exact rep_of_mem (forall₂_zip h0.1 h0.2 h1.1 h1.2).1 hT

theorem size_zipWith : ∀ (a b : List Table) {T : Table}, T ∈ List.zipWith (compT 31) a b →
    T.size = 31
  | [], _, _, h => by simp at h
  | _ :: _, [], _, h => by simp at h
  | A :: a, B :: b, T, h => by
    rw [List.zipWith_cons_cons, List.mem_cons] at h
    rcases h with rfl | h
    · exact Array.size_ofFn
    · exact size_zipWith a b h

theorem size_lits : ([x5T, x7T, x31T] ++ e16.flatten ++ e64a0.flatten ++ e64a1.flatten).all
    (fun T => T.size == 31) = true := by decide +kernel

theorem memL_size : ∀ T ∈ memL, T.size = 31 := by
  intro T hT
  rw [memL_base, List.mem_dedup, List.mem_append] at hT
  rcases hT with hT | hT
  · exact beq_iff_eq.mp (List.all_eq_true.mp size_lits T hT)
  · obtain ⟨w, -, hT⟩ := List.mem_flatMap.mp hT
    rw [diagT.eq_1] at hT
    exact size_zipWith _ _ hT

theorem eq_of_tblEq {S T : Table} (h : tblEq 31 S T = true) (hS : S.size = 31)
    (hT : T.size = 31) : S = T := by
  rw [tblEq_iff] at h
  refine Array.ext (by rw [hS, hT]) fun i h1 h2 => ?_
  have e := h i (by omega)
  unfold ap at e
  rw [getElem!_pos S i h1, getElem!_pos T i h2] at e
  exact UInt32.toNat_inj.mp e

theorem rep_eq_iff {u T : Table} {π : Equiv.Perm (Fin 31)} (hT : Rep 31 T π) :
    tblEq 31 u T = true ↔ Rep 31 u π := by
  rw [tblEq_iff]
  exact ⟨fun h i hi => by rw [h i hi, hT i hi], fun h i hi => by rw [h i hi, hT i hi]⟩

theorem distinctT_of : ∀ {L : List Table}, L.Nodup → (∀ T ∈ L, T.size = 31) →
    distinctT 31 L = true
  | [], _, _ => rfl
  | T :: L, hn, hs => by
    rw [List.nodup_cons] at hn
    simp only [distinctT, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true']
    refine ⟨fun S hS => ?_, distinctT_of hn.2 fun U hU => hs U (List.mem_cons_of_mem _ hU)⟩
    rw [← Bool.not_eq_true]
    intro e
    exact hn.1 ((eq_of_tblEq e (hs T List.mem_cons_self)
      (hs S (List.mem_cons_of_mem _ hS))) ▸ hS)

theorem card_memL : Nat.card {g : G // ∃ u ∈ memL, Rep 31 u (glPerm g)} = memL.length := by
  classical
  choose! f hf using memL_rep
  have hinj : ∀ u ∈ memL, ∀ v ∈ memL, f u = f v → u = v := fun u hu v hv e =>
    eq_of_tblEq ((rep_eq_iff (hf v hv)).mpr (e ▸ hf u hu)) (memL_size u hu) (memL_size v hv)
  have e : ∀ g : G, (∃ u ∈ memL, Rep 31 u (glPerm g)) ↔ g ∈ (memL.map f).toFinset := fun g => by
    rw [List.mem_toFinset, List.mem_map]
    constructor
    · rintro ⟨u, hu, hr⟩
      exact ⟨u, hu, glPerm_injective
        ((tblEq_iff_eq (hf u hu) hr).mp ((rep_eq_iff (hf u hu)).mpr (hf u hu)))⟩
    · rintro ⟨u, hu, rfl⟩
      exact ⟨u, hu, hf u hu⟩
  rw [Nat.card_congr (Equiv.subtypeEquivRight e), Nat.card_eq_fintype_card, Fintype.card_coe,
    List.toFinset_card_of_nodup (List.Nodup.map_on hinj (List.nodup_dedup _)), List.length_map]

theorem tabOK_of_rep {T : Table} {π : Equiv.Perm (Fin 31)} (hT : Rep 31 T π) :
    tabOK 31 T (invT 31 T) = true := by
  have hR := rep_invT_of_rep hn31 hT
  unfold tabOK
  refine allIn_eq_true.mpr fun i _ hi => ?_
  rw [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, hT i hi]
  refine ⟨idx_lt _ hi, ?_⟩
  rw [hR _ (idx_lt _ hi), idx_inv_idx]

theorem exists_of_f2 {α β : Type} {R : α → β → Prop} {l : List α} {l' : List β}
    (h : List.Forall₂ R l l') {a : α} (ha : a ∈ l) : ∃ b, R a b := by
  induction h with
  | nil => exact absurd ha List.not_mem_nil
  | cons hr _ ih =>
    rcases List.mem_cons.mp ha with rfl | ha
    · exact ⟨_, hr⟩
    · exact ih ha

theorem candsOK_of {cands : List (List Table)} {C : List (List G)}
    (hc : List.Forall₂ (List.Forall₂ fun T y => Rep 31 T (glPerm y)) cands C) :
    candsOK 31 cands = true := by
  unfold candsOK
  rw [List.all_eq_true]
  intro c hc'
  obtain ⟨B, hB⟩ := exists_of_f2 hc hc'
  rw [List.all_eq_true]
  intro T hT
  obtain ⟨y, hy⟩ := exists_of_f2 hB hT
  exact tabOK_of_rep hy

theorem ord_of {i : ℕ} (hx : ch725108x i = true) (hP : 0 < (ch725108pt.getD i (0, #[])).1) :
    ordTest 31 (ch725108pt.getD i (0, #[])).1 (ch725108pt.getD i (0, #[])).2 = true := by
  obtain ⟨x, hX, hord, -⟩ := x_facts hx hP
  rw [ordTest_iff' hX hP, orderOf_injective glPerm glPerm_injective x]
  exact hord

theorem one_parts {c : ℕ} (hc : c ∈ O.inv.flatten) :
    orbOneK (O.px.getD 0 []) (O.qx.getD 0 []) (O.cs.getD 0 []) c = true ∧
      orbOneK (O.px.getD 1 []) (O.qx.getD 1 []) (O.cs.getD 1 []) c = true ∧
      orbOneK (O.px.getD 2 []) (O.qx.getD 2 []) (O.cs.getD 2 []) c = true := by
  have h := one_of_mem hc
  unfold ch725108one at h
  obtain ⟨-, r⟩ := and2 h
  obtain ⟨h0, r⟩ := and2 r
  obtain ⟨h1, h2⟩ := and2 r
  exact ⟨h0, h1, h2⟩

theorem cs2 : O.cs.getD 2 [] = [] := by decide +kernel

theorem pt0 : (ch725108pt.getD 0 (0, #[])).1.Prime := by
  have e : (ch725108pt.getD 0 (0, #[])).1 = 5 := rfl
  rw [e]
  norm_num

theorem pt1 : (ch725108pt.getD 1 (0, #[])).1.Prime := by
  have e : (ch725108pt.getD 1 (0, #[])).1 = 7 := rfl
  rw [e]
  norm_num

theorem pt2 : (ch725108pt.getD 2 (0, #[])).1.Prime := by
  have e : (ch725108pt.getD 2 (0, #[])).1 = 31 := rfl
  rw [e]
  norm_num

theorem chkOrb52_true :
    chkOrb52 () = true := by
  classical
  obtain ⟨hc5, hcs5⟩ := cands_facts ch725108t0
  obtain ⟨hc7, hcs7⟩ := cands_facts ch725108t1
  have hcount : countProducts 31 (inSp 31 memL) (levelTables glCert) (idT 31) = memL.length := by
    rw [← card_memL]
    exact (card_subtype_glPerm (fun π => ∃ u ∈ memL, Rep 31 u π) (inSp 31 memL)
      fun T π hT => by
        unfold inSp
        rw [List.any_eq_true]
        exact ⟨fun ⟨u, hu, e⟩ => ⟨u, hu, (rep_eq_iff hT).mp e⟩,
          fun ⟨u, hu, e⟩ => ⟨u, hu, (rep_eq_iff hT).mpr e⟩⟩).symm
  have o31 : orbCheck 31 31 (orderTables glCert 2) (powTabs 31 x31T 31) [] = true := by
    refine orb_of (i := 2) (C := []) ch725108x2 pt2 List.Forall₂.nil cs2 fun c hc => ?_
    exact (one_parts hc).2.2
  have e0 : ch725108pt.getD 0 (0, #[]) = (5, x5T) := rfl
  have e1 : ch725108pt.getD 1 (0, #[]) = (7, x7T) := rfl
  have e2 : ch725108pt.getD 2 (0, #[]) = (31, x31T) := rfl
  have d5 := ord_of ch725108x0 pt0.pos
  have d7 := ord_of ch725108x1 pt1.pos
  have d31 := ord_of ch725108x2 pt2.pos
  rw [e0] at d5
  rw [e1] at d7
  rw [e2] at d31
  rw [chkOrb52.eq_1]
  simp only [Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, hcount⟩, d5⟩, d7⟩, d31⟩, candsOK_of hc5⟩, candsOK_of hc7⟩, ?_⟩, ?_⟩,
    o31⟩
  · rw [tabsOK, List.all_eq_true]
    intro T hT
    obtain ⟨g, hg⟩ := memL_rep T hT
    exact tabOK_of_rep hg
  · exact distinctT_of (List.nodup_dedup _) memL_size
  · exact orb_of (i := 0) ch725108x0 pt0 hc5 hcs5 fun c hc => (one_parts hc).1
  · exact orb_of (i := 1) ch725108x1 pt1 hc7 hcs7 fun c hc => (one_parts hc).2.1

end CertificateChecks.KernelL52I

end
