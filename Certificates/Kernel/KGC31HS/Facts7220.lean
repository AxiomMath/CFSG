module

public import Certificates.Kernel.KGC31HS.Facts7219
public import Certificates.Kernel.KGC31HS.Cos16A
public import Certificates.Kernel.KGC31HS.Cos16B
public import Certificates.Kernel.KGC31HS.Cos16C
public import Certificates.Kernel.KGC31HS.Cos8A
public import Certificates.Kernel.KGC31HS.Cos8B
public import CFSG.Quasithin.Vol2.KGFactC31HSData
public import CFSG.RankThree.Native.HSMcLSmall
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelKGC31HS

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.KGC31P CFSG.KC.Child3 CFSG.KC.BfsPin
open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native
open CFSG.Quasithin.KGC31 CFSG.Quasithin.KGC31.Native CFSG.Quasithin.KGC31.HS
open CFSG.KS.SporSch.MOC CFSG.Monster.B.Mathieu CFSG.Certificates CertificateChecks.KernelHS100
open CFSG.KS.SporSch.CodesImg CFSG.KS.M11 CFSG.RankThree.Native

theorem ppcAll {c : Nat} {bs : List Nat} (hc : PP 100 7 c) (hb : ∀ b ∈ bs, PP 100 7 b) :
    ∀ b ∈ cAll c bs, PP 100 7 b := by
  intro b hbb
  obtain ⟨b', hb', rfl⟩ := List.mem_map.1 hbb
  exact PP_pcj hc hc.pinv (hb b' hb')

theorem conjAll_eq {c : Nat} {bs : List Nat} (hc : PP 100 7 c) (hb : ∀ b ∈ bs, PP 100 7 b) :
    conjAll (tabP 100 7 c) (bs.map (tabP 100 7)) = (cAll c bs).map (tabP 100 7) := by
  rw [conjAll, cAll, invT_tabP hc, List.map_map, List.map_map]
  exact List.map_congr_left fun b hbb => conjTab_tabP hc hc.pinv (hb b hbb)

theorem cA (wd : List Int) (ws : List (List Int)) :
    conjAll (wordT 100 gensT wd) (ws.map (wordT 100 gensT)) =
      (cAll (pw wd) (ws.map pw)).map (tabP 100 7) := by
  rw [wT, mapW]
  exact conjAll_eq (ppw' wd) (ppL ws)

theorem cands5_eq : cands5 = C5.map (List.map (tabP 100 7)) := by
  rw [cands5, C5, List.map_map]
  refine List.map_congr_left fun k _ => ?_
  simp only [Function.comp_apply]
  rw [candT, u16T, tabsOf, cA]
  rfl

theorem cands7_eq : cands7 = C7.map (List.map (tabP 100 7)) := by
  simp only [cands7, C7, candT, cnd, u8T, u8P, tabsOf, cA, List.map_cons, List.map_nil]

theorem ppC5 : ∀ c ∈ C5, ∀ b ∈ c, PP 100 7 b := by
  intro c hc
  obtain ⟨k, -, rfl⟩ := List.mem_map.1 hc
  exact ppcAll (ppw' _) (ppL _)

theorem ppC7 : ∀ c ∈ C7, ∀ b ∈ c, PP 100 7 b := by
  simp only [C7, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, forall_const,
    and_true]
  exact ⟨ppcAll (ppw' _) (ppL _), ppcAll (ppw' _) (ppL _)⟩

theorem orb5 : orbCheck 100 5 invs [lineT 0] cands5 = true := by
  rw [lineT_eq0, cands5_eq, orbCheck, List.all_cons, List.all_nil, Bool.and_true, invOK_tabP ppL0,
    Bool.true_and, List.all_eq_true]
  intro t ht
  obtain ⟨j, hj, rfl⟩ := mem_invs t ht
  rw [orbOne_tabP hsz ppL0 (inv_facts hj).1 ppC5]
  exact (inv_facts hj).2.1

theorem act5b : actCheck 100 5 invs [lineT 2] = true := by
  rw [lineT_eq2, actCheck, List.all_cons, List.all_nil, Bool.and_true, invOK_tabP ppL2,
    Bool.true_and, List.all_eq_true]
  intro t ht
  obtain ⟨j, hj, rfl⟩ := mem_invs t ht
  rw [actOne_tabP ppL2 (inv_facts hj).1]
  exact (inv_facts hj).2.2.1

theorem act5a : actCheck 100 5 invs [lineT 23] = true := by
  rw [lineT_eq23, actCheck, List.all_cons, List.all_nil, Bool.and_true, invOK_tabP ppL23,
    Bool.true_and, List.all_eq_true]
  intro t ht
  obtain ⟨j, hj, rfl⟩ := mem_invs t ht
  rw [actOne_tabP ppL23 (inv_facts hj).1]
  exact (inv_facts hj).2.2.2.1

theorem orb7 : orbCheck 100 7 invs [x7T] cands7 = true := by
  have hx : x7T = tabP 100 7 X7 := wT w7
  have pX : PP 100 7 X7 := ppw' w7
  rw [hx, cands7_eq, orbCheck, List.all_cons, List.all_nil, Bool.and_true, invOK_tabP pX,
    Bool.true_and, List.all_eq_true]
  intro t ht
  obtain ⟨j, hj, rfl⟩ := mem_invs t ht
  rw [orbOne_tabP hsz pX (inv_facts hj).1 ppC7]
  exact (inv_facts hj).2.2.2.2.1

theorem act11 : actCheck 100 11 invs [x11T] = true := by
  have hx : x11T = tabP 100 7 X11 := wT w11
  have pX : PP 100 7 X11 := ppw' w11
  rw [hx, actCheck, List.all_cons, List.all_nil, Bool.and_true, invOK_tabP pX,
    Bool.true_and, List.all_eq_true]
  intro t ht
  obtain ⟨j, hj, rfl⟩ := mem_invs t ht
  rw [actOne_tabP pX (inv_facts hj).1]
  exact (inv_facts hj).2.2.2.2.2

theorem candInv : ((List.range 7).all fun k => invOK 100 (candT k) (invT 100 (candT k))) = true := by
  rw [List.all_eq_true]
  intro k _
  rw [candT, wT]
  exact invOK_tabP (ppw' _)

theorem ebW (ws : List (List Int)) :
    ebasisOK 100 (ws.map (wordT 100 gensT)) = pebasis 100 7 (ws.map pw) := by
  rw [mapW]
  exact ebasisOK_tabP hsz (ppL ws)

theorem kEbP : pebasis 100 7 u16P = true ∧ pebasis 100 7 u8P = true := and_split kEb

theorem eb16 : ebasisOK 100 u16T = true := (ebW u16W).trans kEbP.1
theorem eb8 : ebasisOK 100 u8T = true := (ebW u8W).trans kEbP.2

theorem cntW (ws : List (List Int)) :
    (cbP.map (tabP 100 7)).countP (commAll 100 (ws.map (wordT 100 gensT))) =
      cbP.countP (pcommAll 100 7 (ws.map pw)) := by
  rw [mapW, List.countP_map]
  exact countP_congr' fun c hcc => commAll_tabP (ppL ws) (ppcb c hcc)

theorem cent16 : cbT.countP (commAll 100 u16T) = 16 := by
  have h1 : cbT.countP (commAll 100 u16T) = cbP.countP (pcommAll 100 7 u16P) := by
    rw [cbT_eq]
    exact cntW u16W
  rw [h1, Nat.eq_of_beq_eq_true kC16]

theorem cent8 : cbT.countP (commAll 100 u8T) = 64 := by
  have h1 : cbT.countP (commAll 100 u8T) = cbP.countP (pcommAll 100 7 u8P) := by
    rw [cbT_eq]
    exact cntW u8W
  rw [h1, Nat.eq_of_beq_eq_true kC8]

theorem kCosP : pcosetOK 100 7 (HP.F 0) u16P r16P = true ∧ pcosetOK 100 7 (HP.F 0) u8P r8P = true :=
  and_split kCos

theorem coset16 : cosetOK 100 b0T u16T u16CosetT = true := by
  have e : b0T = tabP 100 7 (HP.F 0) := aT_eq
  rw [e, u16T, u16CosetT, tabsOf, tabsOf, mapW, mapW, cosetOK_tabP hsz ppA (ppL u16W) (ppL u16CosetW)]
  exact kCosP.1

theorem coset8 : cosetOK 100 b0T u8T u8CosetT = true := by
  have e : b0T = tabP 100 7 (HP.F 0) := aT_eq
  rw [e, u8T, u8CosetT, tabsOf, tabsOf, mapW, mapW, cosetOK_tabP hsz ppA (ppL u8W) (ppL u8CosetW)]
  exact kCosP.2

theorem cos_map (ws : List (List Int)) : ∀ {l : List Nat}, (∀ r ∈ l, PP 100 7 r) →
    (l.map (tabP 100 7)).map (fun r => (cbP.map (tabP 100 7)).countP fun c =>
        normAll 100 ((ws.map pw).map (tabP 100 7)) (compT 100 r c)) =
      l.map (cosCnt (ws.map pw))
  | [], _ => rfl
  | r :: l, h => by
    have hrp := h r List.mem_cons_self
    rw [List.map_cons, List.map_cons, List.map_cons,
      cos_map ws fun s hs => h s (List.mem_cons_of_mem _ hs)]
    congr 1
    unfold cosCnt
    rw [List.countP_map]
    refine countP_congr' fun c hc => ?_
    simp only [Function.comp_apply]
    rw [compT_tabP' hrp (ppcb c hc), normAll_tabP hsz (ppL ws) (hrp.pc (ppcb c hc))]

theorem sum_rec {l : List Nat} {f : Nat → Nat} {K : Nat → Nat} {m : Nat} (hl : l.length = m)
    (h : ∀ i < m, f (l.getD i 0) = K i) : (l.map f).sum = ((List.range m).map K).sum := by
  congr 1
  apply List.ext_getElem (by simp [hl])
  intro i h1 h2
  have hi : i < m := by simpa using h2
  rw [List.getElem_map, List.getElem_map, List.getElem_range, ← h i hi,
    List.getD_eq_getElem _ _ (by simpa using h1)]

#kc_forall_chunks cos16All (fun i => cos16T i = true) 15 CertificateChecks.KernelKGC31HS.cos16T 1

#kc_forall_chunks cos8All (fun i => cos8T i = true) 7 CertificateChecks.KernelKGC31HS.cos8T 1

theorem ptEq_eq {T b s : Nat} (hT : PP 100 7 T) (hb : PP 100 7 b) (hs : PP 100 7 s) :
    ptEq T b s = Nat.beq (pc 100 7 T b) (pc 100 7 s T) := by
  change ptEq T b s = Nat.beq (pcomp 100 7 (mask 7) T b) (pcomp 100 7 (mask 7) s T)
  rw [← eqA_PP (hT.mul hb) (hs.mul hT)]
  apply Bool.eq_iff_iff.2
  unfold ptEq CFSG.Monster.B.Co2.Native.eqA
  rw [CFSG.Monster.B.Co2.allLt_iff, CFSG.KS.Raw.Orb.allN_iff]
  refine forall_congr' fun p => forall_congr' fun hp => ?_
  rw [CFSG.KC.Child3.unpack_get' hp, CFSG.KC.Child3.unpack_get' hp, CFSG.KS.PF.pg_pcomp (by norm_num) hp,
    CFSG.KS.PF.pg_pcomp (by norm_num) hp, Nat.beq_eq, beq_iff_eq]

theorem preFT_of {nb ns : Nat} {B S : Nat → Nat} {L T : Nat} {τ : Nat → Nat}
    (hB : ∀ j < nb, PP 100 7 (B j))
    (hO : ∀ m < ns, ∀ q < 100, pg 7 (mask 7) L (pg 7 (mask 7) (S m) q) = pg 7 (mask 7) L q)
    (hT : PP 100 7 T) (hτ : ∀ x < 100, τ x = pg 7 (mask 7) T x) (h : pnormT nb ns B S T = true) :
    preFT nb B L τ = true := by
  unfold pnormT at h
  unfold preFT
  rw [List.all_eq_true] at h ⊢
  intro b hb
  obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hb
  obtain ⟨s, hs, hst⟩ := List.any_eq_true.1 (h _ hb)
  obtain ⟨m, hm, rfl⟩ := List.mem_map.1 hs
  have hp := (CFSG.KS.Raw.Orb.allN_iff.1 hst) 0 (by norm_num)
  rw [Nat.beq_eq] at hp
  have h0 : pg 7 (mask 7) T 0 < 100 := hT.2.1 0 (by norm_num)
  have hb0 : pg 7 (mask 7) (B j) 0 < 100 := (hB j (List.mem_range.1 hj)).2.1 0 (by norm_num)
  rw [Nat.beq_eq, hτ _ hb0, hτ 0 (by norm_num), hp, hO m (List.mem_range.1 hm) _ h0]

theorem pnormF_eq {nb ns : Nat} {B S P : Nat → Nat} {T : Nat} {τ : Nat → Nat}
    (hB : ∀ j < nb, PP 100 7 (B j)) (hτ : ∀ x < 100, τ x = pg 7 (mask 7) T x) :
    pnormF nb ns B S P τ = pnormL nb ns B S P T := by
  unfold pnormF pnormL ptB5
  refine all_congr' fun b hb => ?_
  obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hb
  have hbP := hB j (List.mem_range.1 hj)
  refine any_congr' fun m _ => ?_
  rw [hτ 0 (by norm_num), hτ _ (hbP.2.1 0 (by norm_num))]
  congr 1
  apply Bool.eq_iff_iff.2
  rw [CFSG.KS.Raw.Orb.allN_iff, CFSG.KS.Raw.Orb.allN_iff]
  refine forall_congr' fun p => forall_congr' fun hp => ?_
  rw [hτ _ (hbP.2.1 p (by omega)), hτ p (by omega)]

theorem bool_and_of {a b : Bool} (h : b = true → a = true) : b = (a && b) := by
  cases b <;> simp_all

theorem kOrbLP : (∀ m < 16, ∀ q < 100,
      pg 7 (mask 7) (OrbL16 0) (pg 7 (mask 7) (SP16 m) q) = pg 7 (mask 7) (OrbL16 0) q) ∧
    ∀ m < 8, ∀ q < 100, pg 7 (mask 7) (OrbL8 0) (pg 7 (mask 7) (SP8 m) q) = pg 7 (mask 7) (OrbL8 0) q := by
  have h := kOrbL
  rw [Bool.and_eq_true, List.all_eq_true, List.all_eq_true] at h
  exact ⟨fun m hm q hq => Nat.eq_of_beq_eq_true
      (CFSG.KS.Raw.Orb.allN_iff.1 (h.1 m (List.mem_range.2 hm)) q hq),
    fun m hm q hq => Nat.eq_of_beq_eq_true
      (CFSG.KS.Raw.Orb.allN_iff.1 (h.2 m (List.mem_range.2 hm)) q hq)⟩

theorem kRecP :(∀ m < 16, SP16 m = pmask 100 7 u16P m) ∧ (∀ m < 8, SP8 m = pmask 100 7 u8P m) ∧
    (∀ j < 4, B16 j = pw (u16W.getD j [])) ∧ (∀ j < 3, B8 j = pw (u8W.getD j [])) ∧
    (∀ i < 15, R16 i = pw (u16CosetW.getD i [])) ∧ (∀ i < 7, R8 i = pw (u8CosetW.getD i [])) := by
  have h := kRec
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨⟨⟨a, b⟩, c⟩, d⟩, e⟩, f⟩ := h
  exact ⟨fun m hm => Nat.eq_of_beq_eq_true (a m hm), fun m hm => Nat.eq_of_beq_eq_true (b m hm),
    fun m hm => Nat.eq_of_beq_eq_true (c m hm), fun m hm => Nat.eq_of_beq_eq_true (d m hm),
    fun m hm => Nat.eq_of_beq_eq_true (e m hm), fun m hm => Nat.eq_of_beq_eq_true (f m hm)⟩

theorem basis_rec {ws : List (List Int)} {B : Nat → Nat} {k : Nat} (hl : ws.length = k)
    (hB : ∀ j < k, B j = pw (ws.getD j [])) : ws.map pw = (List.range k).map B := by
  apply List.ext_getElem (by simp [hl])
  intro j h1 h2
  have hj : j < k := by simpa using h2
  rw [List.getElem_map, List.getElem_map, List.getElem_range, hB j hj,
    List.getD_eq_getElem _ _ (by simpa using h1)]

theorem span_rec {bs : List Nat} {S : Nat → Nat} {k : Nat} (hl : 2 ^ bs.length = k)
    (hS : ∀ m < k, S m = pmask 100 7 bs m) : pspan 100 7 bs = (List.range k).map S := by
  rw [pspan, hl]
  exact List.map_congr_left fun m hm => (hS m (List.mem_range.1 hm)).symm

theorem norm_rec {ws : List (List Int)} {B S : Nat → Nat} {nb ns : Nat} (hl : ws.length = nb)
    (hns : 2 ^ nb = ns) (hB : ∀ j < nb, B j = pw (ws.getD j []))
    (hS : ∀ m < ns, S m = pmask 100 7 (ws.map pw) m) {T : Nat} (hT : PP 100 7 T) :
    pnormAll 100 7 (ws.map pw) T (pinv 100 7 T) = pnormT nb ns B S T := by
  have hsp := span_rec (by rw [List.length_map, hl, hns]) hS
  unfold pnormAll pnormT
  rw [hsp, basis_rec hl hB]
  refine all_congr' fun b hb => any_congr' fun s hs => ?_
  obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hb
  obtain ⟨m, hm, rfl⟩ := List.mem_map.1 hs
  have hbP : PP 100 7 (B j) := by
    rw [hB j (List.mem_range.1 hj)]
    exact ppw' _
  have hsP : PP 100 7 (S m) := by
    rw [hS m (List.mem_range.1 hm)]
    exact PP_pmask hsz _ (ppL ws) m
  rw [← beq_comm_conj hT hbP hsP, ptEq_eq hT hbP hsP]

@[expose] def InHS (x : Nat) : Prop := PP 100 7 x ∧ CFSG.KC.HeGlueK.sg 100 7 x ∈ hs100P

theorem InHS.mul {a b : Nat} (ha : InHS a) (hb : InHS b) : InHS (pc 100 7 a b) := by
  have e : CFSG.KC.HeGlueK.sg 100 7 (pc 100 7 a b) =
      CFSG.KC.HeGlueK.sg 100 7 a * CFSG.KC.HeGlueK.sg 100 7 b := CFSG.KC.HeGlueK.sg_pcomp ha.1 hb.1
  exact ⟨ha.1.pc hb.1, e ▸ mul_mem ha.2 hb.2⟩

@[expose] noncomputable def hsMemK (G : Nat) : Bool :=
  Nat.beq (Nat.shiftRight G (100 * 7)) 0 && allN 100 (fun t => Nat.blt (pg 7 (mask 7) G t) 100) &&
    siftK 100 7 (mask 7) (100 * 7) (pidn 100 7) HC.LR HC.TRI HC.BP 5 0 G

theorem inHS_of {G : Nat} (hG : PP 100 7 G) (h : hsMemK G = true) : InHS G := by
  refine ⟨hG, ?_⟩
  rw [hs100P_eq_original]
  exact (siftA_iff_mem_originalSubgroup hs100ChainArrays (by norm_num) hs100_chain_check.1
    (CFSG.KC.HeGlueK.rep_sg hG)).1 (siftP rfl h)

theorem eqB5 {x y : Nat} (hx : InHS x) (hy : InHS y)
    (h : ∀ p < 5, pg 7 (mask 7) x p = pg 7 (mask 7) y p) : x = y := by
  have hf := baseFaithful_of_valid hs100Chain_valid
  have hb : hs100Chain.base.toList.map Fin.val = [0, 1, 2, 3, 4] := by rfl
  rw [hb] at hf
  rw [CFSG.KC.HeGlueK.PP_eq_iff hx.1 hy.1]
  have hm : (CFSG.KC.HeGlueK.sg 100 7 y)⁻¹ * CFSG.KC.HeGlueK.sg 100 7 x ∈
      hs100Chain.originalSubgroup := by
    rw [← hs100P_eq_original]
    exact mul_mem (inv_mem hy.2) hx.2
  have h1 := hf _ hm fun q hq => by
    have hq5 : (q : Nat) < 5 := by simp at hq; omega
    rw [Equiv.Perm.mul_apply, Equiv.Perm.inv_eq_iff_eq]
    apply Fin.ext
    rw [← CFSG.KC.HeGlueK.rep_sg hx.1 q, ← CFSG.KC.HeGlueK.rep_sg hy.1 q,
      CFSG.KC.Child3.unpack_get' q.2, CFSG.KC.Child3.unpack_get' q.2]
    exact h q hq5
  exact (inv_mul_eq_one.1 h1).symm

theorem ptB5_eq {T b s : Nat} (hT : InHS T) (hb : InHS b) (hs : InHS s) :
    ptB5 T b s = ptEq T b s := by
  rw [ptEq_eq hT.1 hb.1 hs.1]
  apply Bool.eq_iff_iff.2
  rw [Nat.beq_eq]
  unfold ptB5
  rw [CFSG.KS.Raw.Orb.allN_iff]
  constructor
  · intro h
    refine eqB5 (hT.mul hb) (hs.mul hT) fun p hp => ?_
    have e1 : pg 7 (mask 7) (pc 100 7 T b) p = pg 7 (mask 7) T (pg 7 (mask 7) b p) :=
      CFSG.KS.PF.pg_pcomp (by norm_num) (by omega)
    have e2 : pg 7 (mask 7) (pc 100 7 s T) p = pg 7 (mask 7) s (pg 7 (mask 7) T p) :=
      CFSG.KS.PF.pg_pcomp (by norm_num) (by omega)
    rw [e1, e2]
    exact Nat.eq_of_beq_eq_true (h p hp)
  · intro e p hp
    have e1 : pg 7 (mask 7) (pc 100 7 T b) p = pg 7 (mask 7) T (pg 7 (mask 7) b p) :=
      CFSG.KS.PF.pg_pcomp (by norm_num) (by omega)
    have e2 : pg 7 (mask 7) (pc 100 7 s T) p = pg 7 (mask 7) s (pg 7 (mask 7) T p) :=
      CFSG.KS.PF.pg_pcomp (by norm_num) (by omega)
    rw [Nat.beq_eq, ← e1, ← e2, e]

theorem pnormL_eq {nb ns : Nat} {B S P : Nat → Nat} (hB : ∀ j < nb, InHS (B j))
    (hS : ∀ m < ns, InHS (S m))
    (hP : ∀ m < ns, ∀ x < 100, tbit (P x) (pg 7 (mask 7) (S m) x) m = true) {T : Nat}
    (hT : InHS T) : pnormL nb ns B S P T = pnormT nb ns B S T := by
  unfold pnormL pnormT
  refine all_congr' fun b hb => ?_
  obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hb
  rw [List.any_map]
  refine any_congr' fun m hm => ?_
  change _ = ptEq T (B j) (S m)
  rw [ptB5_eq hT (hB j (List.mem_range.1 hj)) (hS m (List.mem_range.1 hm))]
  cases h : ptEq T (B j) (S m)
  · simp
  · have hp := (CFSG.KS.Raw.Orb.allN_iff.1 h) 0 (by norm_num)
    rw [Nat.beq_eq] at hp
    rw [hp, hP m (List.mem_range.1 hm) _ (hT.1.2.1 0 (by norm_num))]
    rfl

theorem kPTP : (∀ m < 16, ∀ x < 100, tbit (PT16 x) (pg 7 (mask 7) (SP16 m) x) m = true) ∧
    ∀ m < 8, ∀ x < 100, tbit (PT8 x) (pg 7 (mask 7) (SP8 m) x) m = true := by
  have h := kPT
  rw [Bool.and_eq_true, List.all_eq_true, List.all_eq_true] at h
  exact ⟨fun m hm x hx => CFSG.KS.Raw.Orb.allN_iff.1 (h.1 m (List.mem_range.2 hm)) x hx,
    fun m hm x hx => CFSG.KS.Raw.Orb.allN_iff.1 (h.2 m (List.mem_range.2 hm)) x hx⟩

theorem kHSs : (((List.range 15).all fun i => hsMemK (R16 i)) &&
    ((List.range 7).all fun i => hsMemK (R8 i)) && ((List.range 4).all fun j => hsMemK (B16 j)) && ((List.range 3).all fun j => hsMemK (B8 j)) &&
    ((List.range 16).all fun m => hsMemK (SP16 m)) && ((List.range 8).all fun m => hsMemK (SP8 m)) &&
    (trPL 100 7 CCA.LR CCA.TR 3).all fun L => L.all hsMemK) = true := by
  quickRfl

theorem kHSsP : (∀ i < 15, hsMemK (R16 i) = true) ∧ (∀ i < 7, hsMemK (R8 i) = true) ∧
    (∀ j < 4, hsMemK (B16 j) = true) ∧ (∀ j < 3, hsMemK (B8 j) = true) ∧
    (∀ m < 16, hsMemK (SP16 m) = true) ∧ (∀ m < 8, hsMemK (SP8 m) = true) ∧
    ∀ L ∈ trPL 100 7 CCA.LR CCA.TR 3, ∀ t ∈ L, hsMemK t = true := by
  have h := kHSs
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨⟨⟨⟨a, b⟩, c⟩, d⟩, e⟩, f⟩, g⟩ := h
  exact ⟨a, b, c, d, e, f, g⟩

theorem trHS : ∀ L ∈ trPL 100 7 CCA.LR CCA.TR 3, ∀ t ∈ L, InHS t := fun L hL t ht =>
  inHS_of (kTRP.1 L hL t ht) (kHSsP.2.2.2.2.2.2 L hL t ht)

theorem foldl_addS {α : Type} (k : α → Nat) : ∀ (T : List α) (a : Nat),
    T.foldl (fun c t => c + k t) a = a + (T.map k).sum
  | [], a => by simp
  | t :: T, a => by
    rw [List.foldl_cons, foldl_addS k T, List.map_cons, List.sum_cons]
    omega

theorem countP_sumI {α : Type} (p : α → Bool) : ∀ T : List α,
    T.countP p = (T.map fun t => if p t then 1 else 0).sum
  | [] => rfl
  | t :: T => by
    rw [List.countP_cons, countP_sumI p T, List.map_cons, List.sum_cons]
    omega

theorem pf_countP (F : Nat → Bool) : ∀ (Ls : List (List Nat)) (g : Nat) (acc : List Nat),
    (pfilterProducts 100 7 (fun _ => true) Ls g acc).countP F =
      pcountProducts 100 7 F Ls g + acc.countP F
  | [], g, acc => by
    simp only [pfilterProducts, pcountProducts, if_true, List.countP_cons]
    omega
  | T :: Ts, g, acc => by
    simp only [pfilterProducts, pcountProducts]
    rw [foldl_addS, Nat.zero_add]
    induction T generalizing acc with
    | nil => simp
    | cons t T ih =>
      rw [List.foldl_cons, ih, pf_countP F Ts, List.map_cons, List.sum_cons]
      omega

theorem sg_pcK {a b : Nat} (ha : PP 100 7 a) (hb : PP 100 7 b) :
    CFSG.KC.HeGlueK.sg 100 7 (pc 100 7 a b) =
      CFSG.KC.HeGlueK.sg 100 7 a * CFSG.KC.HeGlueK.sg 100 7 b :=
  CFSG.KC.HeGlueK.sg_pcomp ha hb

theorem pc_assocP {a b c : Nat} (ha : PP 100 7 a) (hb : PP 100 7 b) (hc : PP 100 7 c) :
    pc 100 7 a (pc 100 7 b c) = pc 100 7 (pc 100 7 a b) c :=
  (CFSG.KC.HeGlueK.PP_eq_iff (ha.pc (hb.pc hc)) ((ha.pc hb).pc hc)).2 (by
    rw [sg_pcK ha (hb.pc hc), sg_pcK hb hc, sg_pcK (ha.pc hb) hc, sg_pcK ha hb, mul_assoc])

theorem pc_ridP {a : Nat} (ha : PP 100 7 a) : pc 100 7 a (pidn 100 7) = a :=
  (CFSG.KC.HeGlueK.PP_eq_iff (ha.pc (PP.id hsz)) ha).2 (by
    rw [sg_pcK ha (PP.id hsz), CFSG.KC.HeGlueK.sg_id hsz, mul_one])

theorem pcount_shift (F : Nat → Bool) {R : Nat} (hR : PP 100 7 R) : ∀ (Ls : List (List Nat)),
    (∀ T ∈ Ls, ∀ t ∈ T, PP 100 7 t) → ∀ g, PP 100 7 g →
    pcountProducts 100 7 (fun x => F (pc 100 7 R x)) Ls g = pcountProducts 100 7 F Ls (pc 100 7 R g)
  | [], _, g, _ => by simp only [pcountProducts]
  | T :: Ts, hL, g, hg => by
    simp only [pcountProducts]
    rw [foldl_addS, foldl_addS]
    congr 2
    refine List.map_congr_left fun t ht => ?_
    have htP := hL T List.mem_cons_self t ht
    rw [pcount_shift F hR Ts (fun T' hT' => hL T' (List.mem_cons_of_mem _ hT')) _ (hg.pc htP),
      pc_assocP hR hg htP]

theorem pg_stepF {g : Nat → Nat} {G t : Nat} (hg : ∀ x < 100, g x = pg 7 (mask 7) G x)
    (ht : PP 100 7 t) : ∀ x < 100, g (pg 7 (mask 7) t x) = pg 7 (mask 7) (pc 100 7 G t) x :=
  fun x hx => by
    have e : pg 7 (mask 7) (pc 100 7 G t) x = pg 7 (mask 7) G (pg 7 (mask 7) t x) :=
      CFSG.KS.PF.pg_pcomp (by norm_num) hx
    rw [hg _ (ht.2.1 x hx), e]

theorem cosF_eq {f : (Nat → Nat) → Bool} {F : Nat → Bool}
    (hf : ∀ τ G, InHS G → (∀ x < 100, τ x = pg 7 (mask 7) G x) → f τ = F G) :
    ∀ (Ls : List (List Nat)), Ls ≠ [] → (∀ T ∈ Ls, ∀ t ∈ T, InHS t) → ∀ g G, InHS G →
    (∀ x < 100, g x = pg 7 (mask 7) G x) → cosF f Ls g = pcountProducts 100 7 F Ls G
  | [], h, _, _, _, _, _ => absurd rfl h
  | [T], _, hL, g, G, hG, hg => by
    simp only [cosF, pcountProducts]
    rw [foldl_addS, Nat.zero_add, countP_sumI]
    congr 1
    refine List.map_congr_left fun t ht => ?_
    have htH := hL T List.mem_cons_self t ht
    rw [hf _ _ (hG.mul htH) (pg_stepF hg htH.1)]
  | T :: T' :: Ts, _, hL, g, G, hG, hg => by
    simp only [cosF]
    rw [pcountProducts, foldl_addS, foldl_addS]
    congr 2
    refine List.map_congr_left fun t ht => ?_
    have htH := hL T List.mem_cons_self t ht
    exact cosF_eq hf (T' :: Ts) (List.cons_ne_nil _ _)
      (fun T'' hT'' => hL T'' (List.mem_cons_of_mem _ hT'')) _ _ (hG.mul htH) (pg_stepF hg htH.1)

theorem cosCnt_rec {ws rs : List (List Int)} {B S R P K : Nat → Nat} {nb ns L : Nat}
    (hl : ws.length = nb) (hns : 2 ^ nb = ns) (hB : ∀ j < nb, B j = pw (ws.getD j []))
    (hS : ∀ m < ns, S m = pmask 100 7 (ws.map pw) m) (hR : ∀ i < rs.length, R i = pw (rs.getD i []))
    (hO : ∀ m < ns, ∀ q < 100, pg 7 (mask 7) L (pg 7 (mask 7) (S m) q) = pg 7 (mask 7) L q)
    (hPT : ∀ m < ns, ∀ x < 100, tbit (P x) (pg 7 (mask 7) (S m) x) m = true)
    (hBH : ∀ j < nb, hsMemK (B j) = true) (hSH : ∀ m < ns, hsMemK (S m) = true)
    {i : Nat} (hi : i < rs.length) (hRH : hsMemK (R i) = true) (h : cosT nb ns B S R P K L i = true) :
    cosCnt (ws.map pw) ((rs.map pw).getD i 0) = K i := by
  have e : (rs.map pw).getD i 0 = R i := by
    rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map, hR i hi,
      List.getD_eq_getElem _ _ hi]
  rw [e, ← Nat.eq_of_beq_eq_true h]
  unfold cosCnt
  have hRP : PP 100 7 (R i) := by rw [hR i hi]; exact ppw' _
  have hBP : ∀ j < nb, PP 100 7 (B j) := fun j hj => by rw [hB j hj]; exact ppw' _
  have hSP : ∀ m < ns, PP 100 7 (S m) := fun m hm => by rw [hS m hm]; exact PP_pmask hsz _ (ppL ws) m
  have h1 : cbP.countP (fun c => pnormAll 100 7 (ws.map pw) (pc 100 7 (R i) c)
      (pinv 100 7 (pc 100 7 (R i) c))) = cbP.countP fun c => pnormT nb ns B S (pc 100 7 (R i) c) :=
    countP_congr' fun c hc => norm_rec hl hns hB hS (hRP.pc (ppcb c hc))
  rw [h1, cbP, pf_countP, List.countP_nil, Nat.add_zero,
    pcount_shift _ hRP _ kTRP.1 _ (PP.id hsz), pc_ridP hRP]
  exact (cosF_eq (fun τ G hG hτ => by
      rw [pnormF_eq hBP hτ, pnormL_eq (fun j hj => inHS_of (hBP j hj) (hBH j hj))
        (fun m hm => inHS_of (hSP m hm) (hSH m hm)) hPT hG]
      exact (bool_and_of (preFT_of hBP hO hG.1 hτ)).symm) _
    (by simp [trPL]) trHS _ _ (inHS_of hRP hRH) fun _ _ => rfl).symm

theorem kSumP : ((List.range 15).map K16).sum = 11520 ∧ ((List.range 7).map K8).sum = 10752 := by
  have h := kSum
  rw [Bool.and_eq_true] at h
  exact ⟨Nat.eq_of_beq_eq_true h.1, Nat.eq_of_beq_eq_true h.2⟩

theorem ccount16 : cosetCount 100 cbT u16CosetT (normAll 100 u16T) = 11520 := by
  rw [cosetCount, cbT_eq, u16CosetT, u16T, tabsOf, tabsOf, mapW, mapW, cos_map u16W (ppL u16CosetW),
    ← kSumP.1]
  refine sum_rec (by simp [u16CosetW]) fun i hi => ?_
  exact cosCnt_rec (rs := u16CosetW) (by rfl) (by rfl) kRecP.2.2.1 kRecP.1 kRecP.2.2.2.2.1 kOrbLP.1
    kPTP.1 kHSsP.2.2.1 kHSsP.2.2.2.2.1 (by simpa [u16CosetW] using hi) (kHSsP.1 i hi) (cos16All i hi)

theorem ccount8 : cosetCount 100 cbT u8CosetT (normAll 100 u8T) = 10752 := by
  rw [cosetCount, cbT_eq, u8CosetT, u8T, tabsOf, tabsOf, mapW, mapW, cos_map u8W (ppL u8CosetW),
    ← kSumP.2]
  refine sum_rec (by simp [u8CosetW]) fun i hi => ?_
  exact cosCnt_rec (rs := u8CosetW) (by rfl) (by rfl) kRecP.2.2.2.1 kRecP.2.1 kRecP.2.2.2.2.2 kOrbLP.2
    kPTP.2 kHSsP.2.2.2.1 kHSsP.2.2.2.2.2.1 (by simpa [u8CosetW] using hi) (kHSsP.2.1 i hi)
    (cos8All i hi)

theorem mzW {bs : List Nat} (hb : ∀ b ∈ bs, PP 100 7 b) (ws : List (List Int)) (ms : List (List Nat)) :
    ((permsOf ws).zip ms).all (fun p => masksOK 100 (bs.map (tabP 100 7)) (toTable p.1) p.2) =
      ((ws.map pw).zip ms).all (fun p => pmasksOK 100 7 bs p.1 p.2) := by
  rw [permsOf, List.zip_map_left, List.zip_map_left, List.all_map, List.all_map]
  refine all_congr' fun p _ => ?_
  simp only [Function.comp_apply, Prod.map_fst, Prod.map_snd, id]
  rw [toTable_tab, masksOK_tabP hsz hb (ppw' _)]

theorem kMasksP : ((m16GenW.map pw).zip m16Masks).all (fun p => pmasksOK 100 7 u16P p.1 p.2) = true ∧
    ((n8GenW.map pw).zip n8Masks).all (fun p => pmasksOK 100 7 u8P p.1 p.2) = true :=
  and_split kMasks

theorem masks16 : ((permsOf m16GenW).zip m16Masks).all
    (fun p => masksOK 100 u16T (toTable p.1) p.2) = true := by
  rw [u16T, tabsOf, mapW, mzW (ppL u16W)]
  exact kMasksP.1

theorem masks8 : ((permsOf n8GenW).zip n8Masks).all
    (fun p => masksOK 100 u8T (toTable p.1) p.2) = true := by
  rw [u8T, tabsOf, mapW, mzW (ppL u8W)]
  exact kMasksP.2

theorem kSIP : ((List.range 2).all fun j => permOK 100 7 (mask 7) (100 * 7) (CM16.S j) (CM16.SI j)) =
      true ∧ ((List.range 2).all fun j => permOK 100 7 (mask 7) (100 * 7) (CN8.S j) (CN8.SI j)) =
      true := and_split kSI

theorem idImg : imageList (1 : Equiv.Perm (Fin 100)) = (unpack 100 7 (pidn 100 7)).toList :=
  CertificateChecks.KernelLC.ExcGlue.one_img (idK_of_szOK hsz)

theorem permsOf_len (ws : List (List Int)) : (permsOf ws).length = ws.length := by
  simp [permsOf]

theorem evalM16 {wd : List Int} (h : lettersK 2 wd = true) :
    imageList (evalCodes (permsOf m16GenW) wd) =
      (unpack 100 7 (wordK 100 7 (mask 7) (pidn 100 7) CM16.S CM16.SI wd)).toList := by
  refine evalCodes_img hsz (gens_img (ws := m16GenW) (m := 2) rfl kGensP.2.2.2.1) (fun j hj => ?_)
    idImg h
  have hj' : j < 2 := by simpa [m16GenW] using hj
  exact List.all_eq_true.1 kSIP.1 j (List.mem_range.2 hj')

theorem evalN8 {wd : List Int} (h : lettersK 2 wd = true) :
    imageList (evalCodes (permsOf n8GenW) wd) =
      (unpack 100 7 (wordK 100 7 (mask 7) (pidn 100 7) CN8.S CN8.SI wd)).toList := by
  refine evalCodes_img hsz (gens_img (ws := n8GenW) (m := 2) rfl kGensP.2.2.2.2.1)
    (fun j hj => ?_) idImg h
  have hj' : j < 2 := by simpa [n8GenW] using hj
  exact List.all_eq_true.1 kSIP.2 j (List.mem_range.2 hj')

theorem u16in : ((List.range 4).all fun i => tblEq 100 (u16T.getD i (idT 100))
    (toTable (evalCodes (permsOf m16GenW) (u16InM16.getD i [])))) = true := by
  rw [List.all_eq_true]
  intro i hi
  have hi4 : i < 4 := List.mem_range.1 hi
  have h := allN_spec kU16 i (by simpa [u16InM16] using hi4)
  obtain ⟨h1, h2⟩ := CertificateChecks.KernelLC.ExcGlue.and_of_bAnd h
  have hP : PP 100 7 (pw (u16W.getD i [])) := ppw' _
  rw [CFSG.KS.SporSch.CodesImg.toTable_eq_arrTable_of_img (evalM16 h1), Nat.eq_of_beq_eq_true h2,
    u16T, tabsOf, mapW, getD_map_tabP hsz]
  have hl : i < u16W.length := by simpa [u16W] using hi4
  have e : (u16W.map pw).getD i (pidn 100 7) = pw (u16W.getD i []) := by
    rw [List.getD_eq_getElem _ _ (by simpa using hl), List.getElem_map,
      List.getD_eq_getElem _ _ hl]
  rw [e]
  exact (tblEq_tabP hP hP).trans (Nat.beq_refl _)

theorem kPerfW {j : Nat} (hj : j < 2) :
    lettersK 2 ((n8PerfW.getD j []).getD 0 []) = true ∧ lettersK 2 ((n8PerfW.getD j []).getD 1 []) = true ∧
      Nat.beq (pw (n8GenW.getD j []))
        (pc 100 7 (pc 100 7 (pc 100 7
          (wordK 100 7 (mask 7) (pidn 100 7) CN8.S CN8.SI ((n8PerfW.getD j []).getD 0 []))
          (wordK 100 7 (mask 7) (pidn 100 7) CN8.S CN8.SI ((n8PerfW.getD j []).getD 1 [])))
          (pinv 100 7 (wordK 100 7 (mask 7) (pidn 100 7) CN8.S CN8.SI ((n8PerfW.getD j []).getD 0 []))))
          (pinv 100 7 (wordK 100 7 (mask 7) (pidn 100 7) CN8.S CN8.SI ((n8PerfW.getD j []).getD 1 []))))
        = true := by
  have h := List.all_eq_true.1 kPerf j (List.mem_range.2 hj)
  obtain ⟨h1, h2⟩ := CertificateChecks.KernelLC.ExcGlue.and_of_bAnd h
  obtain ⟨h2, h3⟩ := CertificateChecks.KernelLC.ExcGlue.and_of_bAnd h2
  exact ⟨h1, h2, h3⟩

theorem kPerfI : (List.range 2).all (fun j =>
    permOK 100 7 (mask 7) (100 * 7)
      (wordK 100 7 (mask 7) (pidn 100 7) CN8.S CN8.SI ((n8PerfW.getD j []).getD 0 []))
      (pinv 100 7 (wordK 100 7 (mask 7) (pidn 100 7) CN8.S CN8.SI ((n8PerfW.getD j []).getD 0 []))) &&
    permOK 100 7 (mask 7) (100 * 7)
      (wordK 100 7 (mask 7) (pidn 100 7) CN8.S CN8.SI ((n8PerfW.getD j []).getD 1 []))
      (pinv 100 7 (wordK 100 7 (mask 7) (pidn 100 7) CN8.S CN8.SI ((n8PerfW.getD j []).getD 1 []))))
    = true := by quickRfl

theorem perf : ((List.range 2).all fun j => tblEq 100 (wordT 100 gensT (n8GenW.getD j []))
    (toTable (commOf (permsOf n8GenW) (n8PerfW.getD j [])))) = true := by
  rw [List.all_eq_true]
  intro j hj
  have hj2 : j < 2 := List.mem_range.1 hj
  obtain ⟨l1, l2, h3⟩ := kPerfW hj2
  obtain ⟨i1, i2⟩ := Bool.and_eq_true_iff.1 (List.all_eq_true.1 kPerfI j hj)
  have iu := evalN8 l1
  have iv := evalN8 l2
  have himg := mulK_rep hsz (mulK_rep hsz (mulK_rep hsz iu iv) (invK_rep iu i1)) (invK_rep iv i2)
  unfold pc at h3
  rw [commOf, CFSG.KS.SporSch.CodesImg.toTable_eq_arrTable_of_img himg, wT,
    ← Nat.eq_of_beq_eq_true h3]
  have hP : PP 100 7 (pw (n8GenW.getD j [])) := ppw' _
  exact (tblEq_tabP hP hP).trans (Nat.beq_refl _)

theorem qT_get (i : Nat) : qT.getD i (idT 100) = tabP 100 7 (qP.getD i (pidn 100 7)) := by
  rw [qT, tabsOf, mapW, getD_map_tabP hsz]
  rfl

theorem ppQ (i : Nat) : PP 100 7 (qP.getD i (pidn 100 7)) := PP_getD hsz (ppL qGenW) i

theorem qmem {i : Nat} (hi : i < 3) : qP.getD i (pidn 100 7) ∈ qP := by
  rw [List.getD_eq_getElem _ _ (by simpa [qP, qGenW] using hi)]
  exact List.getElem_mem _

theorem kQP : qP.all (pcommAll 100 7 u8P) = true ∧ qP.all (fun g => pcommAll 100 7 qP g) = true ∧
    ((List.range 3).all fun i => Nat.beq (pc 100 7 (qP.getD i (pidn 100 7)) (qP.getD i (pidn 100 7)))
      (pmask 100 7 u8P (qSq.getD i 0))) = true := by
  have h := kQ
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem qComm8 : ((List.range 3).all fun i => commAll 100 u8T (qT.getD i (idT 100))) = true := by
  rw [List.all_eq_true]
  intro i hi
  have hi3 := List.mem_range.1 hi
  rw [qT_get, u8T, tabsOf, mapW, commAll_tabP (ppL u8W) (ppQ i)]
  exact List.all_eq_true.1 kQP.1 _ (qmem hi3)

theorem qComm : ((List.range 3).all fun i => (List.range 3).all fun j =>
    commT 100 (qT.getD i (idT 100)) (qT.getD j (idT 100))) = true := by
  rw [List.all_eq_true]
  intro i hi
  rw [List.all_eq_true]
  intro j hj
  have hi3 := List.mem_range.1 hi
  have hj3 := List.mem_range.1 hj
  rw [qT_get, qT_get, commT_tabP (ppQ i) (ppQ j)]
  have h := List.all_eq_true.1 kQP.2.1 _ (qmem hi3)
  exact List.all_eq_true.1 h _ (qmem hj3)

theorem qSqOK : ((List.range 3).all fun i => tblEq 100
    (compT 100 (qT.getD i (idT 100)) (qT.getD i (idT 100))) (maskProd 100 u8T (qSq.getD i 0))) =
    true := by
  rw [List.all_eq_true]
  intro i hi
  have h := List.all_eq_true.1 kQP.2.2 i hi
  rw [qT_get, compT_tabP' (ppQ i) (ppQ i), u8T, tabsOf, mapW, maskProd_tabP hsz _ (ppL u8W),
    tblEq_tabP ((ppQ i).pc (ppQ i)) (PP_pmask hsz _ (ppL u8W) _)]
  exact h

open CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native CFSG.Sporadic.Th.Native
  CFSG.Quasithin.KGC31.Native CFSG.Quasithin.KGC31.HS CFSG.RankThree.Native in
open Certificates in
theorem cert7220 :
    (orbCheck 100 5 invs [lineT 0] cands5 = true) ∧
    (actCheck 100 5 invs [lineT 2] = true) ∧ (actCheck 100 5 invs [lineT 23] = true) ∧
    (orbCheck 100 7 invs [x7T] cands7 = true) ∧ (actCheck 100 11 invs [x11T] = true) ∧
    (((List.range 7).all fun k => invOK 100 (candT k) (invT 100 (candT k))) = true) ∧
    (ebasisOK 100 u16T = true) ∧ (ebasisOK 100 u8T = true) ∧
    (cbT.countP (commAll 100 u16T) = 16) ∧ (cbT.countP (commAll 100 u8T) = 64) ∧
    (cosetOK 100 b0T u16T u16CosetT = true) ∧ (cosetOK 100 b0T u8T u8CosetT = true) ∧
    (cosetCount 100 cbT u16CosetT (normAll 100 u16T) = 11520) ∧
    (cosetCount 100 cbT u8CosetT (normAll 100 u8T) = 10752) ∧
    (m16Chain.check = true) ∧ (m16Chain.orderCertificate = 5760) ∧
    (n8Chain.check = true) ∧ (n8Chain.orderCertificate = 10752) ∧
    (qChain.check = true) ∧ (qChain.orderCertificate = 64) ∧
    (((permsOf m16GenW).zip m16Masks).all (fun p => masksOK 100 u16T (toTable p.1) p.2) =
      true) ∧
    (((permsOf n8GenW).zip n8Masks).all (fun p => masksOK 100 u8T (toTable p.1) p.2) = true) ∧
    (((List.range 4).all fun i => tblEq 100 (u16T.getD i (idT 100))
      (toTable (evalCodes (permsOf m16GenW) (u16InM16.getD i [])))) = true) ∧
    (((List.range 2).all fun j => tblEq 100 (wordT 100 gensT (n8GenW.getD j []))
      (toTable (commOf (permsOf n8GenW) (n8PerfW.getD j [])))) = true) ∧
    (((List.range 3).all fun i => commAll 100 u8T (qT.getD i (idT 100))) = true) ∧
    (((List.range 3).all fun i => (List.range 3).all fun j =>
      commT 100 (qT.getD i (idT 100)) (qT.getD j (idT 100))) = true) ∧
    (((List.range 3).all fun i => tblEq 100
      (compT 100 (qT.getD i (idT 100)) (qT.getD i (idT 100))) (maskProd 100 u8T (qSq.getD i 0))) =
      true) := by
  obtain ⟨m1, m2⟩ := chainK_check (by decide) (by decide) chainM16
  obtain ⟨n1, n2⟩ := chainK_check (by decide) (by decide) chainN8
  obtain ⟨q1, q2⟩ := chainK_check (by decide) (by decide) chainQ
  obtain ⟨-, -, -, o4, o5, o6⟩ := kOrdP
  exact ⟨orb5, act5b, act5a, orb7, act11, candInv, eb16, eb8, cent16, cent8, coset16, coset8,
    ccount16, ccount8, m1, m2.trans o4, n1, n2.trans o5, q1, q2.trans o6, masks16, masks8, u16in,
    perf, qComm8, qComm, qSqOK⟩

end CertificateChecks.KernelKGC31HS

end
