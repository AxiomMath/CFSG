module

public import Certificates.Kernel.LocalComp.L34Bo.CAll
public import Certificates.Kernel.LocalComp.L34Bo.N0
public import Certificates.Kernel.LocalComp.L34Bo.N1
public import Certificates.Kernel.LocalComp.L34Bo.N2
public import Certificates.Kernel.LocalComp.L34Bo.N3
public import Certificates.Kernel.LocalComp.L34Bo.N4
public import Certificates.Kernel.LocalComp.L34Bo.N5
public import Certificates.Kernel.LocalComp.L34Un.Final
import CFSG.Certificates.Kernel.L34KSnd.Tab
import CFSG.Certificates.Kernel.Spor.RawOrbEval
import CFSG.Certificates.Kernel.Spor.PackFld
import CFSG.Certificates.Kernel.L34PreSound

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelLC.L34Bo

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.L34K CFSG.KC.L34Scan
open CFSG.KS.PEnum CFSG.KC.L34KSnd CertificateChecks.KernelLC.L34X CertificateChecks.KernelLC.L34Cert
open CFSG.PSL3Four.Native Certificates.L34Borel
open CFSG.KLie.CT (andB orB notB)

abbrev Cn (p : Nat) : Prop := canonK 42 6 (mask 6) (42 * 6) p = true

theorem andB_eq (a b : Bool) : andB a b = (a && b) := by cases a <;> rfl

theorem notAllNotB {n : Nat} {f : Nat → Bool} :
    notB (allN n fun i => notB (f i)) = true ↔ ∃ i < n, f i = true := by
  rw [notB_iff]
  constructor
  · intro h
    by_contra hn
    have : allN n (fun i => notB (f i)) = true := CFSG.KS.Raw.Orb.allN_iff.2 fun i hi => by
      cases hf : f i
      · rfl
      · exact absurd ⟨i, hi, hf⟩ hn
    rw [this] at h
    exact Bool.noConfusion h
  · rintro ⟨i, hi, hf⟩
    cases h : allN n (fun i => notB (f i))
    · rfl
    · have := CFSG.KS.Raw.Orb.allN_iff.1 h i hi
      rw [hf] at this
      exact Bool.noConfusion this

theorem top : u0iT = unpack 42 6 UI ∧ Cn UI ∧ pcomp 42 6 (mask 6) UI (UE0.G 0) = pidn 42 6 ∧
    pcomp 42 6 (mask 6) (UE0.G 0) UI = pidn 42 6 ∧ Nat.beq (UE0.G 0) (pidn 42 6) = false ∧
    pcomp 42 6 (mask 6) (UE0.G 0) (pcomp 42 6 (mask 6) (UE0.G 0) (UE0.G 0)) = pidn 42 6 ∧
    inS (UE0.G 0) = true := by
  obtain ⟨h1, h⟩ := andT k_top
  obtain ⟨h2, h⟩ := andT h
  obtain ⟨h3, h⟩ := andT h
  obtain ⟨h4, h⟩ := andT h
  obtain ⟨h5, h⟩ := andT h
  obtain ⟨h6, h7⟩ := andT h
  exact ⟨unpack_eq_of_bindArrK h1, h2, Nat.eq_of_beq_eq_true h3, Nat.eq_of_beq_eq_true h4,
    notB_iff.1 h5, Nat.eq_of_beq_eq_true h6, h7⟩

theorem cU : Cn (UE0.G 0) := L34Un.u0_eq.2

theorem cj_eq {x : Nat} (hx : Cn x) : conjU (unpack 42 6 x) = unpack 42 6 (cj x) ∧ Cn (cj x) := by
  unfold conjU conjTab cj
  rw [L34Un.u0_eq.1, top.1, comp_unpack' cU hx, comp_unpack' (canonK_pcomp cU hx) top.2.1]
  exact ⟨rfl, canonK_pcomp (canonK_pcomp cU hx) top.2.1⟩

theorem inS_iff {x : Nat} : inS x = true ↔ ∃ q < 20160, L34S.T q = x := by
  unfold inS
  rw [notAllNotB]
  exact ⟨fun ⟨q, hq, h⟩ => ⟨q, hq, Nat.eq_of_beq_eq_true h⟩, fun ⟨q, hq, h⟩ =>
    ⟨q, hq, by rw [h]; exact Nat.beq_refl x⟩⟩

theorem inSY_iff {j x : Nat} : inSY j x = true ↔ ∃ q < 64, syT j q = x := by
  unfold inSY
  rw [notAllNotB]
  exact ⟨fun ⟨q, hq, h⟩ => ⟨q, hq, Nat.eq_of_beq_eq_true h⟩, fun ⟨q, hq, h⟩ =>
    ⟨q, hq, by rw [h]; exact Nat.beq_refl x⟩⟩

theorem inSYf_eq {j : Nat} (hj : j < 6) (x : Nat) : inSYf j x = inSY j x := by
  unfold inSYf
  cases h : inSY j x
  · rw [andB_eq, andB_eq, Bool.and_false, Bool.and_false]
  · obtain ⟨q, hq, e⟩ := inSY_iff.1 h
    obtain ⟨h1, h2⟩ := andT (CFSG.KS.Raw.Orb.allN_iff.1 (CFSG.KS.Raw.Orb.allN_iff.1 k_fix j hj) q hq)
    rw [← e, h1, h2]
    rfl

theorem foundS {x : Nat} (h : inS x = true) :
    found (indexOf (pts 42 6 20160 L34S.T)) (pts 42 6 20160 L34S.T) (unpack 42 6 x) = true := by
  obtain ⟨q, hq, e⟩ := inS_iff.1 h
  exact found_pts hq e

structure SylF (j : Nat) : Prop where
  size : (sylEnum j).tabs.size = 64
  get : ∀ q < 64, (sylEnum j).tabs[q]! = unpack 42 6 (syT j q)
  ok : enumOK 42 (sylGens[j]!) (sylEnum j) = true
  gens : (sylGens[j]!).size = 4 ∧ ∀ i < 4, (sylGens[j]!)[i]! = unpack 42 6 (syG j i) ∧
    Cn (syG j i) ∧ inS (syG j i) = true
  canon : ∀ q < 64, Cn (syT j q)
  found : ∀ x, Cn x → (found (indexOf (sylEnum j).tabs) (sylEnum j).tabs (unpack 42 6 x) = true ↔
    inSY j x = true)
  conj : ∀ q < 64, inSY j (cj (syT j q)) = true

theorem syl_of {j k cnt : Nat} {G GI T PL POS SRT SRI : Nat → Nat}
    (h : sylK j k cnt G GI T PL POS SRT SRI sylGens[j]! = true) : SylF j := by
  unfold sylK at h
  obtain ⟨hk, h⟩ := andT h
  obtain ⟨hc, h⟩ := andT h
  obtain ⟨hg, h⟩ := andT h
  obtain ⟨hh, h⟩ := andT h
  obtain ⟨hsl, h⟩ := andT h
  obtain ⟨hgi, hq⟩ := andT h
  have hk' := Nat.eq_of_beq_eq_true hk
  have hc' := Nat.eq_of_beq_eq_true hc
  have hGO := gensOK_of hg
  have hpt : ∀ i < cnt, penumPtK 42 6 (mask 6) (42 * 6) false G GI k cnt T PL POS SRT SRI i =
      true := fun i hi => penumSl_spec hsl i (Nat.zero_le _) (by omega) hi
  have hGO' : GensOK 42 6 k G sylGens[j]! := by rw [hk']; exact hGO
  obtain ⟨e1, e2⟩ := penumK_left_sound (cap := 64) (by decide) hGO' hh hpt
  have hq' : ∀ q < 64, syT j q = T q ∧ syPL j q = PL q ∧ inSY j (cj (T q)) = true := fun q hq0 => by
    obtain ⟨a, b⟩ := andT (CFSG.KS.Raw.Orb.allN_iff.1 hq q hq0)
    obtain ⟨b, c⟩ := andT b
    exact ⟨Nat.eq_of_beq_eq_true a, Nat.eq_of_beq_eq_true b, c⟩
  have hcan : ∀ q < 64, Cn (syT j q) := fun q hq0 => by
    rw [(hq' q hq0).1]
    exact penumPt_canon (hpt q (by omega))
  have hE : sylEnum j = penumRec 42 6 cnt T PL := by unfold sylEnum; rw [e1]
  refine ⟨by rw [hE, penumRec_eq, Array.size_ofFn, hc'], fun q hq0 => ?_, by rw [hE]; exact e2,
    ⟨?_, ?_⟩, hcan, ?_, ?_⟩
  · rw [hE, (hq' q hq0).1]
    rw [getElem!_pos _ q (by simp [penumRec]; omega)]
    simp [penumRec]
  · rw [hGO.1]
  · intro i hi
    obtain ⟨a, b⟩ := andT (CFSG.KS.Raw.Orb.allN_iff.1 hgi i hi)
    rw [Nat.eq_of_beq_eq_true b]
    exact ⟨(hGO.2 i hi).1, (hGO.2 i hi).2, a⟩
  · intro x hx
    rw [hE, found_penumRec_iff hpt hx, inSY_iff]
    constructor
    · rintro ⟨q, hq0, e⟩
      exact ⟨q, by omega, by rw [(hq' q (by omega)).1, e]⟩
    · rintro ⟨q, hq0, e⟩
      exact ⟨q, by omega, by rw [← (hq' q hq0).1, e]⟩
  · intro q hq0
    rw [(hq' q hq0).1]
    exact (hq' q hq0).2.2

theorem syl_all : ∀ j < 6, SylF j := by
  intro j hj
  interval_cases j
  exacts [syl_of k_syl0, syl_of k_syl1, syl_of k_syl2, syl_of k_syl3, syl_of k_syl4,
    syl_of k_syl5]

theorem Es_get {j : Nat} (hj : j < 6) :
    ((Array.range 6).map fun j => (sylEnum j).tabs)[j]! = (sylEnum j).tabs := by
  rw [getElem!_pos _ j (by simpa using hj), Array.getElem_map, Array.getElem_range]

theorem idxs_get {j : Nat} (hj : j < 6) :
    (((Array.range 6).map fun j => (sylEnum j).tabs).map indexOf)[j]! =
      indexOf (sylEnum j).tabs := by
  rw [getElem!_pos _ j (by simpa using hj), Array.getElem_map, Array.getElem_map,
    Array.getElem_range]

theorem foundSY {j x : Nat} (hj : j < 6) (hx : Cn x) :
    found (((Array.range 6).map fun j => (sylEnum j).tabs).map indexOf)[j]!
      ((Array.range 6).map fun j => (sylEnum j).tabs)[j]! (unpack 42 6 x) = inSY j x := by
  rw [idxs_get hj, Es_get hj, Bool.eq_iff_iff]
  exact (syl_all j hj).found x hx

theorem commB {x g : Nat} (hx : Cn x) (hg : Cn g) :
    (comp 42 (unpack 42 6 x) (unpack 42 6 g) == comp 42 (unpack 42 6 g) (unpack 42 6 x)) =
      commPt 42 6 x g := by
  rw [Bool.eq_iff_iff, beq_iff_eq, commPt_iff hx hg]

theorem sylOK_all : ∀ j < 6,
    sylOK (indexOf (pts 42 6 20160 L34S.T)) (pts 42 6 20160 L34S.T) j = true := by
  intro j hj
  have F := syl_all j hj
  unfold sylOK
  dsimp only
  rw [F.ok, F.gens.1, F.size]
  simp only [Bool.and_true, Bool.true_and, Bool.and_eq_true, beq_self_eq_true]
  refine ⟨?_, ?_⟩
  · rw [CFSG.KS.BfsReplay.allBelow_iff]
    intro i hi
    rw [(F.gens.2 i hi).1]
    exact foundS (F.gens.2 i hi).2.2
  · rw [CFSG.KS.BfsReplay.allBelow_iff]
    intro q hq
    rw [F.get q hq, (cj_eq (F.canon q hq)).1, F.found _ (cj_eq (F.canon q hq)).2]
    exact F.conj q hq

theorem allBelow_mem {A : Array Tab} {P : Tab → Bool} (h : ∀ x ∈ A, P x = true) :
    (allBelow A.size fun i => P A[i]!) = true := by
  rw [CFSG.KS.BfsReplay.allBelow_iff]
  intro i hi
  rw [getElem!_pos A i hi]
  exact h _ (Array.getElem_mem hi)

theorem cover_ok : coverScan (pts 42 6 20160 L34S.T) ((Array.range 6).map fun j => (sylEnum j).tabs)
    (((Array.range 6).map fun j => (sylEnum j).tabs).map indexOf) = true := by
  unfold coverScan
  rw [CFSG.KS.BfsReplay.allBelow_iff, size_pts]
  intro k hk
  have hx := pinS.canon k hk
  have h := scanSl_spec (L := 1120) (K := 18) (by decide) (by decide) (fun s hs => by
    have h1 := covAll s hs
    unfold cov at h1
    rwa [strictB_app] at h1) k hk
  unfold covK at h
  rw [strictB_app, strictB_app] at h
  obtain ⟨e1, c1⟩ := cj_eq hx
  obtain ⟨e2, c2⟩ := cj_eq c1
  have hinv : (comp 42 (unpack 42 6 (L34S.T k)) (unpack 42 6 (L34S.T k)) == idTab 42) =
      invPt 42 6 (L34S.T k) := by
    rw [Bool.eq_iff_iff, beq_iff_eq, invPt_iff hx]
  rw [pts_get' hk]
  dsimp only
  rw [e1, e2, hinv, commB hx c1, idTab_unpack' hsz42,
    CFSG.KC.L34KSnd.beq_unpack hx (canon_pidn hsz42)]
  simp only [orB_eq, notB_eq] at h
  cases ha : Nat.beq (L34S.T k) (pidn 42 6)
  · cases hb : invPt 42 6 (L34S.T k)
    · simp
    · cases hc : commPt 42 6 (L34S.T k) (cj (L34S.T k))
      · simp
      · rw [ha, hb, hc] at h
        simp only [Bool.false_or, Bool.not_true] at h
        obtain ⟨j, hj, hJ⟩ := notAllNotB.1 (by rw [notB_eq]; exact h)
        simp only [inSYf_eq hj] at hJ
        simp only [Bool.not_true, Bool.or_false, Bool.false_or]
        rw [CFSG.KC.L34KSnd.anyBelow_iff]
        refine ⟨j, hj, ?_⟩
        generalize hC : centTabs 42 (centTabs 42 (centTabs 42 (pts 42 6 20160 L34S.T)
          (unpack 42 6 (L34S.T k))) (unpack 42 6 (cj (L34S.T k))))
          (unpack 42 6 (cj (cj (L34S.T k)))) = C
        refine allBelow_mem (A := C) (P := fun c =>
          found (((Array.range 6).map fun j => (sylEnum j).tabs).map indexOf)[j]!
            ((Array.range 6).map fun j => (sylEnum j).tabs)[j]! c) fun c hcm => ?_
        rw [← hC] at hcm
        unfold centTabs at hcm
        rw [Array.mem_filter, Array.mem_filter, Array.mem_filter] at hcm
        obtain ⟨⟨⟨hm, h1⟩, h2⟩, h3⟩ := hcm
        unfold pts at hm
        rw [Array.mem_ofFn] at hm
        obtain ⟨⟨q, hq⟩, hqe⟩ := hm
        have cq := pinS.canon q hq
        dsimp only at hqe
        subst hqe
        rw [commB cq hx] at h1
        rw [commB cq c1] at h2
        rw [commB cq c2] at h3
        have hs := CFSG.KS.Raw.Orb.allN_iff.1 hJ q hq
        rw [strictB_app, h1, h2, h3] at hs
        simp only [andB_eq, Bool.and_true, notB_eq, Bool.not_true, orB_eq, Bool.false_or] at hs
        rw [foundSY hj cq]
        exact hs
  · simp

theorem tree_facts {j : Nat} (hj : j < 6) : ∀ q < 64,
    (∀ l < 4, inSY j (pcomp 42 6 (mask 6) (syG j l) (syT j q)) = true) ∧
    (q = 0 → syT j q = pidn 42 6) ∧
    (q ≠ 0 → ∃ p < q, ∃ l < 4, syT j q = pcomp 42 6 (mask 6) (syG j l) (syT j p)) ∧
    (∀ r < 64, syT j r = syT j q → r = q) := by
  have F := syl_all j hj
  have hok := F.ok
  unfold enumOK treeOK at hok
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hok
  obtain ⟨⟨-, h0⟩, hall⟩ := hok
  rw [F.size, F.gens.1] at hall
  intro q hq
  have hx := CFSG.KS.BfsReplay.allBelow_iff.1 hall q hq
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at hx
  obtain ⟨⟨hpos, hfd⟩, htr⟩ := hx
  refine ⟨fun l hl => ?_, fun h => ?_, fun h => ?_, fun r hr e => ?_⟩
  · have h1 := CFSG.KS.BfsReplay.allBelow_iff.1 hfd l hl
    unfold leftStep at h1
    rw [(F.gens.2 l hl).1, F.get q hq, comp_unpack' (F.gens.2 l hl).2.1 (F.canon q hq)] at h1
    exact (F.found _ (canonK_pcomp (F.gens.2 l hl).2.1 (F.canon q hq))).1 h1
  · subst h
    rw [F.get 0 hq, idTab_unpack' hsz42] at h0
    exact unpack_inj' (F.canon 0 hq) (canon_pidn hsz42) h0
  · rcases htr with h0' | ⟨⟨hp, hl⟩, he⟩
    · exact absurd h0' h
    · have hp64 : (sylEnum j).par[q]! < 64 := by omega
      rw [F.get q hq, F.get _ hp64] at he
      unfold leftStep at he
      rw [(F.gens.2 _ hl).1, comp_unpack' (F.gens.2 _ hl).2.1 (F.canon _ hp64)] at he
      exact ⟨_, hp, _, hl,
        unpack_inj' (F.canon q hq) (canonK_pcomp (F.gens.2 _ hl).2.1 (F.canon _ hp64)) he⟩
  · have hx' := CFSG.KS.BfsReplay.allBelow_iff.1 hall r hr
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at hx'
    obtain ⟨⟨hposr, -⟩, -⟩ := hx'
    have et : (sylEnum j).tabs[r]! = (sylEnum j).tabs[q]! := by rw [F.get r hr, F.get q hq, e]
    rw [et, hpos] at hposr
    exact hposr.symm

theorem pgc {p q y : Nat} (hy : y < 42) :
    pg 6 (mask 6) (pcomp 42 6 (mask 6) p q) y = pg 6 (mask 6) p (pg 6 (mask 6) q y) :=
  CFSG.KS.PackFld.pg_pcomp (by decide) hy

noncomputable abbrev cjP (x y : Nat) : Nat := pcomp 42 6 (mask 6) (pcomp 42 6 (mask 6) x y) (pinvS 42 6 (mask 6) x)

theorem pinv_l {x y : Nat} (hx : PP 42 6 x) (hy : y < 42) :
    pg 6 (mask 6) (pinvS 42 6 (mask 6) x) (pg 6 (mask 6) x y) = y :=
  CFSG.KS.PinvS.pg_pinvS (by decide) hx.2 hy

theorem pinv_r {x y : Nat} (hx : PP 42 6 x) (hy : y < 42) :
    pg 6 (mask 6) x (pg 6 (mask 6) (pinvS 42 6 (mask 6) x) y) = y := by
  have h : pg 6 (mask 6) (pcomp 42 6 (mask 6) x (pinvS 42 6 (mask 6) x)) y =
      pg 6 (mask 6) (pidn 42 6) y := by
    rw [CFSG.KC.L34Pre.pcomp_pinvS_PP hx]
  rwa [pgc hy, pg_pidn' hsz42 hy] at h

theorem cjP_mul {x a b : Nat} (hx : PP 42 6 x) (ha : Cn a) (hb : Cn b) :
    cjP x (pcomp 42 6 (mask 6) a b) = pcomp 42 6 (mask 6) (cjP x a) (cjP x b) := by
  have hs := hx.inv.1
  refine eq_of_pg (canonK_pcomp (canonK_pcomp hx.1 (canonK_pcomp ha hb)) hs)
    (canonK_pcomp (canonK_pcomp (canonK_pcomp hx.1 ha) hs) (canonK_pcomp (canonK_pcomp hx.1 hb) hs))
    fun y hy => ?_
  have s1 : pg 6 (mask 6) (pinvS 42 6 (mask 6) x) y < 42 := canon_lt hs hy
  have s2 : pg 6 (mask 6) b (pg 6 (mask 6) (pinvS 42 6 (mask 6) x) y) < 42 := canon_lt hb s1
  have s3 := canon_lt hx.1 s2
  unfold cjP
  rw [pgc hy, pgc s1, pgc s1, pgc hy, pgc hy, pgc s1, pgc s3, pgc (canon_lt hs s3), pinv_l hx s2]

theorem cjP_id {x : Nat} (hx : PP 42 6 x) : cjP x (pidn 42 6) = pidn 42 6 := by
  have hs := hx.inv.1
  refine eq_of_pg (canonK_pcomp (canonK_pcomp hx.1 (canon_pidn hsz42)) hs) (canon_pidn hsz42)
    fun y hy => ?_
  unfold cjP
  rw [pgc hy, pgc (canon_lt hs hy), pg_pidn' hsz42 (canon_lt hs hy), pinv_r hx hy,
    pg_pidn' hsz42 hy]

theorem inSY_canon {j y : Nat} (hj : j < 6) (h : inSY j y = true) : Cn y := by
  obtain ⟨q, hq, e⟩ := inSY_iff.1 h
  rw [← e]
  exact (syl_all j hj).canon q hq

theorem prod_closed {j : Nat} (hj : j < 6) : ∀ q < 64, ∀ y, inSY j y = true →
    inSY j (pcomp 42 6 (mask 6) (syT j q) y) = true := by
  intro q
  induction q using Nat.strong_induction_on with
  | _ q ih =>
    intro hq y hy
    have cy := inSY_canon hj hy
    by_cases h0 : q = 0
    · have e : pcomp 42 6 (mask 6) (syT j q) y = y := by
        rw [(tree_facts hj q hq).2.1 h0]
        exact eq_of_pg (canonK_pcomp (canon_pidn hsz42) cy) cy fun i hi => by
          rw [pgc hi, pg_pidn' hsz42 (canon_lt cy hi)]
      rw [e]
      exact hy
    · obtain ⟨p, hp, l, hl, e⟩ := (tree_facts hj q hq).2.2.1 h0
      have F := syl_all j hj
      rw [e, pcomp_assoc' (F.gens.2 l hl).2.1 (F.canon p (by omega)) cy]
      obtain ⟨r, hr, er⟩ := inSY_iff.1 (ih p hp (by omega) y hy)
      rw [← er]
      exact (tree_facts hj r hr).1 l hl

theorem conj_all {j x : Nat} (hj : j < 6) (hx : PP 42 6 x)
    (hg : ∀ i < 4, inSY j (cjP x (syG j i)) = true) : ∀ q < 64, inSY j (cjP x (syT j q)) = true := by
  have F := syl_all j hj
  intro q
  induction q using Nat.strong_induction_on with
  | _ q ih =>
    intro hq
    by_cases h0 : q = 0
    · rw [(tree_facts hj q hq).2.1 h0, cjP_id hx, ← (tree_facts hj q hq).2.1 h0]
      exact inSY_iff.2 ⟨q, hq, rfl⟩
    · obtain ⟨p, hp, l, hl, e⟩ := (tree_facts hj q hq).2.2.1 h0
      rw [e, cjP_mul hx (F.gens.2 l hl).2.1 (F.canon p (by omega))]
      obtain ⟨a, ha, ea⟩ := inSY_iff.1 (hg l hl)
      obtain ⟨b, hb, eb⟩ := inSY_iff.1 (ih p hp (by omega))
      rw [← ea, ← eb]
      exact prod_closed hj a ha _ (inSY_iff.2 ⟨b, hb, rfl⟩)

theorem fab_lt : ∀ j < 6, fa j < 42 ∧ fb j < 42 := by decide

theorem rejB_false {j x : Nat} (hj : j < 6) (hx : PP 42 6 x)
    (hg : ∀ i < 4, inSY j (cjP x (syG j i)) = true) : rejB j x = false := by
  have F := syl_all j hj
  have hc : ∀ i < 64, ∃ q < 64, syT j q = cjP x (syT j i) := fun i hi =>
    inSY_iff.1 (conj_all hj hx hg i hi)
  have hd : ∀ a < 64, ∀ b < 64, syT j a = syT j b → a = b := fun a ha b hb e =>
    (tree_facts hj b hb).2.2.2 a ha e
  have hfix : ∀ q < 64, pg 6 (mask 6) (syT j q) (fa j) = fa j ∧
      pg 6 (mask 6) (syT j q) (fb j) = fb j := fun q hq => by
    obtain ⟨h1, h2⟩ := andT (CFSG.KS.Raw.Orb.allN_iff.1 (CFSG.KS.Raw.Orb.allN_iff.1 k_fix j hj) q hq)
    exact ⟨Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h2⟩
  unfold rejB
  rw [CFSG.KC.L34Pre.mvFix_false (F := syT j) hx F.canon hd (fun q hq => (hfix q hq).1)
      (fab_lt j hj).1 hc,
    CFSG.KC.L34Pre.mvFix_false (F := syT j) hx F.canon hd (fun q hq => (hfix q hq).2)
      (fab_lt j hj).2 hc]
  rfl

theorem nrm_all : ∀ j < 6, ∀ k < 20160,
    orB (rejB j (L34S.T k)) (normK j (pidn 42 6) (L34S.T k)) = true := by
  intro j hj k hk
  have hsl : ∀ s < 18, nrm j s = true := by
    intro s hs
    interval_cases j
    exacts [nrm0All s hs, nrm1All s hs, nrm2All s hs, nrm3All s hs, nrm4All s hs, nrm5All s hs]
  exact scanSl_spec (f := fun x => orB (rejB j x) (normK j (pidn 42 6) x)) (T := L34S.T)
    (L := 1120) (K := 18) (by decide) (by decide) (fun s hs => by
    have h1 := hsl s hs
    unfold nrm at h1
    rwa [strictB_app] at h1) k hk

theorem norm_ok : normScan (pts 42 6 20160 L34S.T) ((Array.range 6).map fun j => (sylEnum j).tabs)
    (((Array.range 6).map fun j => (sylEnum j).tabs).map indexOf) = true := by
  unfold normScan
  rw [CFSG.KS.BfsReplay.allBelow_iff]
  intro j hj
  have F := syl_all j hj
  rw [CFSG.KS.BfsReplay.allBelow_iff, size_pts]
  intro k hk
  have hx := pinS.canon k hk
  have hPP := CFSG.KC.L34Pre.PinE.pp pinS k hk
  have h0 := nrm_all j hj k hk
  have hsi : Cn (pinvS 42 6 (mask 6) (L34S.T k)) := hPP.inv.1
  have hr' := CFSG.KC.L34Pre.pcomp_pinvS_PP hPP
  have hl : Nat.beq (pcomp 42 6 (mask 6) (pinvS 42 6 (mask 6) (L34S.T k)) (L34S.T k))
      (pidn 42 6) = true := by
    rw [eq_of_pg (canonK_pcomp hsi hx) (canon_pidn hsz42) fun y hy => by
      rw [pgc hy, pinv_l hPP hy, pg_pidn' hsz42 hy]]
    exact Nat.beq_refl _
  have hinvT : invTab 42 (unpack 42 6 (L34S.T k)) = unpack 42 6 (pinvS 42 6 (mask 6) (L34S.T k)) :=
    invTab_eq_of_pcomp hx hsi hr'
  rw [pts_get' hk]
  dsimp only
  rw [hinvT, size_unpack, comp_unpack' hsi hx, idTab_unpack' hsz42,
    CFSG.KC.L34KSnd.beq_unpack (canonK_pcomp hsi hx) (canon_pidn hsz42), hl, F.gens.1]
  have hU : u0iT = unpack 42 6 UI := top.1
  rw [hU, comp_unpack' top.2.1 hx, comp_unpack' top.2.1 (canonK_pcomp top.2.1 hx),
    foundSY hj hx, foundSY hj (canonK_pcomp top.2.1 hx),
    foundSY hj (canonK_pcomp top.2.1 (canonK_pcomp top.2.1 hx))]
  have hall : (allBelow 4 fun i => found
      (((Array.range 6).map fun j => (sylEnum j).tabs).map indexOf)[j]!
      ((Array.range 6).map fun j => (sylEnum j).tabs)[j]!
      (conjTab 42 (unpack 42 6 (L34S.T k)) (unpack 42 6 (pinvS 42 6 (mask 6) (L34S.T k)))
        (sylGens[j]!)[i]!)) =
      allN 4 fun i => inSY j (pcomp 42 6 (mask 6) (pcomp 42 6 (mask 6) (L34S.T k) (syG j i))
        (pinvS 42 6 (mask 6) (L34S.T k))) := by
    rw [Bool.eq_iff_iff, CFSG.KS.BfsReplay.allBelow_iff, CFSG.KS.Raw.Orb.allN_iff]
    refine forall_congr' fun i => imp_congr_right fun hi => ?_
    obtain ⟨hg, cg, -⟩ := F.gens.2 i hi
    unfold conjTab
    rw [hg, comp_unpack' hx cg, comp_unpack' (canonK_pcomp hx cg) hsi,
      foundSY hj (canonK_pcomp (canonK_pcomp hx cg) hsi)]
  rw [hall]
  simp only [Bool.true_and, beq_self_eq_true]
  rw [orB_eq, Bool.or_eq_true] at h0
  rcases h0 with hrej | h
  · cases hA : allN 4 (fun i => inSY j (pcomp 42 6 (mask 6) (pcomp 42 6 (mask 6) (L34S.T k)
        (syG j i)) (pinvS 42 6 (mask 6) (L34S.T k))))
    · simp
    · rw [rejB_false hj hPP (fun i hi => CFSG.KS.Raw.Orb.allN_iff.1 hA i hi)] at hrej
      exact absurd hrej (by decide)
  · unfold normK at h
    simp only [inSYf_eq hj] at h
    rw [strictB_app] at h
    obtain ⟨-, h⟩ := andT h
    obtain ⟨-, h⟩ := andT h
    obtain ⟨-, h⟩ := andT h
    simpa only [orB_eq, notB_eq, Bool.or_assoc] using h

theorem borel_true : l34BorelCheck (enumBFS 42 gensS 20160).tabs = true := by
  unfold l34BorelCheck
  rw [hS.1]
  dsimp only
  rw [cover_ok, norm_ok, L34Un.u0_eq.1, top.1, comp_unpack' top.2.1 cU,
    top.2.2.1, idTab_unpack' hsz42, size_unpack, foundS top.2.2.2.2.2.2,
    CFSG.KC.L34KSnd.beq_unpack cU (canon_pidn hsz42), top.2.2.2.2.1,
    comp_unpack' cU cU, comp_unpack' cU (canonK_pcomp cU cU), top.2.2.2.2.2.1,
    CFSG.KS.BfsReplay.allBelow_iff.2 sylOK_all]
  simp
  rfl

end CertificateChecks.KernelLC.L34Bo

end
