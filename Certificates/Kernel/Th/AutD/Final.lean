module

public import Certificates.Kernel.Th.AutD.Chk
public import Certificates.Kernel.Th.AutD.P
public import Certificates.Kernel.Th.AutD.AAll
import CFSG.Certificates.Kernel.L34KSnd.Tab
import CFSG.Certificates.Kernel.Spor.RawOrbEval
import CFSG.Certificates.Kernel.Spor.ChainKProof
public import CFSG.Certificates.Kernel.Th.S.HswTC
import CFSG.Certificates.Kernel.Th.SoundnessGen
import CFSG.Certificates.Kernel.BfsPinSetSound

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelTh.AutD

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.L34K
open CFSG.KS.PEnum CFSG.KC.L34KSnd CertificateChecks.KernelTh.AutDG CFSG.Sporadic.Th.Recog
open CFSG.PSL3Four.Native
open CFSG.KLie.CT (fget andB orB notB)

abbrev Cn (p : Nat) : Prop := canonK 51 6 (mask 6) (51 * 6) p = true

theorem sz : szOK 51 6 = true := by decide

theorem andB_eq (a b : Bool) : andB a b = (a && b) := by cases a <;> rfl
theorem orB_eq (a b : Bool) : orB a b = (a || b) := by cases a <;> rfl
theorem notB_eq (a : Bool) : notB a = !a := by cases a <;> rfl
theorem strictB_app (y : Nat) (k : Nat → Bool) : strictB y k = k y := by cases y <;> rfl

theorem andT {a b : Bool} (h : andB a b = true) : a = true ∧ b = true := by
  cases a <;> cases b <;> simp_all [andB]

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

theorem allL_iff {α : Type} {l : List α} {f : α → Bool} : allL l f = l.all f := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    change andB (f a) (allL l f) = (f a && l.all f)
    rw [ih, andB_eq]

theorem beqU {p q : Nat} (hp : Cn p) (hq : Cn q) : (unpack 51 6 p == unpack 51 6 q) = Nat.beq p q :=
  CFSG.KC.L34KSnd.beq_unpack hp hq

theorem idT : idTab 51 = unpack 51 6 (pidn 51 6) := idTab_unpack' sz

theorem cE : Cn (pidn 51 6) := canon_pidn sz

theorem compU {p q : Nat} (hp : Cn p) (hq : Cn q) :
    comp 51 (unpack 51 6 p) (unpack 51 6 q) = unpack 51 6 (pc p q) := comp_unpack' hp hq

theorem cpc {p q : Nat} (hp : Cn p) (hq : Cn q) : Cn (pc p q) := canonK_pcomp hp hq

theorem wTab_unpack {m : Nat} {Gs GIs : Array Tab} {G GI : Nat → Nat}
    (h : ∀ j < m, Gs[j]! = unpack 51 6 (G j) ∧ Cn (G j) ∧ GIs[j]! = unpack 51 6 (GI j) ∧
      Cn (GI j)) :
    ∀ w : List (Fin m × Bool), wTab Gs GIs w = unpack 51 6 (wK G GI w) ∧ Cn (wK G GI w)
  | [] => ⟨idT, cE⟩
  | l :: w => by
    obtain ⟨ih1, ih2⟩ := wTab_unpack h w
    obtain ⟨a1, a2, a3, a4⟩ := h l.1.val l.1.isLt
    have e1 : wTab Gs GIs (l :: w) =
        comp 51 (if l.2 then Gs[l.1.val]! else GIs[l.1.val]!) (wTab Gs GIs w) := rfl
    have e2 : wK G GI (l :: w) =
        pc (Bool.rec (motive := fun _ => Nat) (GI l.1.val) (G l.1.val) l.2) (wK G GI w) := rfl
    rw [e1, e2, ih1]
    cases l.2
    · simp only [Bool.false_eq_true, if_false]
      rw [a3]
      exact ⟨compU a4 ih2, cpc a4 ih2⟩
    · simp only [if_true]
      rw [a1]
      exact ⟨compU a2 ih2, cpc a2 ih2⟩

theorem enum_parts : GensOK 51 6 ADE.k ADE.G letArr ∧ ADE.cnt = 3456 ∧
    penumHdK (pidn 51 6) ADE.cnt 3456 ADE.T ADE.PL = true ∧ AOA.k = 6 ∧ AOB.k = 6 ∧
    (∀ j < 6, AOA.G j = L j ∧ AOA.GI j = LI j ∧ AOB.G j = L j ∧ AOB.GI j = LI j) ∧
    AOA.cnt = 144 ∧ AOB.cnt = 144 ∧ penumHdK (H 0) AOA.cnt 3456 AOA.T AOA.PL = true ∧
    penumHdK X1 AOB.cnt 3456 AOB.T AOB.PL = true ∧
    penumSlK 51 6 (mask 6) (51 * 6) true AOA.G AOA.GI AOA.k AOA.cnt AOA.T AOA.PL AOA.POS
      AOA.SRT AOA.SRI 0 144 = true ∧
    penumSlK 51 6 (mask 6) (51 * 6) true AOB.G AOB.GI AOB.k AOB.cnt AOB.T AOB.PL AOB.POS
      AOB.SRT AOB.SRI 0 144 = true := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := (by
    simpa only [bAnd_iff] using k_enum :
    gensK letArr 51 6 ADE.k ADE.G = true ∧ Nat.beq ADE.cnt 3456 = true ∧ _ ∧
      Nat.beq AOA.k 6 = true ∧ Nat.beq AOB.k 6 = true ∧ _ ∧ Nat.beq AOA.cnt 144 = true ∧
      Nat.beq AOB.cnt 144 = true ∧ _ ∧ _ ∧ _ ∧ _)
  refine ⟨gensOK_of h1, Nat.eq_of_beq_eq_true h2, h3, Nat.eq_of_beq_eq_true h4,
    Nat.eq_of_beq_eq_true h5, fun j hj => ?_, Nat.eq_of_beq_eq_true h7, Nat.eq_of_beq_eq_true h8,
    h9, h10, h11, h12⟩
  obtain ⟨a, b, c, d⟩ := (by simpa only [bAnd_iff] using CFSG.KS.Raw.Orb.allN_iff.1 h6 j hj :
    Nat.beq (AOA.G j) (L j) = true ∧ Nat.beq (AOA.GI j) (LI j) = true ∧
      Nat.beq (AOB.G j) (L j) = true ∧ Nat.beq (AOB.GI j) (LI j) = true)
  exact ⟨Nat.eq_of_beq_eq_true a, Nat.eq_of_beq_eq_true b, Nat.eq_of_beq_eq_true c,
    Nat.eq_of_beq_eq_true d⟩

theorem let_get {j : Nat} (hj : j < 6) : letArr[j]! = unpack 51 6 (L j) ∧ Cn (L j) ∧
    (letInv ())[j]! = unpack 51 6 (LI j) ∧ Cn (LI j) := by
  have hG := enum_parts.1
  have hk : ADE.k = 6 := by rw [← hG.1]; rfl
  obtain ⟨a, b⟩ := hG.2 j (by rw [hk]; exact hj)
  obtain ⟨c, d, e⟩ := (by simpa only [andB_eq, Bool.and_eq_true] using
    CFSG.KS.Raw.Orb.allN_iff.1 k_let j hj :
    canonK 51 6 (mask 6) (51 * 6) (LI j) = true ∧ Nat.beq (pc (L j) (LI j)) (pidn 51 6) = true ∧
      Nat.beq (pc (LI j) (L j)) (pidn 51 6) = true)
  refine ⟨a, b, ?_, c⟩
  unfold letInv
  rw [map_get _ (by simp [letArr]; omega), a]
  exact invTab_eq_of_pcomp b c (Nat.eq_of_beq_eq_true d)

theorem let_all : ∀ j < 6, letArr[j]! = unpack 51 6 (L j) ∧ Cn (L j) ∧
    (letInv ())[j]! = unpack 51 6 (LI j) ∧ Cn (LI j) := fun _ hj => let_get hj

theorem wL (w : List (Fin 6 × Bool)) :
    wTab letArr (letInv ()) w = unpack 51 6 (wK L LI w) ∧ Cn (wK L LI w) :=
  wTab_unpack let_all w

theorem h0_eq : hTab 0 = unpack 51 6 (H 0) := (wL _).1
theorem h1_eq : hTab 1 = unpack 51 6 (H 1) := (wL _).1
theorem hi0_eq : hInv 0 = unpack 51 6 (HI 0) := (wL _).1
theorem hi1_eq : hInv 1 = unpack 51 6 (HI 1) := (wL _).1
theorem x1_eq : x1Tab () = unpack 51 6 X1 := (wL _).1
theorem x1i_eq : x1Inv () = unpack 51 6 X1I := (wL _).1
theorem cH0 : Cn (H 0) := (wL _).2
theorem cH1 : Cn (H 1) := (wL _).2
theorem cHI0 : Cn (HI 0) := (wL _).2
theorem cHI1 : Cn (HI 1) := (wL _).2
theorem cX1 : Cn X1 := (wL _).2
theorem cX1I : Cn X1I := (wL _).2

theorem ept : ∀ i < ADE.cnt, penumPtK 51 6 (mask 6) (51 * 6) false ADE.G ADE.GI ADE.k ADE.cnt
    ADE.T ADE.PL ADE.POS ADE.SRT ADE.SRI i = true := by
  intro i hi
  have hi' : i < 3456 := enum_parts.2.1 ▸ hi
  have hs : i / 384 < 9 := by omega
  exact penumSl_spec (eAll (i / 384) hs) i (by change i / 384 * 384 ≤ i; omega)
    (by change i < i / 384 * 384 + 384; omega) hi

theorem dEnum_eq : dEnum () = penumRec 51 6 ADE.cnt ADE.T ADE.PL ∧
    enumOK 51 letArr (penumRec 51 6 ADE.cnt ADE.T ADE.PL) = true := by
  unfold dEnum
  exact penumK_left_sound sz enum_parts.1 enum_parts.2.2.1 ept

theorem cT {i : Nat} (hi : i < 3456) : Cn (ADE.T i) :=
  penumPt_canon (ept i (by rw [enum_parts.2.1]; exact hi))

theorem E_size : (dEnum ()).tabs.size = 3456 := by
  rw [dEnum_eq.1, penumRec_eq, Array.size_ofFn, enum_parts.2.1]

theorem E_get {i : Nat} (hi : i < 3456) : (dEnum ()).tabs[i]! = unpack 51 6 (ADE.T i) := by
  rw [dEnum_eq.1, getElem!_pos _ i (by simp [penumRec, enum_parts.2.1, hi])]
  simp [penumRec]

theorem pt_all {i : Nat} (hi : i < 3456) : pt i = true := by
  have hs : i / 384 < 9 := by omega
  have h := CFSG.KS.Raw.Orb.allN_iff.1 (pAll (i / 384) hs) (i % 384) (Nat.mod_lt _ (by decide))
  rw [strictB_app] at h
  have e : Nat.add (Nat.mul 384 (i / 384)) (i % 384) = i := Nat.div_add_mod i 384
  rwa [e] at h

theorem inv_parts {i : Nat} (hi : i < 3456) : Cn (pinv (ADE.T i)) ∧
    pc (ADE.T i) (pinv (ADE.T i)) = pidn 51 6 ∧ pc (pinv (ADE.T i)) (ADE.T i) = pidn 51 6 := by
  have h := (andT (pt_all hi)).1
  unfold invK at h
  rw [strictB_app, strictB_app] at h
  obtain ⟨a, h⟩ := andT h
  obtain ⟨b, c⟩ := andT h
  exact ⟨a, Nat.eq_of_beq_eq_true b, Nat.eq_of_beq_eq_true c⟩

theorem EI_get {i : Nat} (hi : i < 3456) : (dEnumInv ())[i]! = unpack 51 6 (pinv (ADE.T i)) := by
  unfold dEnumInv
  rw [map_get _ (by rw [E_size]; exact hi), E_get hi]
  exact invTab_eq_of_pcomp (cT hi) (inv_parts hi).1 (inv_parts hi).2.1

theorem EI_size : (dEnumInv ()).size = 3456 := by
  unfold dEnumInv
  rw [Array.size_map, E_size]

theorem invs_ok : invsOK 51 (dEnum ()).tabs (dEnumInv ()) = true := by
  unfold invsOK
  rw [EI_size, E_size]
  simp only [beq_self_eq_true, Bool.true_and]
  rw [CFSG.KS.BfsReplay.allBelow_iff]
  intro i hi
  rw [EI_get hi, E_get hi, size_unpack, compU (inv_parts hi).1 (cT hi), idT,
    beqU (cpc (inv_parts hi).1 (cT hi)) cE, (inv_parts hi).2.2]
  simp

theorem pi_parts {k : Nat} (hk : k < 9) : (piArr.push iotaTab)[k]! = unpack 51 6 (PI k) ∧
    Cn (PI k) ∧ Cn (PII k) ∧ pc (PI k) (PII k) = pidn 51 6 ∧ pc (PII k) (PI k) = pidn 51 6 := by
  obtain ⟨a, h⟩ := andT (CFSG.KS.Raw.Orb.allN_iff.1 k_pi k hk)
  obtain ⟨b, h⟩ := andT h
  obtain ⟨c, h⟩ := andT h
  obtain ⟨d, e⟩ := andT h
  exact ⟨unpack_eq_of_bindArrK a, b, c, Nat.eq_of_beq_eq_true d, Nat.eq_of_beq_eq_true e⟩

theorem piTab_eq {k : OutD} (hk : outIdx k < 8) : piTab k = unpack 51 6 (PI (outIdx k)) := by
  unfold piTab
  have e : piArr[outIdx k]! = (piArr.push iotaTab)[outIdx k]! := by
    rw [getElem!_pos _ _ (by simp [piArr]; omega), getElem!_pos _ _ (by simp [piArr]; omega),
      Array.getElem_push_lt]
  rw [e]
  exact (pi_parts (by omega)).1

theorem iota_eq : iotaTab = unpack 51 6 (PI 8) := by
  have e : iotaTab = (piArr.push iotaTab)[8]! := by rfl
  rw [e]
  exact (pi_parts (by decide)).1

theorem invPI {k : Nat} (hk : k < 9) : invTab 51 (unpack 51 6 (PI k)) = unpack 51 6 (PII k) :=
  invTab_eq_of_pcomp (pi_parts hk).2.1 (pi_parts hk).2.2.1 (pi_parts hk).2.2.2.1

theorem pisInv_unpack {p q : Nat} (hp : Cn p) (hq : Cn q) (h : pc q p = pidn 51 6) :
    CFSG.ONSchreier.Native.pisInv 51 (unpack 51 6 p) (unpack 51 6 q) = true := by
  unfold CFSG.ONSchreier.Native.pisInv
  rw [CFSG.KS.CH.allBelowN_iff']
  intro i hi
  rw [CFSG.KC.BfsPin.unpack_get' hi, CFSG.KC.BfsPin.unpack_get' (canon_lt hp hi)]
  have e : pg 6 (mask 6) q (pg 6 (mask 6) p i) = i := by
    rw [← pg_pcomp' hq hi]
    unfold pc at h
    rw [h, pg_pidn' sz hi]
  rw [e]
  simp [canon_lt hp hi]

theorem outIdx_lt {k : OutD} (hk : k ∈ outList) : outIdx k < 8 := by
  simp only [outList, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem conjB {p q x y : Nat} (hp : Cn p) (hq : Cn q) (hx : Cn x) (hy : Cn y) :
    conjOK (unpack 51 6 p) (unpack 51 6 q) (unpack 51 6 x) (unpack 51 6 y) =
      Nat.beq (pc (pc p x) q) y := by
  unfold conjOK
  rw [compU hp hx, compU (cpc hp hx) hq, beqU (cpc (cpc hp hx) hq) hy]

theorem pi_ok : piCheck () = true := by
  unfold piCheck
  rw [List.all_eq_true]
  intro k hk
  have hi := outIdx_lt hk
  obtain ⟨-, c1, c2, e1, -⟩ := pi_parts (k := outIdx k) (by omega)
  have hc := CFSG.KS.Raw.Orb.allN_iff.1 k_pic (outIdx k) hi
  obtain ⟨hw, h0, h5⟩ := (by simpa only [andB_eq, Bool.and_eq_true] using hc :
    allN 6 (fun j => Nat.beq (pc (pc (PII (outIdx k)) (L j)) (PI (outIdx k)))
      (wK L LI ((wYList.getD (outIdx k) []).getD j []))) = true ∧
    Nat.beq (pc (pc (PI (outIdx k)) (L 0)) (PII (outIdx k))) (L 0) = true ∧
    Nat.beq (pc (pc (PI (outIdx k)) (L 5)) (PII (outIdx k))) (L 5) = true)
  dsimp only
  rw [piTab_eq hi, invPI (by omega), pisInv_unpack c1 c2 (by
    have := (pi_parts (k := outIdx k) (by omega)).2.2.2.2; exact this), size_unpack, size_unpack]
  simp only [beq_self_eq_true, Bool.true_and, Bool.and_eq_true]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro j _
    obtain ⟨a, b, c, d⟩ := let_get j.isLt
    rw [(wL _).1, a, conjB c2 c1 b (wL _).2]
    exact CFSG.KS.Raw.Orb.allN_iff.1 hw j.val j.isLt
  · obtain ⟨a, b, -, -⟩ := let_get (j := 0) (by decide)
    rw [a, conjB c1 c2 b b]
    exact h0
  · obtain ⟨a, b, -, -⟩ := let_get (j := 5) (by decide)
    rw [a, conjB c1 c2 b b]
    exact h5

theorem iota_ok : iotaCheck () = true := by
  unfold iotaCheck
  obtain ⟨-, c1, c2, -, e2⟩ := pi_parts (k := 8) (by decide)
  dsimp only
  rw [iota_eq, invPI (by decide), pisInv_unpack c1 c2 e2, size_unpack, size_unpack]
  simp only [beq_self_eq_true, Bool.true_and]
  rw [List.all_eq_true]
  intro j _
  have h := CFSG.KS.Raw.Orb.allN_iff.1 k_iota j.val j.isLt
  by_cases h5 : j.val = 5
  · have hj : j = ⟨5, by decide⟩ := Fin.ext h5
    subst hj
    obtain ⟨a5, b5, c5, d5⟩ := let_get (j := 5) (by decide)
    have e5 : (((⟨5, by decide⟩ : Fin 6) : Nat) == 5) = true := rfl
    rw [if_pos e5, a5, c5, conjB c1 c2 b5 d5]
    exact h
  · obtain ⟨a, b, c, d⟩ := let_get j.isLt
    have e5 : ¬ (j.val == 5) = true := by simpa using h5
    rw [if_neg e5, a, conjB c1 c2 b b]
    have e : Nat.beq j.val 5 = false := by
      cases hb : Nat.beq j.val 5
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true hb) h5
    rw [e] at h
    exact h

theorem part_ok : partnerCheck () = true := by
  unfold partnerCheck
  obtain ⟨-, ci1, ci2, -, ei2⟩ := pi_parts (k := 8) (by decide)
  rw [List.all_eq_true]
  intro k hk
  have ht : ∃ t < 4, [Twist.id, .f1, .f3, .f13].getD t .id = k ∧ outIdx (k, false) = t ∧
      outIdx (k, true) = 4 + t := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl
    exacts [⟨0, by decide, rfl, rfl, rfl⟩, ⟨1, by decide, rfl, rfl, rfl⟩,
      ⟨2, by decide, rfl, rfl, rfl⟩, ⟨3, by decide, rfl, rfl, rfl⟩]
  obtain ⟨t, htl, hkt, h0, h1⟩ := ht
  have h := CFSG.KS.Raw.Orb.allN_iff.1 k_part t htl
  rw [strictB_app, strictB_app, hkt] at h
  obtain ⟨-, c0, c0i, -, -⟩ := pi_parts (k := t) (by omega)
  obtain ⟨-, c1, c1i, -, -⟩ := pi_parts (k := 4 + t) (by omega)
  dsimp only
  rw [piTab_eq (by rw [h0]; omega), piTab_eq (by rw [h1]; omega), h0, h1, invPI (by omega),
    invPI (by omega), iota_eq, invPI (by decide), (wL _).1, (wL _).1, List.all_eq_true]
  intro j _
  obtain ⟨a, b, -, -⟩ := let_get j.isLt
  have cm := (wL (mWord k)).2
  have cmi := (wL (FreeGroup.invRev (mWord k))).2
  rw [a, compU c0 b, compU (cpc c0 b) c0i, compU cmi b, compU (cpc cmi b) cm,
    compU c1 (cpc (cpc cmi b) cm), compU (cpc c1 (cpc (cpc cmi b) cm)) c1i,
    compU ci1 (cpc (cpc c1 (cpc (cpc cmi b) cm)) c1i),
    compU (cpc ci1 (cpc (cpc c1 (cpc (cpc cmi b) cm)) c1i)) ci2,
    beqU (cpc (cpc c0 b) c0i) (cpc (cpc ci1 (cpc (cpc c1 (cpc (cpc cmi b) cm)) c1i)) ci2)]
  exact CFSG.KS.Raw.Orb.allN_iff.1 h j.val j.isLt

theorem tpow_unpack {x : Nat} (hx : Cn x) :
    ∀ n, tpow (unpack 51 6 x) n = unpack 51 6 (pw x n) ∧ Cn (pw x n)
  | 0 => ⟨idT, cE⟩
  | n + 1 => by
    obtain ⟨a, b⟩ := tpow_unpack hx n
    have e1 : tpow (unpack 51 6 x) (n + 1) = comp 51 (unpack 51 6 x) (tpow (unpack 51 6 x) n) :=
      rfl
    have e2 : pw x (n + 1) = pc x (pw x n) := rfl
    rw [e1, e2, a]
    exact ⟨compU hx b, cpc hx b⟩

theorem ord24_eq {x : Nat} (hx : Cn x) : ord24 (unpack 51 6 x) = ord24K x := by
  unfold ord24 ord24K
  rw [(tpow_unpack hx 24).1, (tpow_unpack hx 12).1, (tpow_unpack hx 8).1, idT,
    beqU (tpow_unpack hx 24).2 cE, beqU (tpow_unpack hx 12).2 cE, beqU (tpow_unpack hx 8).2 cE,
    andB_eq, andB_eq, notB_eq, notB_eq, Bool.and_assoc]

theorem decW_eq : ∀ w : List (Fin 8 × Bool),
    decW w.length (CFSG.KC.Th.Hsw.wordNat w) = w
  | [] => rfl
  | l :: w => by
    have hc : CFSG.KC.Th.Hsw.code l < 16 := by
      unfold CFSG.KC.Th.Hsw.code
      have := l.1.isLt
      split <;> omega
    have e1 : CFSG.KC.Th.Hsw.wordNat (l :: w) =
        CFSG.KC.Th.Hsw.code l + 256 * CFSG.KC.Th.Hsw.wordNat w := rfl
    have e2 : (CFSG.KC.Th.Hsw.code l + 256 * CFSG.KC.Th.Hsw.wordNat w) % 256 =
        CFSG.KC.Th.Hsw.code l := by omega
    have e3 : (CFSG.KC.Th.Hsw.code l + 256 * CFSG.KC.Th.Hsw.wordNat w) / 256 =
        CFSG.KC.Th.Hsw.wordNat w := by omega
    have e4 : (CFSG.KC.Th.Hsw.code l + 256 * CFSG.KC.Th.Hsw.wordNat w) % 2 =
        CFSG.KC.Th.Hsw.code l % 2 := by omega
    rw [List.length_cons, e1]
    unfold decW
    rw [e2, e3, e4, decW_eq w]
    congr 1
    obtain ⟨g, b⟩ := l
    have hg := g.isLt
    unfold CFSG.KC.Th.Hsw.code
    cases b
    · simp only [Bool.false_eq_true, if_false, Prod.mk.injEq]
      refine ⟨Fin.ext ?_, ?_⟩
      · simp only [Fin.val_ofNat]
        omega
      · simp only [beq_eq_false_iff_ne, ne_eq]
        omega
    · simp only [if_true, Prod.mk.injEq]
      refine ⟨Fin.ext ?_, ?_⟩
      · simp only [Fin.val_ofNat]
        omega
      · simp only [beq_iff_eq]
        omega

theorem decE_ent (w : List (Fin 8 × Bool)) (h : w.length < 1024) :
    decE (CFSG.KC.Th.Hsw.ent w) = w := by
  unfold decE CFSG.KC.Th.Hsw.ent
  have e1 : (4 * w.length + 4096 * CFSG.KC.Th.Hsw.wordNat w) % 4096 / 4 = w.length := by omega
  have e2 : (4 * w.length + 4096 * CFSG.KC.Th.Hsw.wordNat w) / 4096 =
      CFSG.KC.Th.Hsw.wordNat w := by omega
  rw [e1, e2]
  exact decW_eq w

theorem map_dec (Ls : List (List (Fin 8 × Bool))) (h : ∀ w ∈ Ls, w.length < 1024) :
    (Ls.map CFSG.KC.Th.Hsw.ent).map decE = Ls := by
  rw [List.map_map]
  conv_rhs => rw [← List.map_id Ls]
  exact List.map_congr_left fun w hw => decE_ent w (h w hw)

theorem rel_len : ∀ w ∈ (TauCeti.Sporadic.Thompson.presentation.relators :
    List (List (Fin 8 × Bool))), w.length < 1024 := by
  intro w hw
  rw [TauCeti.GroupPresentation.relators_def, List.mem_map] at hw
  obtain ⟨r, hr, rfl⟩ := hw
  have h := List.all_eq_true.mp CFSG.KC.Th.Soundness.th_relator_lengths _
    (List.mem_map_of_mem (f := fun r => r.toWord.length) hr)
  simpa using h

theorem R0'_eq : R0' = CFSG.KC.Th.Hsw.list.map decE := by
  unfold R0'
  rw [← CFSG.KC.Th.Hsw.relators_eq]
  exact (map_dec _ rel_len).symm

theorem autTests_eq : autTests = autTestsC := by
  unfold autTests RD rdHSW autTestsC rdC
  rw [R0'_eq]

theorem pair_get {X Y XI YI : Nat} (cX : Cn X) (cY : Cn Y) (cXI : Cn XI) (cYI : Cn YI) :
    ∀ j < 2, (#[unpack 51 6 X, unpack 51 6 Y] : Array Tab)[j]! = unpack 51 6 (g2 X Y j) ∧
      Cn (g2 X Y j) ∧
      (#[unpack 51 6 XI, unpack 51 6 YI] : Array Tab)[j]! = unpack 51 6 (g2 XI YI j) ∧
      Cn (g2 XI YI j) := by
  intro j hj
  match j, hj with
  | 0, _ => exact ⟨rfl, cX, rfl, cXI⟩
  | 1, _ => exact ⟨rfl, cY, rfl, cYI⟩

theorem tests_eq {X Y XI YI : Nat} (cX : Cn X) (cY : Cn Y) (cXI : Cn XI) (cYI : Cn YI) :
    (autTests.all fun S => wTab #[unpack 51 6 X, unpack 51 6 Y]
      #[unpack 51 6 XI, unpack 51 6 YI] S == idTab 51) = testK X XI Y YI := by
  unfold testK
  rw [autTests_eq, allL_iff, Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
  refine forall_congr' fun S => imp_congr_right fun _ => ?_
  obtain ⟨a, b⟩ := wTab_unpack (pair_get cX cY cXI cYI) S
  rw [a, idT, beqU b cE]

theorem hgen_ok : hGenCheck () = true := by
  unfold hGenCheck
  obtain ⟨hw, ho, ht, -⟩ := (by simpa only [andB_eq, Bool.and_eq_true] using k_hgen :
    allN 6 (fun j => Nat.beq (wK (g2 (H 0) (H 1)) (g2 (HI 0) (HI 1)) (lW (Fin.ofNat 6 j))) (L j))
      = true ∧ ord24K (H 0) = true ∧ testK (H 0) (HI 0) (H 1) (HI 1) = true ∧ _)
  dsimp only
  rw [h0_eq, h1_eq, hi0_eq, hi1_eq, ord24_eq cH0, ho, tests_eq cH0 cH1 cHI0 cHI1, ht]
  simp only [Bool.and_true, List.all_eq_true]
  intro j _
  obtain ⟨a, b, -, -⟩ := let_get j.isLt
  obtain ⟨w1, w2⟩ := wTab_unpack (pair_get cH0 cH1 cHI0 cHI1) (lW j)
  rw [w1, a, beqU w2 b]
  have := CFSG.KS.Raw.Orb.allN_iff.1 hw j.val j.isLt
  have e : Fin.ofNat 6 j.val = j := by ext; simp [Nat.mod_eq_of_lt j.isLt]
  rwa [e] at this

theorem gensL : GensOK 51 6 6 L letArr :=
  ⟨rfl, fun j hj => ⟨(let_get hj).1, (let_get hj).2.1⟩⟩

theorem gensLI : GensOK 51 6 6 LI (letInv ()) :=
  ⟨by simp [letInv, letArr], fun j hj => ⟨(let_get hj).2.2.1, (let_get hj).2.2.2⟩⟩

theorem gensO {G : Nat → Nat} (h : ∀ j < 6, G j = L j) : GensOK 51 6 6 G letArr :=
  ⟨rfl, fun j hj => by rw [h j hj]; exact gensL.2 j hj⟩

theorem gensOI {G : Nat → Nat} (h : ∀ j < 6, G j = LI j) : GensOK 51 6 6 G (letInv ()) :=
  ⟨gensLI.1, fun j hj => by rw [h j hj]; exact gensLI.2 j hj⟩

theorem invs_let : invsOK 51 letArr (letInv ()) = true := by
  unfold invsOK
  have hs : (letInv ()).size = 6 := gensLI.1
  rw [hs]
  simp only [show letArr.size = 6 from rfl, beq_self_eq_true, Bool.true_and]
  rw [CFSG.KS.BfsReplay.allBelow_iff]
  intro j hj
  obtain ⟨a, b, c, d⟩ := let_get hj
  obtain ⟨-, -, e⟩ := (by simpa only [andB_eq, Bool.and_eq_true] using
    CFSG.KS.Raw.Orb.allN_iff.1 k_let j hj :
    canonK 51 6 (mask 6) (51 * 6) (LI j) = true ∧ Nat.beq (pc (L j) (LI j)) (pidn 51 6) = true ∧
      Nat.beq (pc (LI j) (L j)) (pidn 51 6) = true)
  rw [a, c, size_unpack, compU d b, idT, beqU (cpc d b) cE, e]
  rfl

theorem oA_pt : ∀ i < AOA.cnt, penumPtK 51 6 (mask 6) (51 * 6) true AOA.G AOA.GI AOA.k AOA.cnt
    AOA.T AOA.PL AOA.POS AOA.SRT AOA.SRI i = true := fun i hi =>
  penumSl_spec enum_parts.2.2.2.2.2.2.2.2.2.2.1 i (Nat.zero_le _)
    (by have := enum_parts.2.2.2.2.2.2.1; omega) hi

theorem oB_pt : ∀ i < AOB.cnt, penumPtK 51 6 (mask 6) (51 * 6) true AOB.G AOB.GI AOB.k AOB.cnt
    AOB.T AOB.PL AOB.POS AOB.SRT AOB.SRI i = true := fun i hi =>
  penumSl_spec enum_parts.2.2.2.2.2.2.2.2.2.2.2 i (Nat.zero_le _)
    (by have := enum_parts.2.2.2.2.2.2.2.1; omega) hi

theorem oA_enc : xOrb (hTab 0) = penumRec 51 6 AOA.cnt AOA.T AOA.PL ∧
    treeOK (conjStep 51 letArr (letInv ())) letArr.size (hTab 0)
      (penumRec 51 6 AOA.cnt AOA.T AOA.PL) = true := by
  have hk := enum_parts.2.2.2.1
  have hg : GensOK 51 6 AOA.k AOA.G letArr := by
    rw [hk]; exact gensO fun j hj => (enum_parts.2.2.2.2.2.1 j hj).1
  have hgi : GensOK 51 6 AOA.k AOA.GI (letInv ()) := by
    rw [hk]; exact gensOI fun j hj => (enum_parts.2.2.2.2.2.1 j hj).2.1
  unfold xOrb
  exact penumK_conj_sound sz hg hgi h0_eq enum_parts.2.2.2.2.2.2.2.2.1 oA_pt

theorem oB_enc : xOrb (x1Tab ()) = penumRec 51 6 AOB.cnt AOB.T AOB.PL ∧
    treeOK (conjStep 51 letArr (letInv ())) letArr.size (x1Tab ())
      (penumRec 51 6 AOB.cnt AOB.T AOB.PL) = true := by
  have hk := enum_parts.2.2.2.2.1
  have hg : GensOK 51 6 AOB.k AOB.G letArr := by
    rw [hk]; exact gensO fun j hj => (enum_parts.2.2.2.2.2.1 j hj).2.2.1
  have hgi : GensOK 51 6 AOB.k AOB.GI (letInv ()) := by
    rw [hk]; exact gensOI fun j hj => (enum_parts.2.2.2.2.2.1 j hj).2.2.2
  unfold xOrb
  exact penumK_conj_sound sz hg hgi x1_eq enum_parts.2.2.2.2.2.2.2.2.2.1 oB_pt

theorem foundA {x : Nat} (hx : Cn x) :
    found (indexOf (penumRec 51 6 AOA.cnt AOA.T AOA.PL).tabs)
      (penumRec 51 6 AOA.cnt AOA.T AOA.PL).tabs (unpack 51 6 x) = inOA x := by
  rw [Bool.eq_iff_iff, found_penumRec_iff oA_pt hx]
  unfold inOA
  rw [notAllNotB, enum_parts.2.2.2.2.2.2.1]
  exact ⟨fun ⟨q, hq, e⟩ => ⟨q, hq, by rw [e]; exact Nat.beq_refl x⟩,
    fun ⟨q, hq, e⟩ => ⟨q, hq, Nat.eq_of_beq_eq_true e⟩⟩

theorem foundB {x : Nat} (hx : Cn x) :
    found (indexOf (penumRec 51 6 AOB.cnt AOB.T AOB.PL).tabs)
      (penumRec 51 6 AOB.cnt AOB.T AOB.PL).tabs (unpack 51 6 x) = inOB x := by
  rw [Bool.eq_iff_iff, found_penumRec_iff oB_pt hx]
  unfold inOB
  rw [notAllNotB, enum_parts.2.2.2.2.2.2.2.1]
  exact ⟨fun ⟨q, hq, e⟩ => ⟨q, hq, by rw [e]; exact Nat.beq_refl x⟩,
    fun ⟨q, hq, e⟩ => ⟨q, hq, Nat.eq_of_beq_eq_true e⟩⟩

theorem cover_ok : cover24Check () = true := by
  unfold cover24Check orbitOK
  dsimp only
  rw [oA_enc.1, oB_enc.1, oA_enc.2, oB_enc.2, invs_let]
  simp only [Bool.true_and]
  rw [CFSG.KS.BfsReplay.allBelow_iff, E_size]
  intro i hi
  have h := (andT (pt_all hi)).2
  rw [strictB_app] at h
  rw [E_get hi, ord24_eq (cT hi), foundA (cT hi), foundB (cT hi)]
  simpa only [orB_eq, notB_eq, Bool.or_assoc] using h

theorem outList_get {f : Nat} (hf : f < 8) :
    ∃ k ∈ outList, outIdx k = f := by
  interval_cases f
  exacts [⟨(.id, false), by simp [outList], rfl⟩, ⟨(.f1, false), by simp [outList], rfl⟩,
    ⟨(.f3, false), by simp [outList], rfl⟩, ⟨(.f13, false), by simp [outList], rfl⟩,
    ⟨(.id, true), by simp [outList], rfl⟩, ⟨(.f1, true), by simp [outList], rfl⟩,
    ⟨(.f3, true), by simp [outList], rfl⟩, ⟨(.f13, true), by simp [outList], rfl⟩]

theorem twTab_eq {k : OutD} (hk : outIdx k < 8) (i : Fin 2) :
    twTab k i = unpack 51 6 (tw (outIdx k) i.val) ∧ Cn (tw (outIdx k) i.val) := by
  obtain ⟨-, c1, c2, -, -⟩ := pi_parts (k := outIdx k) (by omega)
  have hH : hTab i = unpack 51 6 (H i.val) ∧ Cn (H i.val) := by
    match i with
    | 0 => exact ⟨h0_eq, cH0⟩
    | 1 => exact ⟨h1_eq, cH1⟩
  unfold twTab tw
  rw [piTab_eq hk, invPI (by omega), hH.1, compU c1 hH.2, compU (cpc c1 hH.2) c2]
  exact ⟨rfl, cpc (cpc c1 hH.2) c2⟩

theorem pair_ok {i : Nat} (hi : i < 3456) {X XI : Nat} (cX : Cn X) (cXI : Cn XI)
    (h : orB (notB (testK X XI (ADE.T i) (pinv (ADE.T i))))
      (witK (AW (Nat.add (Nat.mul 2 i) 0)) X (ADE.T i)) = true ∨
      orB (notB (testK X XI (ADE.T i) (pinv (ADE.T i))))
      (witK (AW (Nat.add (Nat.mul 2 i) 1)) X (ADE.T i)) = true) :
    autPairOK (twList ()) (dEnum ()) (dEnumInv ()) (unpack 51 6 X) (unpack 51 6 XI)
      (dEnum ()).tabs[i]! (dEnumInv ())[i]! = true := by
  have cY := cT hi
  have cYI := (inv_parts hi).1
  unfold autPairOK
  rw [E_get hi, EI_get hi, tests_eq cX cY cXI cYI]
  have key : ∀ w, witK w X (ADE.T i) = true →
      ((twList ()).any fun f => anyBelow (dEnum ()).tabs.size fun mi =>
        conjOK (dEnum ()).tabs[mi]! (dEnumInv ())[mi]! f.2.1 (unpack 51 6 X) &&
          conjOK (dEnum ()).tabs[mi]! (dEnumInv ())[mi]! f.2.2 (unpack 51 6 (ADE.T i))) = true := by
    intro w hw
    unfold witK at hw
    obtain ⟨-, hw⟩ := andT hw
    rw [strictB_app, strictB_app] at hw
    obtain ⟨hf, hw⟩ := andT hw
    obtain ⟨hm, hw⟩ := andT hw
    rw [strictB_app, strictB_app] at hw
    obtain ⟨e1, e2⟩ := andT hw
    have hf' := Nat.blt_eq.mp hf
    have hm' := Nat.blt_eq.mp hm
    obtain ⟨k, hk, hkf⟩ := outList_get hf'
    rw [List.any_eq_true]
    refine ⟨(k, twTab k 0, twTab k 1), by unfold twList; exact List.mem_map_of_mem hk, ?_⟩
    rw [CFSG.KC.L34KSnd.anyBelow_iff]
    refine ⟨_, by rw [E_size]; exact hm', ?_⟩
    have cm := cT hm'
    have cmi := (inv_parts hm').1
    obtain ⟨t0, ct0⟩ := twTab_eq (k := k) (by omega) 0
    obtain ⟨t1, ct1⟩ := twTab_eq (k := k) (by omega) 1
    dsimp only
    rw [E_get hm', EI_get hm', t0, t1, conjB cm cmi ct0 cX, conjB cm cmi ct1 cY, Bool.and_eq_true]
    simp only [Fin.val_zero, Fin.val_one, hkf] at e1 e2 ⊢
    exact ⟨e1, e2⟩
  rcases h with h | h <;>
  · cases ht : testK X XI (ADE.T i) (pinv (ADE.T i))
    · rfl
    · rw [ht, orB_eq, notB_eq] at h
      simp only [Bool.not_true, Bool.false_or] at h
      simp only [Bool.not_true, Bool.false_or]
      exact key _ h

theorem aut_pt {i : Nat} (hi : i < 3456) : autK i 0 = true ∧ autK i 1 = true := by
  have hs : i / 128 < 27 := by omega
  have h := CFSG.KS.Raw.Orb.allN_iff.1 (by
    have h1 := aAll (i / 128) hs
    unfold aSl at h1
    exact h1) (i % 128) (Nat.mod_lt _ (by decide))
  rw [strictB_app] at h
  have e : Nat.add (Nat.mul 128 (i / 128)) (i % 128) = i := Nat.div_add_mod i 128
  rw [e] at h
  exact andT h

theorem aut_ok : autCheck () = true := by
  unfold autCheck
  dsimp only
  rw [CFSG.KS.BfsReplay.allBelow_iff, E_size]
  intro i hi
  obtain ⟨h0, h1⟩ := aut_pt hi
  unfold autK at h0 h1
  simp only [strictB_app] at h0 h1
  rw [Bool.and_eq_true, h0_eq, hi0_eq, x1_eq, x1i_eq]
  exact ⟨pair_ok hi cH0 cHI0 (Or.inl h0), pair_ok hi cX1 cX1I (Or.inr h1)⟩

theorem autD_true : piCheck () = true ∧ iotaCheck () = true ∧ partnerCheck () = true ∧
    hGenCheck () = true ∧ invsOK 51 (dEnum ()).tabs (dEnumInv ()) = true ∧
    cover24Check () = true ∧ autCheck () = true :=
  ⟨pi_ok, iota_ok, part_ok, hgen_ok, invs_ok, cover_ok, aut_ok⟩

end CertificateChecks.KernelTh.AutD

end
