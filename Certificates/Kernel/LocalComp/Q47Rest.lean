module

public import Certificates.Kernel.LocalComp.Q47Pack
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.BfsPinAlg
import CFSG.Certificates.Kernel.Spor.PcompFacts
import CFSG.Certificates.Kernel.Q47KRunSound

public section

set_option maxRecDepth 400000
set_option Elab.async false

namespace CertificateChecks.KernelLC.Q47

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.HexaK CFSG.KC.HeAutK CFSG.KC.Q47K
open CFSG.ComponentClassification.AS81.Q47 CFSG.ComponentClassification.AS81.HeSylow
open CertificateChecks.KernelLC CertificateChecks.KernelLC.Step44Check

@[expose] noncomputable def q47FormP : Nat := packA 1 q47Form.toList

@[expose] noncomputable def formPK (F T : Nat) : Bool :=
  allN 64 fun v => Nat.beq (pg 1 (mask 1) F (pg 7 (mask 7) T v)) (pg 1 (mask 1) F v)

@[expose] noncomputable def transPK (F k T : Nat) : Bool :=
  formPK F T && allN k fun i => Nat.beq (pg 7 (mask 7) T (2 ^ i)) (2 ^ i)

theorem unpack_get47 {P p : Nat} (hp : p < 64) : (unpack 64 7 P)[p]! = pg 7 (mask 7) P p := by
  unfold unpack
  rw [getElem!_pos _ p (by rw [Array.size_ofFn]; exact hp), Array.getElem_ofFn]

theorem transEl_of_pk {form : Array Nat} {F T k : Nat} (hk : k ≤ 6)
    (hF : ∀ x < 128, form[x]! = pg 1 (mask 1) F x) (h : transPK F k T = true) :
    transElG form k (unpack 64 7 T) = true := by
  unfold transPK formPK at h
  rw [Bool.and_eq_true] at h
  unfold transElG formCheckG
  rw [Bool.and_eq_true, List.all_eq_true, List.all_eq_true]
  refine ⟨fun v hv => ?_, fun i hi => ?_⟩
  · have hv' := List.mem_range.1 hv
    have hl : pg 7 (mask 7) T v < 2 ^ 7 := Nat.and_lt_two_pow _ (by decide : mask 7 < 2 ^ 7)
    rw [unpack_get47 hv', hF _ hl, hF v (by omega)]
    exact beq_iff_eq.2 (Nat.eq_of_beq_eq_true (allN_spec h.1 v hv'))
  · have hi' := List.mem_range.1 hi
    have h64 : 2 ^ i < 64 := lt_of_lt_of_le (Nat.pow_lt_pow_right (by decide) (by omega : i < 6))
      (by decide)
    rw [unpack_get47 h64]
    exact beq_iff_eq.2 (Nat.eq_of_beq_eq_true (allN_spec h.2 i hi'))

theorem directTrans_of_pk {d : QD} {SZ : Nat → Nat} {TR : Nat → Nat → Nat} {F : Nat}
    (hl : d.trans.length = 6)
    (bT : ∀ k < 6, (d.trans[k]!).length = SZ k ∧ Bound 64 7 d.trans[k]! (TR k))
    (hF : ∀ x < 128, d.form[x]! = pg 1 (mask 1) F x)
    (hP : ∀ k < 6, ∀ j < SZ k, transPK F k (TR k j) = true)
    (hR : ((List.range 6).all (fun k => (List.range 64).all fun x =>
      !(admKG d.form k x) || d.trans[k]!.any fun t => t[2 ^ k]! == x) && nondegCheckG d.form) =
      true) :
    directTransG d = true := by
  unfold directTransG
  rw [Bool.and_eq_true] at hR
  rw [Bool.and_eq_true, Bool.and_eq_true, hl]
  refine ⟨⟨rfl, List.all_eq_true.2 fun k hk => ?_⟩, hR.2⟩
  have hk' := List.mem_range.1 hk
  refine Bool.and_eq_true_iff.2 ⟨List.all_eq_true.2 fun t ht => ?_, List.all_eq_true.1 hR.1 k hk⟩
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem ht
  rw [← getElem!_pos _ j hj, ((bT k hk').2 j hj).1]
  exact transEl_of_pk (by omega) hF (hP k hk' j (by rw [← (bT k hk').1]; exact hj))

theorem kDTP : ((allN 128 fun x => Nat.beq q47Form[x]! (pg 1 (mask 1) q47FormP x)) &&
    (List.range 6).all fun k => allN (SZ k) fun j => transPK q47FormP k (TR k j)) = true := by
  quickRfl

@[expose] noncomputable def q47NDW : Nat :=
  packA 6 [0, 2, 1, 3, 8, 10, 9, 11, 4, 6, 5, 7, 12, 14, 13, 15, 32, 34, 33, 35, 40, 42, 41, 43, 36,
    38, 37, 39, 44, 46, 45, 47, 16, 18, 17, 19, 24, 26, 25, 27, 20, 22, 21, 23, 28, 30, 29, 31, 48,
    50, 49, 51, 56, 58, 57, 59, 52, 54, 53, 55, 60, 62, 61, 63]

@[expose] noncomputable def bilinP (F u v : Nat) : Nat :=
  Nat.mod (Nat.add (Nat.add (pg 1 (mask 1) F (Nat.xor u v)) (pg 1 (mask 1) F u))
    (pg 1 (mask 1) F v)) 2

theorem nondeg_of_pk {form : Array Nat} {F W : Nat} (hF : ∀ x < 128, form[x]! = pg 1 (mask 1) F x)
    (h : (allN 64 fun c => allN 6 fun i =>
      Nat.beq (bilinP F (2 ^ i) (pg 6 (mask 6) W c)) (Nat.mod (Nat.shiftRight c i) 2)) = true) :
    nondegCheckG form = true := by
  unfold nondegCheckG
  refine List.all_eq_true.2 fun c hc => List.any_eq_true.2 ⟨pg 6 (mask 6) W c,
    List.mem_range.2 (Nat.and_lt_two_pow _ (by decide : mask 6 < 2 ^ 6)), ?_⟩
  refine List.all_eq_true.2 fun i hi => ?_
  have hi' := List.mem_range.1 hi
  have hw : pg 6 (mask 6) W c < 2 ^ 6 := Nat.and_lt_two_pow _ (by decide : mask 6 < 2 ^ 6)
  have h2 : 2 ^ i < 2 ^ 6 := Nat.pow_lt_pow_right (by decide) hi'
  have hx : 2 ^ i ^^^ pg 6 (mask 6) W c < 2 ^ 6 := Nat.xor_lt_two_pow h2 hw
  have hw' : pg 6 (mask 6) W c < 128 := lt_trans hw (by decide)
  have h2' : 2 ^ i < 128 := lt_trans h2 (by decide)
  have hx' : 2 ^ i ^^^ pg 6 (mask 6) W c < 128 := lt_trans hx (by decide)
  have e := Nat.eq_of_beq_eq_true (allN_spec (allN_spec h c (List.mem_range.1 hc)) i hi')
  unfold bilinG
  rw [hF _ hx', hF _ h2', hF _ hw']
  exact beq_iff_eq.2 e

theorem kQ47ND : (allN 64 fun c => allN 6 fun i => Nat.beq (bilinP q47FormP (2 ^ i)
    (pg 6 (mask 6) q47NDW c)) (Nat.mod (Nat.shiftRight c i) 2)) = true := by quickRfl

theorem kDTA : ((List.range 6).all fun k => (List.range 64).all fun x =>
    !(admKG q47Form k x) || q47Trans[k]!.any fun t => t[2 ^ k]! == x) = true := by quickRfl

theorem kDTR : ((List.range 6).all (fun k => (List.range 64).all fun x =>
    !(admKG q47Form k x) || q47Trans[k]!.any fun t => t[2 ^ k]! == x) && nondegCheckG q47Form) =
    true := Bool.and_eq_true_iff.2 ⟨kDTA, nondeg_of_pk (fun x hx =>
      Nat.eq_of_beq_eq_true (allN_spec (Bool.and_eq_true_iff.1 kDTP).1 x hx)) kQ47ND⟩

theorem kQ47FormP : ∀ x < 128, q47Form[x]! = pg 1 (mask 1) q47FormP x := fun x hx =>
  Nat.eq_of_beq_eq_true (allN_spec (Bool.and_eq_true_iff.1 kDTP).1 x hx)

theorem allTrans_of_pk {form : Array Nat} {gs : List (Array Nat)} {G : Nat → Nat} {F k : Nat}
    (hk : k ≤ 6) (b : Bound 64 7 gs G) (hF : ∀ x < 128, form[x]! = pg 1 (mask 1) F x)
    (h : allN gs.length (fun j => transPK F k (G j)) = true) : gs.all (transElG form k) = true := by
  refine List.all_eq_true.2 fun t ht => ?_
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem ht
  rw [← getElem!_pos _ j hj, (b j hj).1]
  exact transEl_of_pk hk hF (allN_spec h j hj)

@[expose] def refRestG (d : QD) : Bool :=
  d.yg.length == 2 && d.ng.length == 2 && d.u1.length == 3 && d.u2.length == 3 &&
    tsCheckG d.form d.w1 && tsCheckG d.form d.w2 &&
    d.w1.toList.all (fun a => a == 0 || !(d.w2.contains a)) &&
    d.yg.all (fun y => mapsInto y d.w1 d.w1 && mapsInto y d.w2 d.w2) &&
    d.l30.length == 30 && d.l30.all eightCheck &&
    d.orbRep.length == 4 && d.orbRep.all eightCheck && d.orb.length == 30 &&
    (List.range 30).all (fun j => decide (d.orb[j]!.1 < 4) ||
      (d.orb[j]!.1 == 4 && sameSet d.l30[j]! d.w1) || (d.orb[j]!.1 == 5 && sameSet d.l30[j]! d.w2)) &&
    d.g1.length == 4 && d.g2.length == 4 &&
    (List.range 4).all (fun k =>
      mapsInto d.g1[k]! d.w1 d.orbRep[k]! && mapsInto d.g2[k]! d.w2 d.orbRep[k]!) &&
    (d.u1 ++ d.yg).all (fun t => mapsInto t d.w1 d.w1) &&
    (d.u2 ++ d.yg).all (fun t => mapsInto t d.w2 d.w2) &&
    d.wit.length == 64 && d.wit.all (·.all (·.all fun l => decide (1 ≤ l) && decide (l ≤ 3)))

theorem directRef_of_pk {d : QD} {GY GN GU1 GU2 GG1 GG2 : Nat → Nat} {F : Nat}
    (hF : ∀ x < 128, d.form[x]! = pg 1 (mask 1) F x)
    (bY : Bound 64 7 d.yg GY) (bN : Bound 64 7 d.ng GN) (bU1 : Bound 64 7 d.u1 GU1)
    (bU2 : Bound 64 7 d.u2 GU2) (bG1 : Bound 64 7 d.g1 GG1) (bG2 : Bound 64 7 d.g2 GG2)
    (hY : allN d.yg.length (fun j => transPK F 0 (GY j)) = true)
    (hN : allN d.ng.length (fun j => transPK F 0 (GN j)) = true)
    (hU1 : allN d.u1.length (fun j => transPK F 0 (GU1 j)) = true)
    (hU2 : allN d.u2.length (fun j => transPK F 0 (GU2 j)) = true)
    (hG1 : allN d.g1.length (fun j => transPK F 0 (GG1 j)) = true)
    (hG2 : allN d.g2.length (fun j => transPK F 0 (GG2 j)) = true)
    (hR : refRestG d = true) : directRefG d = true := by
  unfold directRefG
  unfold refRestG at hR
  simp only [allTrans_of_pk (by omega) bY hF hY, allTrans_of_pk (by omega) bN hF hN,
    allTrans_of_pk (by omega) bU1 hF hU1, allTrans_of_pk (by omega) bU2 hF hU2,
    allTrans_of_pk (by omega) bG1 hF hG1, allTrans_of_pk (by omega) bG2 hF hG2, Bool.and_true]
  exact hR

theorem kDRP : (bndK 64 7 q47YGens (PK q47YGens 7) && bndK 64 7 q47NGens (PK q47NGens 7) &&
    allN q47YGens.length (fun j => transPK q47FormP 0 (PK q47YGens 7 j)) &&
    allN q47NGens.length (fun j => transPK q47FormP 0 (PK q47NGens 7 j)) &&
    allN q47U1Gens.length (fun j => transPK q47FormP 0 (PK q47U1Gens 7 j)) &&
    allN q47U2Gens.length (fun j => transPK q47FormP 0 (PK q47U2Gens 7 j)) &&
    allN q47G1.length (fun j => transPK q47FormP 0 (PK q47G1 7 j)) &&
    allN q47G2.length (fun j => transPK q47FormP 0 (PK q47G2 7 j))) = true := by quickRfl

theorem kDRR : refRestG q47D = true := by quickRfl

theorem kDM : directMatG q47D = true := by quickRfl

theorem kDM16 : modelDirectG q47D q47M16 = true := by quickRfl

theorem kDM32 : modelDirectG q47D q47M32 = true := by quickRfl

theorem kT : (allN 6 fun k => Nat.beq (q47Trans[k]!).length (SZ k) &&
    bndK 64 7 q47Trans[k]! (TR k)) = true := by quickRfl

theorem kDT : directTransG q47D = true := by
  have hP := kDTP
  rw [Bool.and_eq_true] at hP
  refine directTrans_of_pk (SZ := SZ) (TR := TR) (F := q47FormP) rfl (fun k hk => ?_)
    (fun x hx => Nat.eq_of_beq_eq_true (allN_spec hP.1 x hx))
    (fun k hk j hj => allN_spec (List.all_eq_true.1 hP.2 k (List.mem_range.2 hk)) j hj) kDTR
  have h := allN_spec kT k hk
  rw [Bool.and_eq_true] at h
  exact ⟨Nat.eq_of_beq_eq_true h.1, bound_of_bndK h.2⟩

theorem kBnd : (bndK 64 7 q47U1Gens (PK q47U1Gens 7) && bndK 64 7 q47U2Gens (PK q47U2Gens 7) &&
    bndK 64 7 q47G1 (PK q47G1 7) && bndK 64 7 q47G2 (PK q47G2 7)) = true := by quickRfl

theorem kDR : directRefG q47D = true := by
  have hb := kBnd
  have hp := kDRP
  simp only [Bool.and_eq_true] at hb hp
  obtain ⟨⟨⟨bU1, bU2⟩, bG1⟩, bG2⟩ := hb
  obtain ⟨⟨⟨⟨⟨⟨⟨bY, bN⟩, hY⟩, hN⟩, hU1⟩, hU2⟩, hG1⟩, hG2⟩ := hp
  exact directRef_of_pk (d := q47D) (F := q47FormP) kQ47FormP (bound_of_bndK bY) (bound_of_bndK bN)
    (bound_of_bndK bU1) (bound_of_bndK bU2) (bound_of_bndK bG1) (bound_of_bndK bG2) hY hN hU1 hU2
    hG1 hG2 kDRR

theorem kPins : (bindL q47YGens 64 7 Q47Y.ng Q47Y.G && gensP 64 7 Q47Y.ng Q47Y.G &&
    bindL q47NGens 64 7 Q47N.ng Q47N.G && gensP 64 7 Q47N.ng Q47N.G &&
    bindL (q47U1Gens ++ q47YGens) 64 7 Q47UY1.ng Q47UY1.G && gensP 64 7 Q47UY1.ng Q47UY1.G &&
    bindL (q47U2Gens ++ q47YGens) 64 7 Q47UY2.ng Q47UY2.G && gensP 64 7 Q47UY2.ng Q47UY2.G &&
    bindL q47NE32 32 6 Q47NE.ng Q47NE.G && gensP 32 6 Q47NE.ng Q47NE.G) = true := by quickRfl

theorem kRun : (Nat.beq (runK 64 7 2 Q47Y.G 200).length 168 &&
    Nat.beq (runK 64 7 3 (PK q47U1Gens 7) 100).length 8 &&
    Nat.beq (runK 64 7 3 (PK q47U2Gens 7) 100).length 8) = true := by quickRfl

theorem allN_of47 {n : Nat} {f : Nat → Bool} (h : ∀ i < n, f i = true) : allN n f = true := by
  rw [allN_eq', List.all_eq_true]
  exact fun i hi => h i (List.mem_range.1 hi)

theorem matAll_of {L : List Nat} {M : List (List Nat)} {N d : Nat} {MP : Nat → Nat}
    (hMP : ∀ i, MP i = L.getD i 0) (hN : L.length = N) (h : (L.map (matOf d) == M) = true) :
    (allN N fun i => matOf d (MP i) == M[i]!) = true := by
  have e := eq_of_beq h
  refine allN_of47 fun i hi => ?_
  have hM : i < M.length := by rw [← e, List.length_map]; omega
  have hL : i < (L.map (matOf d)).length := by rw [List.length_map]; omega
  have hg : L.getD i 0 = L[i] := List.getD_eq_getElem _ _ (by omega)
  rw [hMP, hg, getElem!_pos M i hM, ← List.getElem_of_eq e hL, List.getElem_map]
  exact beq_self_eq_true _

@[expose] noncomputable def distGo (f : Nat → Nat) (n : Nat) : Nat → Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → Bool) (fun _ _ => true)
    (fun _ ih i b => strictB (f i) fun x =>
      !(b.testBit x) && strictB (b ||| 1 <<< x) fun b' => ih (i + 1) b') n

theorem strictB_q47 (y : Nat) (k : Nat → Bool) : strictB y k = k y := by cases y <;> rfl

theorem distGo_spec {f : Nat → Nat} : ∀ n i b, distGo f n i b = true → ∀ j, i ≤ j → j < i + n →
    b.testBit (f j) = false ∧ ∀ j', i ≤ j' → j' < j → f j' ≠ f j := by
  intro n
  induction n with
  | zero => intro i b _ j h1 h2; omega
  | succ n ih =>
    intro i b h j h1 h2
    have e : distGo f (n + 1) i b =
        (!(b.testBit (f i)) && distGo f n (i + 1) (b ||| 1 <<< f i)) := by
      change strictB (f i) (fun x => !(b.testBit x) &&
        strictB (b ||| 1 <<< x) fun b' => distGo f n (i + 1) b') = _
      simp only [strictB_q47]
    rw [e, Bool.and_eq_true, Bool.not_eq_true'] at h
    by_cases hj : j = i
    · subst hj
      exact ⟨h.1, fun j' h1' h2' => by omega⟩
    obtain ⟨hb, hd⟩ := ih (i + 1) _ h.2 j (by omega) (by omega)
    rw [Nat.testBit_lor, Bool.or_eq_false_iff] at hb
    have hne : f i ≠ f j := fun hij => by
      rw [← hij, Nat.one_shiftLeft, Nat.testBit_two_pow_self] at hb
      exact absurd hb.2 (by decide)
    refine ⟨hb.1, fun j' h1' h2' => ?_⟩
    by_cases hj' : j' = i
    · subst hj'
      exact hne
    exact hd j' (by omega) h2'

theorem pairs_of_distGo {N : Nat} (f : Nat → Nat) (h : distGo f N 0 0 = true) :
    (allN N fun i => allN i fun j => CFSG.KLie.CT.notB (Nat.beq (f i) (f j))) = true := by
  refine allN_of47 fun i hi => allN_of47 fun j hj => ?_
  have hne := (distGo_spec N 0 0 h i (by omega) (by omega)).2 j (by omega) hj
  cases hb : Nat.beq (f i) (f j)
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true hb).symm hne

@[expose] noncomputable def headRestK (N : Nat) (T : Nat → Nat) (MP : Nat → Nat) (d : Nat)
    (scal : List Nat → Bool) : Bool :=
  CFSG.KLie.CT.andB (Nat.beq (T 0) (pidn 64 7))
    (allN N fun i => CFSG.KLie.CT.orB (Nat.beq i 0) (CFSG.KLie.CT.notB (scal (matOf d (MP i)))))

theorem headRest_of {L : List Nat} {N d : Nat} {T MP : Nat → Nat} {scal : List Nat → Bool}
    (hMP : ∀ i, MP i = L.getD i 0) (hN : L.length = N)
    (h : (Nat.beq (T 0) (pidn 64 7) &&
      (L.drop 1).all fun m => CFSG.KLie.CT.notB (scal (matOf d m))) = true) :
    headRestK N T MP d scal = true := by
  rw [Bool.and_eq_true, List.all_eq_true] at h
  unfold headRestK
  rw [h.1]
  refine allN_of47 fun i hi => ?_
  rcases i with _ | j
  · rfl
  · have hg : L.getD (j + 1) 0 = L[j + 1] := List.getD_eq_getElem _ _ (by omega)
    rw [hMP, hg]
    have hm : L[j + 1] ∈ L.drop 1 := List.mem_iff_getElem.2
      ⟨j, by rw [List.length_drop]; omega, by
        simp only [List.getElem_drop]
        congr 1
        omega⟩
    exact h.2 _ hm

theorem tableHead_of {N : Nat} {T MP : Nat → Nat} {d : Nat} {scal : List Nat → Bool}
    (h : (distGo (fun i => key3K (T i)) N 0 0 && headRestK N T MP d scal) = true) :
    tableHeadK N T MP d scal = true := by
  rw [Bool.and_eq_true] at h
  unfold tableHeadK
  rw [pairs_of_distGo (fun i => key3K (T i)) h.1]
  exact h.2

theorem kMHD : (Nat.beq MPYL.length 168 && Nat.beq MPNL.length 336 && Nat.beq Q47Y.N 168 &&
    Nat.beq Q47N.N 336 && (MPYL.map (matOf 3) == q47YMat) && (MPNL.map (matOf 2) == q47NMat) &&
    distGo (fun i => key3K (Q47Y.T i)) Q47Y.N 0 0 && distGo (fun i => key3K (Q47N.T i)) Q47N.N 0 0 &&
    (Nat.beq (Q47Y.T 0) (pidn 64 7) && (MPYL.drop 1).all fun m =>
      CFSG.KLie.CT.notB (matOf 3 m == [1, 0, 0, 0, 1, 0, 0, 0, 1])) &&
    (Nat.beq (Q47N.T 0) (pidn 64 7) && (MPNL.drop 1).all fun m =>
      CFSG.KLie.CT.notB ((matOf 2 m)[1]! == 0 && (matOf 2 m)[2]! == 0 &&
        (matOf 2 m)[0]! == (matOf 2 m)[3]!))) = true := by quickRfl

theorem kMH : (((allN 168 fun i => matOf 3 (MPY i) == q47YMat[i]!) &&
    allN 336 fun i => matOf 2 (MPN i) == q47NMat[i]!) &&
    (tableHeadK Q47Y.N Q47Y.T MPY 3 (· == [1, 0, 0, 0, 1, 0, 0, 0, 1]) &&
    tableHeadK Q47N.N Q47N.T MPN 2 (fun m => m[1]! == 0 && m[2]! == 0 && m[0]! == m[3]!))) =
    true := by
  have h := kMHD
  simp only [Bool.and_eq_true] at h ⊢
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨l1, l2⟩, l3⟩, l4⟩, mY⟩, mN⟩, dY⟩, dN⟩, tY, aY⟩, tN, aN⟩ := h
  have lY := Nat.eq_of_beq_eq_true l1
  have lN := Nat.eq_of_beq_eq_true l2
  have nY := Nat.eq_of_beq_eq_true l3
  have nN := Nat.eq_of_beq_eq_true l4
  exact ⟨⟨matAll_of (fun _ => rfl) lY mY, matAll_of (fun _ => rfl) lN mN⟩,
    tableHead_of (Bool.and_eq_true_iff.2 ⟨dY, headRest_of (fun _ => rfl) (lY.trans nY.symm)
      (scal := (· == [1, 0, 0, 0, 1, 0, 0, 0, 1])) (Bool.and_eq_true_iff.2 ⟨tY, aY⟩)⟩),
    tableHead_of (Bool.and_eq_true_iff.2 ⟨dN, headRest_of (fun _ => rfl) (lN.trans nN.symm)
      (scal := fun m => m[1]! == 0 && m[2]! == 0 && m[0]! == m[3]!)
      (Bool.and_eq_true_iff.2 ⟨tN, aN⟩)⟩)⟩

theorem kMP : ((allN 168 fun i => matOf 3 (MPY i) == q47YMat[i]!) &&
    allN 336 fun i => matOf 2 (MPN i) == q47NMat[i]!) = true := by
  have h := kMH
  rw [Bool.and_eq_true] at h
  exact h.1

theorem kRef : refPK (runK 64 7 2 Q47Y.G 200) Q47Y.G (PK q47U1Gens 7) (PK q47U2Gens 7)
    (runK 64 7 3 (PK q47U1Gens 7) 100) (runK 64 7 3 (PK q47U2Gens 7) 100) Q47N.G Q47N.N Q47N.T
    q47W1 q47W2 q47Orb q47OrbRep q47L30 = true := by quickRfl

theorem kHead : (tableHeadK Q47Y.N Q47Y.T MPY 3 (· == [1, 0, 0, 0, 1, 0, 0, 0, 1]) &&
    tableHeadK Q47N.N Q47N.T MPN 2 (fun m => m[1]! == 0 && m[2]! == 0 && m[0]! == m[3]!)) = true := by
  have h := kMH
  rw [Bool.and_eq_true] at h
  exact h.2

@[expose] noncomputable def addBK (t : Nat) : Bool :=
  allN 64 fun u => allN 6 fun i =>
    Nat.beq (pg 7 (mask 7) t (Nat.xor u (2 ^ i))) (Nat.xor (pg 7 (mask 7) t u) (pg 7 (mask 7) t (2 ^ i)))

theorem xorLow64 : ∀ v < 64, v ≠ 0 → ∃ i < 6, v ^^^ 2 ^ i < v := by decide

theorem addK_of_addBK {t : Nat} (h : addBK t = true) : addK t = true := by
  have hb : ∀ u < 64, ∀ i < 6, pg 7 (mask 7) t (u ^^^ 2 ^ i) =
      pg 7 (mask 7) t u ^^^ pg 7 (mask 7) t (2 ^ i) := fun u hu i hi =>
    Nat.eq_of_beq_eq_true (allN_spec (allN_spec h u hu) i hi)
  have h0 : pg 7 (mask 7) t 0 = 0 := by
    have h1 := hb 0 (by decide) 0 (by decide)
    rw [Nat.zero_xor] at h1
    have h2 := congrArg (· ^^^ pg 7 (mask 7) t (2 ^ 0)) h1
    simpa only [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero] using h2.symm
  have key : ∀ v, v < 64 → ∀ u < 64, pg 7 (mask 7) t (u ^^^ v) =
      pg 7 (mask 7) t u ^^^ pg 7 (mask 7) t v := by
    intro v
    refine Nat.strong_induction_on v fun v ih => ?_
    intro hv u hu
    by_cases hz : v = 0
    · subst hz
      rw [Nat.xor_zero, h0, Nat.xor_zero]
    obtain ⟨i, hi, hw⟩ := xorLow64 v hv hz
    have hv' : v = (v ^^^ 2 ^ i) ^^^ 2 ^ i := by
      rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
    have huw : u ^^^ (v ^^^ 2 ^ i) < 64 := Nat.xor_lt_two_pow (n := 6) hu (by omega)
    rw [hv', ← Nat.xor_assoc, hb _ huw i hi, ih _ hw (by omega) u hu,
      hb (v ^^^ 2 ^ i) (by omega) i hi, Nat.xor_assoc]
  unfold addK
  refine allN_of47 fun u hu => allN_of47 fun v hv => ?_
  exact Nat.beq_eq.mpr (key v hv u hu)

theorem kAddB : ((List.range 6).all (fun k => allN (SZ k) fun j => addBK (TR k j)) &&
    allN 2 (fun k => addBK (Q47Y.G k) && addBK (Q47N.G k)) &&
    allN 3 (fun k => addBK (PK q47U1Gens 7 k) && addBK (PK q47U2Gens 7 k)) &&
    allN 4 (fun k => addBK (PK q47G1 7 k) && addBK (PK q47G2 7 k) && addBK (K16.CP k) &&
      addBK (K32.CP k))) = true := by quickRfl

theorem kAdd : ((List.range 6).all (fun k => allN (SZ k) fun j => addK (TR k j)) &&
    allN 2 (fun k => addK (Q47Y.G k) && addK (Q47N.G k)) &&
    allN 3 (fun k => addK (PK q47U1Gens 7 k) && addK (PK q47U2Gens 7 k)) &&
    allN 4 (fun k => addK (PK q47G1 7 k) && addK (PK q47G2 7 k) && addK (K16.CP k) &&
      addK (K32.CP k))) = true := by
  have h := kAddB
  simp only [Bool.and_eq_true, List.all_eq_true] at h ⊢
  obtain ⟨⟨⟨hT, h2⟩, h3⟩, h4⟩ := h
  refine ⟨⟨⟨fun k hk => allN_of47 fun j hj => addK_of_addBK (allN_spec (hT k hk) j hj),
    allN_of47 fun k hk => ?_⟩, allN_of47 fun k hk => ?_⟩, allN_of47 fun k hk => ?_⟩
  · have e := allN_spec h2 k hk
    rw [Bool.and_eq_true] at e ⊢
    exact ⟨addK_of_addBK e.1, addK_of_addBK e.2⟩
  · have e := allN_spec h3 k hk
    rw [Bool.and_eq_true] at e ⊢
    exact ⟨addK_of_addBK e.1, addK_of_addBK e.2⟩
  · have e := allN_spec h4 k hk
    simp only [Bool.and_eq_true] at e ⊢
    exact ⟨⟨⟨addK_of_addBK e.1.1.1, addK_of_addBK e.1.1.2⟩, addK_of_addBK e.1.2⟩,
      addK_of_addBK e.2⟩

theorem kBC : bcK BC = true := by quickRfl

theorem kB16 : (bndK 16 5 q47Rep16 K16.REP &&
    (Nat.beq heSylZ16.size 16 && bindListFromK heSylZ16.toList 5 K16.PZ 0) &&
    permOK 16 5 (mask 5) (16 * 5) K16.PZ (pinvS 16 5 (mask 5) K16.PZ) &&
    bndK 64 7 q47D16 K16.GD && bndK 64 7 q47Eb16 K16.GEb && bndK 64 7 q47Fb16 K16.GFb &&
    (allN 4 fun i => bndK 64 7 (kListG q47M16 i) (K16.GK i)) && bndK 64 7 q47C16 K16.CP) = true := by
  quickRfl

theorem kB32 : (bndK 32 6 q47Rep32 K32.REP &&
    (Nat.beq heAutZ32.size 32 && bindListFromK heAutZ32.toList 6 K32.PZ 0) &&
    permOK 32 6 (mask 6) (32 * 6) K32.PZ (pinvS 32 6 (mask 6) K32.PZ) &&
    bndK 64 7 q47D32 K32.GD && bndK 64 7 q47Eb32 K32.GEb && bndK 64 7 q47Fb32 K32.GFb &&
    (allN 4 fun i => bndK 64 7 (kListG q47M32 i) (K32.GK i)) && bndK 64 7 q47C32 K32.CP) = true := by
  quickRfl

theorem mulA47 {n w a b c : Nat} (ha : PP n w a) (hc : PP n w c) :
    mul n w (mul n w a b) c = mul n w a (mul n w b c) := by
  obtain ⟨hn, hw, -, -⟩ := CFSG.KS.PF.canon_facts ha.1
  obtain ⟨-, -, -, hcc⟩ := CFSG.KS.PF.canon_facts hc.1
  have hn32 : n < 2 ^ 32 := by omega
  have hw0 := CFSG.KS.PF.w_pos hw
  unfold mul
  refine CFSG.KS.PF.eq_of_fields hw0 (CFSG.KS.PF.pcomp_shr _ _ hn32 hw0)
    (CFSG.KS.PF.pcomp_shr _ _ hn32 hw0) fun i hi => ?_
  rw [CFSG.KS.PF.pg_pcomp hn32 hi, CFSG.KS.PF.pg_pcomp hn32 (hcc i hi), CFSG.KS.PF.pg_pcomp hn32 hi,
    CFSG.KS.PF.pg_pcomp hn32 hi]

theorem mulId47 {n w a : Nat} (ha : PP n w a) : mul n w a (pidn n w) = a := by
  obtain ⟨hn, hw, hsh, -⟩ := CFSG.KS.PF.canon_facts ha.1
  have hn32 : n < 2 ^ 32 := by omega
  have hw0 := CFSG.KS.PF.w_pos hw
  unfold mul
  refine CFSG.KS.PF.eq_of_fields hw0 (CFSG.KS.PF.pcomp_shr _ _ hn32 hw0) hsh fun i hi => ?_
  rw [CFSG.KS.PF.pg_pcomp hn32 hi, CFSG.KS.PF.pg_pidn hn hw hi]

def zRel47 (n w z x y : Nat) : Prop := x = y ∨ x = mul n w y z

section zRel

variable {n w z : Nat} (hz : PP n w z) (hzz : mul n w z z = pidn n w)
include hz hzz

theorem zRel47_back {x y : Nat} (hy : PP n w y) (h : x = mul n w y z) : mul n w x z = y := by
  rw [h, mulA47 hy hz, hzz, mulId47 hy]

theorem zRel47_symm {x y : Nat} (hy : PP n w y) (h : zRel47 n w z x y) : zRel47 n w z y x := by
  rcases h with e | e
  · exact Or.inl e.symm
  · exact Or.inr (zRel47_back hz hzz hy e).symm

theorem zRel47_trans {x y t : Nat} (ht : PP n w t) (h1 : zRel47 n w z x y)
    (h2 : zRel47 n w z y t) : zRel47 n w z x t := by
  rcases h1 with e1 | e1 <;> rcases h2 with e2 | e2
  · exact Or.inl (e1.trans e2)
  · exact Or.inr (e1.trans e2)
  · exact Or.inr (by rw [e1, e2])
  · exact Or.inl (by rw [e1, e2, mulA47 ht hz, hzz, mulId47 ht])

omit hzz in
theorem zRel47_left {x y c : Nat} (hc : PP n w c) (h : zRel47 n w z x y) :
    zRel47 n w z (mul n w c x) (mul n w c y) := by
  rcases h with e | e
  · exact Or.inl (by rw [e])
  · exact Or.inr (by rw [e, mulA47 hc hz])

omit hzz in
theorem zRel47_right {x y b : Nat} (hb : PP n w b) (hy : PP n w y)
    (hbz : mul n w b z = mul n w z b) (h : zRel47 n w z x y) :
    zRel47 n w z (mul n w x b) (mul n w y b) := by
  rcases h with e | e
  · exact Or.inl (by rw [e])
  · exact Or.inr (by rw [e, mulA47 hy hb, ← hbz, ← mulA47 hy hz])

theorem prodAll_of_basis {R : Nat → Nat} (hR : ∀ v < 64, PP n w (R v)) (h0 : R 0 = pidn n w)
    (hc : ∀ i < 6, mul n w (R (2 ^ i)) z = mul n w z (R (2 ^ i)))
    (hb : ∀ u < 64, ∀ i < 6, zRel47 n w z (mul n w (R u) (R (2 ^ i))) (R (u ^^^ 2 ^ i))) :
    ∀ v < 64, ∀ u < 64, zRel47 n w z (mul n w (R u) (R v)) (R (u ^^^ v)) := by
  intro v
  refine Nat.strong_induction_on v fun v ih => ?_
  intro hv u hu
  by_cases hzv : v = 0
  · subst hzv
    rw [h0, mulId47 (hR u hu), Nat.xor_zero]
    exact Or.inl rfl
  obtain ⟨i, hi, hw⟩ := xorLow64 v hv hzv
  have h2 : 2 ^ i < 64 := lt_of_lt_of_le (Nat.pow_lt_pow_right (by decide) (by omega : i < 6))
    (by decide)
  have hv' : (v ^^^ 2 ^ i) ^^^ 2 ^ i = v := by rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
  have huw : u ^^^ (v ^^^ 2 ^ i) < 64 := Nat.xor_lt_two_pow (n := 6) hu (by omega)
  have hB := hR _ h2
  have e1 := hb _ (lt_trans hw hv) i hi
  rw [hv'] at e1
  have s1 := zRel47_left hz (hR u hu) (zRel47_symm hz hzz (hR v hv) e1)
  rw [← mulA47 (hR u hu) hB] at s1
  have s2 := zRel47_right hz hB (hR _ huw) (hc i hi) (ih _ hw (by omega) u hu)
  have s3 := hb _ huw i hi
  rw [Nat.xor_assoc, hv'] at s3
  have hx : u ^^^ v < 64 := Nat.xor_lt_two_pow (n := 6) hu hv
  exact zRel47_trans hz hzz (hR _ hx) s1 (zRel47_trans hz hzz (hR _ hx) s2 s3)

end zRel

theorem andB_eq47 (a b : Bool) : CFSG.KLie.CT.andB a b = (a && b) := by cases a <;> rfl

theorem orB_eq47 (a b : Bool) : CFSG.KLie.CT.orB a b = (a || b) := by cases a <;> rfl

@[expose] noncomputable def repBK (n w : Nat) (REP : Nat → Nat) (NQ : Nat) (TQ : Nat → Nat)
    (z : Nat) (form : Array Nat) : Bool :=
  CFSG.KLie.CT.andB (CFSG.KLie.CT.andB (Nat.beq (mul n w z z) (pidn n w))
    (CFSG.KLie.CT.andB (allN 6 fun i => Nat.beq (mul n w (REP (2 ^ i)) z) (mul n w z (REP (2 ^ i))))
      (allN 64 fun u => allN 6 fun i => strictB (mul n w (REP u) (REP (2 ^ i))) fun q =>
        CFSG.KLie.CT.orB (Nat.beq q (REP (Nat.xor u (2 ^ i))))
          (Nat.beq q (mul n w (REP (Nat.xor u (2 ^ i))) z)))))
  (CFSG.KLie.CT.andB (Nat.beq (REP 0) (pidn n w))
  (CFSG.KLie.CT.andB (allN 64 fun v => inL NQ TQ (REP v))
  (CFSG.KLie.CT.andB (allN NQ fun k => strictB (TQ k) fun x =>
      CFSG.KLie.CT.anyN 64 fun v =>
        CFSG.KLie.CT.orB (Nat.beq x (REP v)) (Nat.beq x (mul n w (REP v) z)))
    (allN 64 fun v => strictB (mul n w (REP v) (REP v)) fun q =>
      CFSG.KLie.CT.orB (CFSG.KLie.CT.andB (Nat.beq q (pidn n w)) (Nat.beq form[v]! 0))
        (CFSG.KLie.CT.andB (Nat.beq q z) (Nat.beq form[v]! 1))))))

theorem repK_of_repBK {n w : Nat} {REP : Nat → Nat} {NQ : Nat} {TQ : Nat → Nat} {z : Nat}
    {form : Array Nat} (hR : ∀ v < 64, PP n w (REP v)) (hz : PP n w z)
    (h : repBK n w REP NQ TQ z form = true) : repK n w REP NQ TQ z form = true := by
  unfold repBK at h
  unfold repK
  simp only [andB_eq47, Bool.and_eq_true] at h ⊢
  obtain ⟨⟨hzz, hc, hb⟩, h1, h2, h4, h5⟩ := h
  refine ⟨h1, h2, ?_, h4, h5⟩
  have key := prodAll_of_basis hz (Nat.eq_of_beq_eq_true hzz) hR (Nat.eq_of_beq_eq_true h1)
    (fun i hi => Nat.eq_of_beq_eq_true (allN_spec hc i hi)) (fun u hu i hi => by
      have e := allN_spec (allN_spec hb u hu) i hi
      simp only [strictB_q47, orB_eq47, Bool.or_eq_true] at e
      rcases e with e | e
      · exact Or.inl (Nat.eq_of_beq_eq_true e)
      · exact Or.inr (Nat.eq_of_beq_eq_true e))
  refine allN_of47 fun u hu => allN_of47 fun v hv => ?_
  simp only [strictB_q47, orB_eq47, Bool.or_eq_true]
  rcases key v hv u hu with e | e
  · exact Or.inl (Nat.beq_eq.mpr e)
  · exact Or.inr (Nat.beq_eq.mpr e)

theorem kRepB16 : (Nat.beq q47Rep16.length 64 &&
    repBK 16 5 K16.REP K16.NQ K16.TQ K16.PZ q47Form) = true := by quickRfl

theorem kRepB32 : (Nat.beq q47Rep32.length 64 &&
    repBK 32 6 K32.REP K32.NQ K32.TQ K32.PZ q47Form) = true := by quickRfl

theorem kRep16 : repK 16 5 K16.REP K16.NQ K16.TQ K16.PZ q47Form = true := by
  have hb := kB16
  have hr := kRepB16
  simp only [Bool.and_eq_true] at hb hr
  have hB := bound_of_bndK hb.1.1.1.1.1.1.1
  have hsz : szOK 16 5 = true := by decide
  exact repK_of_repBK (fun v hv => PP_of_permOK hsz
    (hB v (by rw [Nat.eq_of_beq_eq_true hr.1]; exact hv)).2) (PP_of_permOK hsz hb.1.1.1.1.1.2) hr.2

theorem kRep32 : repK 32 6 K32.REP K32.NQ K32.TQ K32.PZ q47Form = true := by
  have hb := kB32
  have hr := kRepB32
  simp only [Bool.and_eq_true] at hb hr
  have hB := bound_of_bndK hb.1.1.1.1.1.1.1
  have hsz : szOK 32 6 = true := by decide
  exact repK_of_repBK (fun v hv => PP_of_permOK hsz
    (hB v (by rw [Nat.eq_of_beq_eq_true hr.1]; exact hv)).2) (PP_of_permOK hsz hb.1.1.1.1.1.2) hr.2

theorem idMul47 {n w a : Nat} (ha : PP n w a) : mul n w (pidn n w) a = a := by
  obtain ⟨hn, hw, hsh, hcc⟩ := CFSG.KS.PF.canon_facts ha.1
  have hn32 : n < 2 ^ 32 := by omega
  have hw0 := CFSG.KS.PF.w_pos hw
  unfold mul
  refine CFSG.KS.PF.eq_of_fields hw0 (CFSG.KS.PF.pcomp_shr _ _ hn32 hw0) hsh fun i hi => ?_
  rw [CFSG.KS.PF.pg_pcomp hn32 hi, CFSG.KS.PF.pg_pidn hn hw (hcc i hi)]

def addN47 (L : List Nat) (y : Nat) : List Nat := if y ∈ L then L else L ++ [y]

theorem runStep_rec47 {n w : Nat} {G : Nat → Nat} (x : Nat) (pts : List Nat) : ∀ m,
    Nat.rec (motive := fun _ => List Nat) pts (fun k acc => strictL (mul n w (G k) x) fun y =>
      Bool.rec (motive := fun _ => List Nat) (acc ++ [y]) acc (memK acc y)) m =
    (List.range m).foldl (fun acc k => addN47 acc (mul n w (G k) x)) pts
  | 0 => rfl
  | m + 1 => by
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, ← runStep_rec47 x pts m]
    have e : ∀ acc : List Nat, strictL (mul n w (G m) x) (fun y =>
        Bool.rec (motive := fun _ => List Nat) (acc ++ [y]) acc (memK acc y)) =
        addN47 acc (mul n w (G m) x) := by
      intro acc
      rw [strictL_eq', memK_eq]
      unfold addN47
      by_cases h : mul n w (G m) x ∈ acc
      · rw [decide_eq_true h, ite_eq_left h]
      · rw [decide_eq_false h, ite_eq_right h]
    exact e _

theorem foldl_addN47 (f : Nat → Nat) : ∀ (ks : List Nat) (L : List Nat),
    L.length ≤ (ks.foldl (fun acc k => addN47 acc (f k)) L).length ∧
    (∀ j < L.length, (ks.foldl (fun acc k => addN47 acc (f k)) L).getD j 0 = L.getD j 0) ∧
    (∀ z ∈ L, z ∈ ks.foldl (fun acc k => addN47 acc (f k)) L) ∧
    (∀ k ∈ ks, f k ∈ ks.foldl (fun acc k => addN47 acc (f k)) L) ∧
    (∀ z ∈ ks.foldl (fun acc k => addN47 acc (f k)) L, z ∈ L ∨ ∃ k ∈ ks, z = f k) ∧
    (L.Nodup → (ks.foldl (fun acc k => addN47 acc (f k)) L).Nodup)
  | [], L => ⟨le_rfl, fun _ _ => rfl, fun _ h => h, fun _ h => absurd h List.not_mem_nil,
      fun _ h => Or.inl h, id⟩
  | k :: ks, L => by
    rw [List.foldl_cons]
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := foldl_addN47 f ks (addN47 L (f k))
    by_cases hm : f k ∈ L
    · have e : addN47 L (f k) = L := ite_eq_left hm
      rw [e] at h1 h2 h3 h4 h5 h6 ⊢
      refine ⟨h1, h2, h3, fun k' hk' => ?_, fun z hz => ?_, h6⟩
      · rcases List.mem_cons.1 hk' with rfl | hk'
        · exact h3 _ hm
        · exact h4 k' hk'
      · rcases h5 z hz with hz | ⟨k', hk', e'⟩
        · exact Or.inl hz
        · exact Or.inr ⟨k', List.mem_cons_of_mem k hk', e'⟩
    · have e : addN47 L (f k) = L ++ [f k] := ite_eq_right hm
      rw [e] at h1 h2 h3 h4 h5 h6 ⊢
      have hl : L.length ≤ (L ++ [f k]).length := by
        rw [List.length_append]
        omega
      refine ⟨le_trans hl h1, fun j hj => ?_, fun z hz => h3 z (List.mem_append_left _ hz),
        fun k' hk' => ?_, fun z hz => ?_, fun hn => h6 ?_⟩
      · rw [h2 j (lt_of_lt_of_le hj hl), List.getD_append _ _ _ _ hj]
      · rcases List.mem_cons.1 hk' with rfl | hk'
        · exact h3 _ (List.mem_append_right _ (List.mem_singleton_self _))
        · exact h4 k' hk'
      · rcases h5 z hz with hz | ⟨k', hk', e'⟩
        · rcases List.mem_append.1 hz with hz | hz
          · exact Or.inl hz
          · exact Or.inr ⟨k, List.mem_cons_self, List.mem_singleton.1 hz⟩
        · exact Or.inr ⟨k', List.mem_cons_of_mem k hk', e'⟩
      · rw [← List.concat_eq_append]
        exact hn.concat hm

noncomputable def rkF47 (n w ng : Nat) (G : Nat → Nat) (st : List Nat × Nat) : List Nat × Nat :=
  if st.2 < st.1.length then (runStep n w ng G (st.1.getD st.2 0) st.1, st.2 + 1) else st

theorem runK_iter47 {n w ng : Nat} {G : Nat → Nat} (fuel : Nat) :
    runK n w ng G fuel = ((rkF47 n w ng G)^[fuel] ([pidn n w], 0)).1 := by
  unfold CFSG.KC.Q47K.runK
  congr 1
  induction fuel with
  | zero => rfl
  | succ f ih =>
    rw [Function.iterate_succ_apply', ← ih]
    have e : ∀ st : List Nat × Nat, Bool.rec (motive := fun _ => List Nat × Nat) st
        (runStep n w ng G (st.1.getD st.2 0) st.1, Nat.succ st.2) (Nat.blt st.2 st.1.length) =
        rkF47 n w ng G st := by
      intro st
      unfold rkF47
      cases h : Nat.blt st.2 st.1.length
      · rw [ite_eq_right fun h' => by rw [Nat.blt_eq.mpr h'] at h; cases h]
      · rw [ite_eq_left (Nat.blt_eq.mp h)]
    exact e _

theorem rkF_count47 {n w ng : Nat} {G : Nat → Nat} (s : List Nat × Nat) (hs : s.2 = 0) : ∀ f,
    ((rkF47 n w ng G)^[f] s).2 = f ∨ rkF47 n w ng G ((rkF47 n w ng G)^[f] s) = (rkF47 n w ng G)^[f] s
  | 0 => Or.inl hs
  | f + 1 => by
    rw [Function.iterate_succ_apply']
    rcases rkF_count47 s hs f with h | h
    · generalize (rkF47 n w ng G)^[f] s = t at h ⊢
      by_cases hlt : t.2 < t.1.length
      · have e : rkF47 n w ng G t = (runStep n w ng G (t.1.getD t.2 0) t.1, t.2 + 1) := ite_eq_left hlt
        rw [e]
        exact Or.inl (by rw [h])
      · have e : rkF47 n w ng G t = t := ite_eq_right hlt
        rw [e]
        exact Or.inr e
    · rw [h]
      exact Or.inr h

def RI47 (n w ng : Nat) (G : Nat → Nat) (S : Nat → Prop) (st : List Nat × Nat) : Prop :=
  (∀ y ∈ st.1, S y) ∧ st.1.Nodup ∧ st.2 ≤ st.1.length ∧
    (∀ j < st.2, ∀ k < ng, mul n w (G k) (st.1.getD j 0) ∈ st.1) ∧ pidn n w ∈ st.1

section RI

variable {n w ng : Nat} {G : Nat → Nat} {S : Nat → Prop}

theorem ri47_step (hS : ∀ y, S y → ∀ k < ng, S (mul n w (G k) y)) {st : List Nat × Nat}
    (h : RI47 n w ng G S st) : RI47 n w ng G S (rkF47 n w ng G st) := by
  obtain ⟨L, i⟩ := st
  obtain ⟨h1, h0, h2, h3, h5⟩ := h
  dsimp only at h1 h0 h2 h3 h5
  unfold rkF47
  dsimp only
  split
  · next hlt =>
    have hr : runStep n w ng G (L.getD i 0) L =
        (List.range ng).foldl (fun acc k => addN47 acc (mul n w (G k) (L.getD i 0))) L :=
      runStep_rec47 _ L ng
    rw [hr]
    obtain ⟨f1, f2, f3, f4, f5, f6⟩ := foldl_addN47 (fun k => mul n w (G k) (L.getD i 0))
      (List.range ng) L
    refine ⟨fun y hy => ?_, f6 h0, Nat.succ_le_of_lt (lt_of_lt_of_le hlt f1),
      fun j hj k hk => ?_, f3 _ h5⟩
    · rcases f5 y hy with hy | ⟨k, hk, rfl⟩
      · exact h1 y hy
      · exact hS _ (h1 _ (getD_mem hlt)) k (List.mem_range.1 hk)
    · rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
      · rw [f2 j (by omega)]
        exact f3 _ (h3 j hj k hk)
      · rw [f2 _ hlt]
        exact f4 k (List.mem_range.2 hk)
  · exact ⟨h1, h0, h2, h3, h5⟩

theorem ri47_run (hS : ∀ y, S y → ∀ k < ng, S (mul n w (G k) y)) (h0 : S (pidn n w))
    (fuel : Nat) : RI47 n w ng G S ((rkF47 n w ng G)^[fuel] ([pidn n w], 0)) := by
  induction fuel with
  | zero =>
    exact ⟨fun y hy => by rw [List.mem_singleton.1 hy]; exact h0, List.nodup_singleton _,
      Nat.zero_le _, fun j hj => absurd hj (Nat.not_lt_zero j), List.mem_singleton_self _⟩
  | succ f ih =>
    rw [Function.iterate_succ_apply']
    exact ri47_step hS ih

theorem runK_in47 (hS : ∀ y, S y → ∀ k < ng, S (mul n w (G k) y)) (h0 : S (pidn n w))
    (fuel : Nat) : (∀ y ∈ runK n w ng G fuel, S y) ∧ (runK n w ng G fuel).Nodup ∧
      pidn n w ∈ runK n w ng G fuel := by
  rw [runK_iter47]
  have h := ri47_run hS h0 fuel
  exact ⟨h.1, h.2.1, h.2.2.2.2⟩

theorem runK_closed47 {fuel : Nat} (hf : (runK n w ng G fuel).length ≤ fuel) :
    ∀ y ∈ runK n w ng G fuel, ∀ k < ng, mul n w (G k) y ∈ runK n w ng G fuel := by
  rw [runK_iter47] at hf ⊢
  have hI := ri47_run (n := n) (w := w) (ng := ng) (G := G) (S := fun _ => True)
    (fun _ _ _ _ => trivial) trivial fuel
  have hc := rkF_count47 (n := n) (w := w) (ng := ng) (G := G) ([pidn n w], 0) rfl fuel
  generalize (rkF47 n w ng G)^[fuel] ([pidn n w], 0) = st at hI hf hc ⊢
  obtain ⟨-, -, h2, h3, -⟩ := hI
  have hlen : st.2 = st.1.length := by
    rcases hc with h | h
    · omega
    · by_contra hne
      have e := congrArg Prod.snd h
      unfold rkF47 at e
      rw [ite_eq_left (lt_of_le_of_ne h2 hne)] at e
      simp at e
  intro y hy k hk
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hy
  have := h3 j (by omega) k hk
  rwa [List.getD_eq_getElem _ _ hj] at this

end RI

@[expose] noncomputable def subOK47 (n w ng : Nat) (G : Nat → Nat) (SL : List Nat)
    (fuel fuel' : Nat) : Bool :=
  CFSG.KLie.CT.andB (allN SL.length fun i => CFSG.KLie.CT.andB (Nat.blt (SL.getD i 0) ng)
    (permOK n w (mask w) (n * w) (G (SL.getD i 0)) (pinvS n w (mask w) (G (SL.getD i 0)))))
  (CFSG.KLie.CT.andB (Nat.ble (runK n w SL.length (fun i => G (SL.getD i 0)) fuel').length fuel')
  (CFSG.KLie.CT.andB (Nat.ble (runK n w SL.length (fun i => G (SL.getD i 0)) fuel').length fuel)
    (allN ng fun k => memK (runK n w SL.length (fun i => G (SL.getD i 0)) fuel') (G k))))

theorem runK_sub47 {n w ng fuel fuel' : Nat} {G : Nat → Nat} {SL : List Nat}
    (hsz : szOK n w = true) (h : subOK47 n w ng G SL fuel fuel' = true) :
    (runK n w ng G fuel).length = (runK n w SL.length (fun i => G (SL.getD i 0)) fuel').length ∧
    ∀ x, memK (runK n w ng G fuel) x = memK (runK n w SL.length (fun i => G (SL.getD i 0)) fuel') x := by
  unfold subOK47 at h
  simp only [andB_eq47, Bool.and_eq_true] at h
  obtain ⟨hs, hf', hf, hm⟩ := h
  generalize hL' : runK n w SL.length (fun i => G (SL.getD i 0)) fuel' = L' at hf' hf hm ⊢
  have hsi : ∀ i < SL.length, SL.getD i 0 < ng ∧ PP n w (G (SL.getD i 0)) := fun i hi => by
    have e := allN_spec hs i hi
    simp only [Bool.and_eq_true] at e
    exact ⟨Nat.blt_eq.mp e.1, PP_of_permOK hsz e.2⟩
  have hPid := PP.id (n := n) (w := w) hsz
  have hfl' := Nat.le_of_ble_eq_true hf'
  have hfl := Nat.le_of_ble_eq_true hf
  have cl' := runK_closed47 (hL' ▸ hfl')
  rw [hL'] at cl'
  obtain ⟨pp', nd', id'⟩ := runK_in47 (n := n) (w := w) (ng := SL.length)
    (G := fun i => G (SL.getD i 0)) (S := PP n w) (fun y hy k hk => (hsi k hk).2.mul hy) hPid fuel'
  rw [hL'] at pp' nd' id'
  have mon : ∀ x ∈ L', ∀ y ∈ L', mul n w x y ∈ L' := by
    have := (runK_in47 (n := n) (w := w) (ng := SL.length) (G := fun i => G (SL.getD i 0))
      (S := fun x => ∀ y ∈ L', mul n w x y ∈ L') (fun x hx k hk y hy => by
        rw [mulA47 (hsi k hk).2 (pp' y hy)]
        exact cl' _ (hx y hy) k hk) (fun y hy => by rw [idMul47 (pp' y hy)]; exact hy) fuel').1
    rw [hL'] at this
    exact this
  have hG : ∀ k < ng, G k ∈ L' := fun k hk => by
    have e := allN_spec hm k hk
    rw [memK_eq] at e
    exact of_decide_eq_true e
  obtain ⟨hsub, nd, idL⟩ := runK_in47 (n := n) (w := w) (ng := ng) (G := G) (S := (· ∈ L'))
    (fun y hy k hk => mon _ (hG k hk) _ hy) id' fuel
  have hle : (runK n w ng G fuel).length ≤ L'.length := nd.length_le_of_subset hsub
  have cl := runK_closed47 (n := n) (w := w) (ng := ng) (G := G) (le_trans hle hfl)
  have hsup := (runK_in47 (n := n) (w := w) (ng := SL.length) (G := fun i => G (SL.getD i 0))
    (S := (· ∈ runK n w ng G fuel)) (fun y hy k hk => cl y hy _ (hsi k hk).1) idL fuel').1
  rw [hL'] at hsup
  refine ⟨le_antisymm hle (nd'.length_le_of_subset hsup), fun x => ?_⟩
  rw [memK_eq, memK_eq]
  exact decide_eq_decide.2 ⟨fun hx => hsub x hx, fun hx => hsup x hx⟩

theorem allN_congr47 {N : Nat} {f g : Nat → Bool} (h : ∀ i < N, f i = g i) :
    allN N f = allN N g := by
  rw [allN_eq', allN_eq']
  apply Bool.eq_iff_iff.2
  simp only [List.all_eq_true, List.mem_range]
  exact ⟨fun h1 i hi => by rw [← h i hi]; exact h1 i hi,
    fun h1 i hi => by rw [h i hi]; exact h1 i hi⟩

theorem modelYK_congr47 {n w gNE NX gE NE gF NF gD gY : Nat}
    {GNE TX GE TE GF TF GD GY CP : Nat → Nat} {LL LL' LK LK' : Nat → List Nat}
    (hL : ∀ l < 4, ∀ x, memK (LL l) x = memK (LL' l) x)
    (h : ∀ c < 4, ∀ x, memK (LK c) x = memK (LK' c) x) :
    modelYK n w gNE GNE NX TX gE GE NE TE gF GF NF TF gD GD LL gY GY CP LK =
      modelYK n w gNE GNE NX TX gE GE NE TE gF GF NF TF gD GD LL' gY GY CP LK' := by
  unfold modelYK
  rw [allN_congr47 (N := 4) (f := fun c => allN gY fun y => memK (LK c) (conj 64 7 (CP c) (GY y)))
    (g := fun c => allN gY fun y => memK (LK' c) (conj 64 7 (CP c) (GY y)))
    fun c hc => allN_congr47 fun y _ => h c hc _,
    allN_congr47 (N := 4) (f := fun l => allN gD fun k => memK (LL l) (GD k))
    (g := fun l => allN gD fun k => memK (LL' l) (GD k))
    fun l hl => allN_congr47 fun k _ => hL l hl _]

@[expose] noncomputable def subPts47 (m : MD) (k : ModelK) (S : List (List Nat)) (c : Nat) :
    List Nat :=
  runK 64 7 (S.getD c []).length (fun i => kefG m k c ((S.getD c []).getD i 0)) 200

@[expose] noncomputable def subKP47 (k : ModelK) (SK : List (List Nat)) (i : Nat) : List Nat :=
  runK 64 7 (SK.getD i []).length (fun j => k.GK i ((SK.getD i []).getD j 0)) 100

@[expose] noncomputable def runsMS47 (n w : Nat) (m : MD) (k : ModelK) (GY : Nat → Nat)
    (S SK : List (List Nat)) : Bool :=
  CFSG.KLie.CT.andB (allN 4 fun c => subOK47 64 7
      ((m.ke.getD (c / 2) []).length + (m.kf.getD (c % 2) []).length) (kefG m k c) (S.getD c [])
      200 200)
  (CFSG.KLie.CT.andB (allN 4 fun i => subOK47 64 7 (kListG m i).length (k.GK i) (SK.getD i [])
      100 100)
  (CFSG.KLie.CT.andB (Nat.beq (runK 64 7 m.d.length k.GD 100).length 8 &&
    Nat.beq (runK 64 7 m.eb.length k.GEb 100).length 4 &&
    Nat.beq (runK 64 7 m.fb.length k.GFb 100).length 4 &&
    allN 4 (fun i => Nat.beq (subKP47 k SK i).length 24) &&
    allN 4 fun c => Nat.beq (subPts47 m k S c).length 168)
  (modelYK n w m.ne.length k.GNE k.NX k.TX m.eg.length k.GE k.NE k.TE m.fg.length k.GF k.NF k.TF
    m.d.length k.GD (subKP47 k SK) 2 GY k.CP (subPts47 m k S))))

theorem runsModel_of47 {n w : Nat} {m : MD} {k : ModelK} {GY : Nat → Nat}
    {S SK : List (List Nat)} (h : runsMS47 n w m k GY S SK = true) :
    (runsB m k && modelB n w m k GY) = true := by
  unfold runsMS47 at h
  simp only [andB_eq47, Bool.and_eq_true] at h
  obtain ⟨hS, hK, ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  have e : ∀ c < 4, (kefPts m k c).length = (subPts47 m k S c).length ∧
      ∀ x, memK (kefPts m k c) x = memK (subPts47 m k S c) x := fun c hc =>
    runK_sub47 (by decide) (allN_spec hS c hc)
  have eK : ∀ i < 4, (kPts m k i).length = (subKP47 k SK i).length ∧
      ∀ x, memK (kPts m k i) x = memK (subKP47 k SK i) x := fun i hi =>
    runK_sub47 (by decide) (allN_spec hK i hi)
  unfold runsB modelB
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, ?_⟩, ?_⟩, ?_⟩
  · refine (allN_congr47 (N := 4) (f := fun i => Nat.beq (kPts m k i).length 24)
      (g := fun i => Nat.beq (subKP47 k SK i).length 24) fun i hi => ?_).trans h4
    simp only [(eK i hi).1]
  · refine (allN_congr47 (N := 4) (f := fun c => Nat.beq (kefPts m k c).length 168)
      (g := fun c => Nat.beq (subPts47 m k S c).length 168) fun c hc => ?_).trans h5
    simp only [(e c hc).1]
  · exact (modelYK_congr47 (fun i hi => (eK i hi).2) fun c hc => (e c hc).2).trans h6

@[expose] def q47S16 : List (List Nat) := [[5, 11], [0, 5, 11], [0, 5, 11], [0, 5, 11]]

@[expose] def q47S32 : List (List Nat) := [[1, 4, 9], [1, 4, 9], [1, 4, 9], [4, 9]]

@[expose] def q47SK16 : List (List Nat) := [[0, 5], [0, 5], [4, 5], [4, 5]]

@[expose] def q47SK32 : List (List Nat) := [[3, 4], [3, 4], [1, 4], [1, 4]]

theorem kRMS16 : runsMS47 16 5 q47M16 K16 Q47Y.G q47S16 q47SK16 = true := by quickRfl

theorem kRMS32 : runsMS47 32 6 q47M32 K32 Q47Y.G q47S32 q47SK32 = true := by quickRfl

theorem kRM16 : (runsB q47M16 K16 && modelB 16 5 q47M16 K16 Q47Y.G) = true :=
  runsModel_of47 kRMS16

theorem kRM32 : (runsB q47M32 K32 && modelB 32 6 q47M32 K32 Q47Y.G) = true :=
  runsModel_of47 kRMS32

theorem kRuns16 : runsB q47M16 K16 = true := by
  have h := kRM16
  simp only [Bool.and_eq_true] at h
  exact h.1

theorem kRuns32 : runsB q47M32 K32 = true := by
  have h := kRM32
  simp only [Bool.and_eq_true] at h
  exact h.1

theorem kWit : witsK Q47Y.G (PK q47G1 7) (PK q47G2 7) (runK 64 7 3 (PK q47U1Gens 7) 100)
    (runK 64 7 3 (PK q47U2Gens 7) 100) q47Wit = true := by quickRfl

theorem kImg16 : (imgK 16 5 K16.REP K16.PZ q47M16.ne.length K16.GNE K16.GD &&
    imgK 16 5 K16.REP K16.PZ q47M16.eg.length K16.GE K16.GEb &&
    imgK 16 5 K16.REP K16.PZ q47M16.fg.length K16.GF K16.GFb) = true := by quickRfl

theorem kImg32 : (imgK 32 6 K32.REP K32.PZ q47M32.ne.length K32.GNE K32.GD &&
    imgK 32 6 K32.REP K32.PZ q47M32.eg.length K32.GE K32.GEb &&
    imgK 32 6 K32.REP K32.PZ q47M32.fg.length K32.GF K32.GFb) = true := by quickRfl

theorem kModel16 : modelB 16 5 q47M16 K16 Q47Y.G = true := by
  have h := kRM16
  simp only [Bool.and_eq_true] at h
  exact h.2

theorem kModel32 : modelB 32 6 q47M32 K32 Q47Y.G = true := by
  have h := kRM32
  simp only [Bool.and_eq_true] at h
  exact h.2

end CertificateChecks.KernelLC.Q47

end
