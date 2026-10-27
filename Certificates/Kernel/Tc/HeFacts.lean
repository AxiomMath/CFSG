module

public import Certificates.Kernel.Tc.HeQE
public import Certificates.Kernel.Tc.HeW0
public import Certificates.Kernel.Tc.HeW1
public import Certificates.Kernel.Co2Chain.He12635
public import CFSG.Certificates.Kernel.TcFSound
public import CFSG.Certificates.Kernel.HeLoc.TreeSound
public import CFSG.Certificates.Kernel.B3S3KSound
public import CFSG.Certificates.Kernel.Misc.ArrBind
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.ThetaSpor.HeThreeCore

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelTc.He

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Raw.Orb CFSG.KS.Prim CFSG.KS.SporSch CFSG.KC.HeLoc
open CFSG.KC.TcF CFSG.KC.B3S3K CFSG.KC.Misc.ArrEnum
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Mathieu CFSG.Monster.B.Fischer
open CFSG.RankThree.Native CFSG.Certificates.Native CFSG.Sporadic.HeldB
open CFSG.AGLEmbeddingD2.Wilson.ThetaSpor.He CFSG.AGLEmbeddingD2.Wilson.Census219
open CertificateChecks.KernelLC.HeFix CFSG.Sporadic.Schreier
open scoped commutatorElement

@[expose] def wd (k : Nat) : List Int := heTcWs.getD k []

theorem wOK_all : ∀ k < 15, wOK k = true
  | 0, _ => wOK0 | 1, _ => wOK1 | 2, _ => wOK2 | 3, _ => wOK3 | 4, _ => wOK4 | 5, _ => wOK5
  | 6, _ => wOK6 | 7, _ => wOK7 | 8, _ => wOK8 | 9, _ => wOK9 | 10, _ => wOK10 | 11, _ => wOK11
  | 12, _ => wOK12 | 13, _ => wOK13 | 14, _ => wOK14
  | _ + 15, h => absurd h (by omega)

theorem wOK_k {k : Nat} (hk : k < 15) :
    wordEqK 8330 14 (mask 14) (pidn 8330 14) L2 L2I 2 (wd k) (HT k) = true ∧
      invEqK 8330 14 (mask 14) (8330 * 14) (HT k) (HTI k) = true := by
  have h := wOK_all k hk
  unfold wOK at h
  exact (bAnd_iff _ _).1 h

theorem arr {k : Nat} (hk : k < 15) :
    heThreeArr (wd k) = unpack 8330 14 (HT k) ∧ lettersOK 2 (wd k) = true :=
  wordEqK_sound CertificateChecks.KernelCo2Chain.He12635.hS kPL2 (wOK_k hk).1

theorem unpackGet {p x : Nat} (hx : x < 8330) :
    (unpack 8330 14 p)[x]! = pg 14 (mask 14) p x := by
  rw [unpack, getElem!_pos _ x (by simpa using hx), Array.getElem_ofFn]

theorem repF_of_rep {p : Nat} {u : Equiv.Perm (Fin 8330)} (h : Rep 8330 (unpack 8330 14 p) u) :
    RepF 8330 (pg 14 (mask 14) p) u := fun x hx => by
  rw [← unpackGet hx]
  exact h ⟨x, hx⟩

section He


@[expose] noncomputable def gp (k : Nat) : Equiv.Perm (Fin 8330) := heThreeP (wd k)

theorem rep {k : Nat} (hk : k < 15) : Rep 8330 (unpack 8330 14 (HT k)) (gp k) := by
  rw [← (arr hk).1]
  exact rep_heThreeP (arr hk).2

theorem mem {k : Nat} : gp k ∈ heP := heThreeP_mem _

theorem inv {k : Nat} (hk : k < 15) :
    invCand 8330 (unpack 8330 14 (HT k)) = unpack 8330 14 (HTI k) ∧
      isInvA 8330 (unpack 8330 14 (HT k)) (unpack 8330 14 (HTI k)) = true :=
  invEqK_sound (wOK_k hk).2

theorem valid {k : Nat} (hk : k < 15) : validA 8330 (unpack 8330 14 (HT k)) = true := by
  unfold validA
  rw [(inv hk).1]
  exact (inv hk).2

theorem pOf {k : Nat} (hk : k < 15) : permOfArr 8330 (unpack 8330 14 (HT k)) = gp k :=
  CFSG.RankThree.Native.permOfArr_eq_of_rep (rep hk)

theorem repF {k : Nat} (hk : k < 15) : RepF 8330 (t k) (gp k) := repF_of_rep (rep hk)

theorem repFi {k : Nat} (hk : k < 15) : RepF 8330 (ti k) (gp k)⁻¹ := by
  have h := (rep_permOfArr (inv hk).2).2
  rw [pOf hk] at h
  exact repF_of_rep h

theorem bs_lt : ∀ b ∈ bs, b < 8330 := by decide

theorem keys_lt : ∀ p ∈ heBase, p < 8330 := by decide

theorem faithful : BaseFaithful heP bs := by
  intro h hh hfix
  refine CFSG.Sporadic.HeldB.eq_one_of_fix_base hh fun x hx => hfix x ?_
  have : (x : Nat) = 0 ∨ (x : Nat) = 1 ∨ (x : Nat) = 2 ∨ (x : Nat) = 3 ∨ (x : Nat) = 4 := by
    omega
  rcases this with h0 | h0 | h0 | h0 | h0 <;> simp [bs, h0]

theorem hF2 : ∀ x ∈ heP, ∀ y ∈ heP, (x ∈ heP ↔ y ∈ heP) →
    (∀ b (hb : b ∈ bs), (x ⟨b, bs_lt b hb⟩ : Nat) = y ⟨b, bs_lt b hb⟩) → x = y := by
  intro x hx y hy _ h
  have h1 := faithful (y⁻¹ * x) (heP.mul_mem (heP.inv_mem hy) hx) fun z hz => by
    rw [Equiv.Perm.mul_apply, Equiv.Perm.inv_eq_iff_eq]
    exact Fin.ext (h z hz)
  exact (inv_mul_eq_one.1 h1).symm

theorem hmul : ∀ a ∈ heP, ∀ b ∈ heP, (a * b ∈ heP ↔ (a ∈ heP ↔ b ∈ heP)) :=
  fun a ha b hb => iff_of_true (heP.mul_mem ha hb) (iff_of_true ha hb)

theorem q0_iff {gpk : Nat → Equiv.Perm (Fin 8330)} {m : Nat} (h : ∀ k < m, gpk k ∈ heP) :
    ∀ k < m, (gpk k ∈ heP ↔ q0 k = 0) := fun k hk => iff_of_true (h k hk) rfl

theorem q0_lt {m : Nat} : ∀ k < m, q0 k < 2 := fun _ _ => Nat.zero_lt_two

theorem eqA_P {a b : Array Nat} {A B : Equiv.Perm (Fin 8330)} {f g : Nat → Nat}
    (ha : Rep 8330 a A) (hb : Rep 8330 b B) (hf : RepF 8330 f A) (hg : RepF 8330 g B)
    (hA : A ∈ heP) (hB : B ∈ heP) (h : eqOnL bs f g = true) : eqA 8330 a b = true :=
  (eqA_iff ha hb).2 (eq_of_eqOnL faithful hf hg hA hB h)

theorem elT {k : Nat} (hk : k < 15) : ElFI heP (unpack 8330 14 (HT k)) (t k) (ti k) := by
  refine ⟨⟨valid hk, ?_, ?_⟩, ?_⟩ <;> rw [pOf hk]
  · exact repF hk
  · exact mem
  · exact repFi hk

theorem elF_id : ElFI heP (idA 8330) (fun x => x) (fun x => x) := by
  have h1 : permOfArr 8330 (idA 8330) = 1 := CFSG.RankThree.Native.permOfArr_eq_of_rep rep_idA
  refine ⟨⟨CFSG.RankThree.Native.F2.validA_of_rep rep_idA, ?_, ?_⟩, ?_⟩
  · rw [h1]
    exact RepF.one
  · rw [h1]
    exact heP.one_mem
  · rw [h1, inv_one]
    exact RepF.one

@[expose] noncomputable def gpq (i : Nat) : Equiv.Perm (Fin 8330) :=
  ⁅gp (2 * i), gp (1 + 2 * i)⁆

@[expose] noncomputable def gpk (l : Nat) : Equiv.Perm (Fin 8330) :=
  if l = 2 then gp 14 else gp (4 + l)

@[expose] noncomputable def gpy (k : Nat) : Equiv.Perm (Fin 8330) := gp (12 + k)

theorem word_get {i : Nat} (hi : i < 15) : heThreeArr (wd i) = unpack 8330 14 (HT i) := (arr hi).1

theorem wU0 : heThreeArr heTcU0 = unpack 8330 14 (HT 0) := word_get (i := 0) (by norm_num)
theorem wV0 : heThreeArr heTcV0 = unpack 8330 14 (HT 1) := word_get (i := 1) (by norm_num)
theorem wU1 : heThreeArr heTcU1 = unpack 8330 14 (HT 2) := word_get (i := 2) (by norm_num)
theorem wV1 : heThreeArr heTcV1 = unpack 8330 14 (HT 3) := word_get (i := 3) (by norm_num)
theorem wK0 : heThreeArr heTcK0 = unpack 8330 14 (HT 4) := word_get (i := 4) (by norm_num)
theorem wK1 : heThreeArr heTcK1 = unpack 8330 14 (HT 5) := word_get (i := 5) (by norm_num)
theorem wR1 : heThreeArr heTcR1 = unpack 8330 14 (HT 6) := word_get (i := 6) (by norm_num)
theorem wR2 : heThreeArr heTcR2 = unpack 8330 14 (HT 7) := word_get (i := 7) (by norm_num)
theorem wR3 : heThreeArr heTcR3 = unpack 8330 14 (HT 8) := word_get (i := 8) (by norm_num)
theorem wR4 : heThreeArr heTcR4 = unpack 8330 14 (HT 9) := word_get (i := 9) (by norm_num)
theorem wR5 : heThreeArr heTcR5 = unpack 8330 14 (HT 10) := word_get (i := 10) (by norm_num)
theorem wR6 : heThreeArr heTcR6 = unpack 8330 14 (HT 11) := word_get (i := 11) (by norm_num)
theorem wS1 : heThreeArr heTcS1 = unpack 8330 14 (HT 12) := word_get (i := 12) (by norm_num)
theorem wS2 : heThreeArr heTcS2 = unpack 8330 14 (HT 13) := word_get (i := 13) (by norm_num)
theorem wB : heThreeBA = unpack 8330 14 (HT 14) := word_get (i := 14) (by norm_num)

theorem gQ_get {i : Nat} (hi : i < 2) : heTcD.gQ[i]! =
    commutatorA 8330 (unpack 8330 14 (HT (2 * i))) (unpack 8330 14 (HT (1 + 2 * i))) := by
  interval_cases i
  · have e : heTcD.gQ[0]! = commutatorA 8330 (heThreeArr heTcU0) (heThreeArr heTcV0) := by
      simp [heTcD]
    rw [e, wU0, wV0]
  · have e : heTcD.gQ[1]! = commutatorA 8330 (heThreeArr heTcU1) (heThreeArr heTcV1) := by
      simp [heTcD]
    rw [e, wU1, wV1]

theorem gK_get {l : Nat} (hl : l < 3) :
    heTcD.gK[l]! = if l = 2 then unpack 8330 14 (HT 14) else unpack 8330 14 (HT (4 + l)) := by
  interval_cases l
  · have e : heTcD.gK[0]! = heThreeArr heTcK0 := by simp [heTcD]
    rw [e, wK0, if_neg (by norm_num)]
  · have e : heTcD.gK[1]! = heThreeArr heTcK1 := by simp [heTcD]
    rw [e, wK1, if_neg (by norm_num)]
  · have e : heTcD.gK[2]! = heThreeBA := by simp [heTcD]
    rw [e, wB, if_pos rfl]

theorem gY_get {k : Nat} (hk : k < 2) : heSylA[k]! = unpack 8330 14 (HT (12 + k)) := by
  interval_cases k
  · have e : heSylA[0]! = heThreeArr heTcS1 := by simp [heSylA]
    rw [e, wS1]
  · have e : heSylA[1]! = heThreeArr heTcS2 := by simp [heSylA]
    rw [e, wS2]

theorem repQ {i : Nat} (hi : i < 2) : Rep 8330 heTcD.gQ[i]! (gpq i) := by
  rw [gQ_get hi]
  have h := rep_commutatorA (valid (k := 2 * i) (by omega)) (valid (k := 1 + 2 * i) (by omega))
  rwa [pOf (by omega), pOf (by omega)] at h

theorem hgsQ : ∀ k < 2, Rep 8330 heTcD.gQ[k]! (gpq k) := fun k hk => repQ hk

theorem hgsK : ∀ k < 3, Rep 8330 heTcD.gK[k]! (gpk k) := fun k hk => by
  rw [gK_get hk, gpk]
  split
  · exact rep (by norm_num)
  · exact rep (by omega)

theorem hgsY : ∀ k < 2, Rep 8330 heSylA[k]! (gpy k) := fun k hk => by
  rw [gY_get hk]
  exact rep (by omega)

theorem hgQ : ∀ k < 2, RepF 8330 (gq k) (gpq k) := fun k hk => by
  have h := (repF (k := 2 * k) (by omega)).comp ((repF (k := 1 + 2 * k) (by omega)).comp
    ((repFi (k := 2 * k) (by omega)).comp (repFi (k := 1 + 2 * k) (by omega))))
  refine h.congr ?_
  rw [gpq, commutatorElement_def, mul_assoc, mul_assoc, Nat.add_comm 1 (2 * k)]

theorem hgK : ∀ k < 3, RepF 8330 (gk k) (gpk k) := fun k hk => by
  interval_cases k
  · rw [gpk, if_neg (by norm_num)]
    exact repF (k := 4) (by norm_num)
  · rw [gpk, if_neg (by norm_num)]
    exact repF (k := 5) (by norm_num)
  · rw [gpk, if_pos rfl]
    exact repF (k := 14) (by norm_num)

theorem hgY : ∀ k < 2, RepF 8330 (gy k) (gpy k) := fun k hk => repF (k := 12 + k) (by omega)

theorem memQ : ∀ k < 2, gpq k ∈ heP := fun k _ => by
  rw [gpq, commutatorElement_def]
  exact heP.mul_mem (heP.mul_mem (heP.mul_mem mem mem) (heP.inv_mem mem)) (heP.inv_mem mem)

theorem memK : ∀ k < 3, gpk k ∈ heP := fun k _ => by
  unfold gpk
  split <;> exact mem

theorem memY : ∀ k < 2, gpy k ∈ heP := fun _ _ => mem

theorem treeQ : TreeOK 2 7560 TQ.P TQ.L := treeOK_of fun i hi h0 => by
  have h := Orb.allN_iff.1 kTreeQ i hi
  rwa [CFSG.KC.HeLoc.beq_zero_false h0] at h

theorem treeK : TreeOK 3 1080 TK.P TK.L := treeOK_of fun i hi h0 => by
  have h := Orb.allN_iff.1 kTreeK i hi
  rwa [CFSG.KC.HeLoc.beq_zero_false h0] at h

theorem treeY : TreeOK 2 27 TY.P TY.L := treeOK_of fun i hi h0 => by
  have h := Orb.allN_iff.1 kTreeY i hi
  rwa [CFSG.KC.HeLoc.beq_zero_false h0] at h

theorem edgeQB_all : ∀ j < 18, edgeQB j = true
  | 0, _ => edgeQB0 | 1, _ => edgeQB1 | 2, _ => edgeQB2 | 3, _ => edgeQB3 | 4, _ => edgeQB4
  | 5, _ => edgeQB5 | 6, _ => edgeQB6 | 7, _ => edgeQB7 | 8, _ => edgeQB8 | 9, _ => edgeQB9
  | 10, _ => edgeQB10 | 11, _ => edgeQB11 | 12, _ => edgeQB12 | 13, _ => edgeQB13
  | 14, _ => edgeQB14 | 15, _ => edgeQB15 | 16, _ => edgeQB16 | 17, _ => edgeQB17
  | _ + 18, h => absurd h (by omega)

theorem sortQB_all : ∀ j < 18, sortQB j = true
  | 0, _ => sortQB0 | 1, _ => sortQB1 | 2, _ => sortQB2 | 3, _ => sortQB3 | 4, _ => sortQB4
  | 5, _ => sortQB5 | 6, _ => sortQB6 | 7, _ => sortQB7 | 8, _ => sortQB8 | 9, _ => sortQB9
  | 10, _ => sortQB10 | 11, _ => sortQB11 | 12, _ => sortQB12 | 13, _ => sortQB13
  | 14, _ => sortQB14 | 15, _ => sortQB15 | 16, _ => sortQB16 | 17, _ => sortQB17
  | _ + 18, h => absurd h (by omega)

theorem kEdgeQ : ∀ i < 7560, edgeAtK gq q0 TQ.P TQ.L EQ 7560 7560 2 bs i = true := by
  intro i hi
  have h := Orb.allN_iff.1 (edgeQB_all (i / 420) (by omega)) (i % 420) (Nat.mod_lt _ (by norm_num))
  have e : Nat.add (Nat.mul 420 (i / 420)) (i % 420) = i := Nat.div_add_mod i 420
  rwa [e] at h

theorem kSortQ : ∀ i < 7560, sortAtK kq TQ.SK TQ.SKI 7560 i = true := by
  intro i hi
  have h := Orb.allN_iff.1 (sortQB_all (i / 420) (by omega)) (i % 420) (Nat.mod_lt _ (by norm_num))
  have e : Nat.add (Nat.mul 420 (i / 420)) (i % 420) = i := Nat.div_add_mod i 420
  rwa [e] at h

theorem edgesQ : ∀ i < 7560, ∀ k < 2, EQ i k < 7560 ∧
    treeArr 8330 heTcD.gQ TQ.P TQ.L (EQ i k) =
      compA 8330 heTcD.gQ[k]! (treeArr 8330 heTcD.gQ TQ.P TQ.L i) :=
  edges_of_edgeAtK treeQ hgQ hgsQ hmul memQ (q0_iff memQ) q0_lt bs_lt hF2 kEdgeQ

theorem edgesK : ∀ i < 1080, ∀ k < 3, EK i k < 1080 ∧
    treeArr 8330 heTcD.gK TK.P TK.L (EK i k) =
      compA 8330 heTcD.gK[k]! (treeArr 8330 heTcD.gK TK.P TK.L i) :=
  edges_of_edgeAtK treeK hgK hgsK hmul memK (q0_iff memK) q0_lt bs_lt hF2
    fun i hi => Orb.allN_iff.1 kEdgeK i hi

theorem edgesY : ∀ i < 27, ∀ k < 2, EY i k < 27 ∧
    treeArr 8330 heSylA TY.P TY.L (EY i k) =
      compA 8330 heSylA[k]! (treeArr 8330 heSylA TY.P TY.L i) :=
  edges_of_edgeAtK treeY hgY hgsY hmul memY (q0_iff memY) q0_lt bs_lt hF2
    fun i hi => Orb.allN_iff.1 kEdgeY i hi

theorem keyQ : ∀ a < 7560, ∀ b < 7560, keyA 8330 heBase (treeArr 8330 heTcD.gQ TQ.P TQ.L a) =
    keyA 8330 heBase (treeArr 8330 heTcD.gQ TQ.P TQ.L b) → a = b := by
  have hk := keys_inj_of_sortAtK (key := kq) kSortQ
  intro a ha b hb e
  rw [keyA_treeArr treeQ hgQ hgsQ keys_lt ha, keyA_treeArr treeQ hgQ hgsQ keys_lt hb] at e
  exact hk a ha b hb e

theorem keyK : ∀ a < 1080, ∀ b < 1080, keyA 8330 heBase (treeArr 8330 heTcD.gK TK.P TK.L a) =
    keyA 8330 heBase (treeArr 8330 heTcD.gK TK.P TK.L b) → a = b := by
  have hk := keys_inj_of_sortAtK (key := kk) fun j hj => Orb.allN_iff.1 kSortK j hj
  intro a ha b hb e
  rw [keyA_treeArr treeK hgK hgsK keys_lt ha, keyA_treeArr treeK hgK hgsK keys_lt hb] at e
  exact hk a ha b hb e

theorem keyY : ∀ a < 27, ∀ b < 27, keyA 8330 heBase (treeArr 8330 heSylA TY.P TY.L a) =
    keyA 8330 heBase (treeArr 8330 heSylA TY.P TY.L b) → a = b := by
  have hk := keys_inj_of_sortAtK (key := ky) fun j hj => Orb.allN_iff.1 kSortY j hj
  intro a ha b hb e
  rw [keyA_treeArr treeY hgY hgsY keys_lt ha, keyA_treeArr treeY hgY hgsY keys_lt hb] at e
  exact hk a ha b hb e

theorem ptsQ : (heTcCQ ()).pts =
    Array.ofFn (n := 7560) fun i => treeArr 8330 heTcD.gQ TQ.P TQ.L i.val :=
  enumBfs_tree treeQ hgsQ (by simp [heTcD]) (by norm_num) (by norm_num) keyQ edgesQ kReplayQ

theorem ptsK : (heTcCK ()).pts =
    Array.ofFn (n := 1080) fun i => treeArr 8330 heTcD.gK TK.P TK.L i.val :=
  enumBfs_tree treeK hgsK (by simp [heTcD]) (by norm_num) (by norm_num) keyK edgesK kReplayK

theorem ptsY : (heTcCY ()).pts =
    Array.ofFn (n := 27) fun i => treeArr 8330 heSylA TY.P TY.L i.val :=
  enumBfs_tree treeY hgsY (by simp [heSylA]) (by norm_num) (by norm_num) keyY edgesY kReplayY

theorem enumQ : enumOK 8330 heTcD.gQ heBase (heTcCQ ()) = true :=
  enumOK_tree treeQ hgsQ (by simp [heTcD]) (by norm_num) (by norm_num) keyQ edgesQ

theorem enumK : enumOK 8330 heTcD.gK heBase (heTcCK ()) = true :=
  enumOK_tree treeK hgsK (by simp [heTcD]) (by norm_num) (by norm_num) keyK edgesK

theorem enumY : enumOK 8330 heSylA heBase (heTcCY ()) = true :=
  enumOK_tree treeY hgsY (by simp [heSylA]) (by norm_num) (by norm_num) keyY edgesY

theorem sizeQ : (heTcCQ ()).pts.size = 7560 := by rw [ptsQ, Array.size_ofFn]

theorem sizeK : (heTcCK ()).pts.size = 1080 := by rw [ptsK, Array.size_ofFn]

theorem sizeY : (heTcCY ()).pts.size = 27 := by rw [ptsY, Array.size_ofFn]

theorem el_tree {ng N : Nat} {gs : Array (Array Nat)} {gpt : Nat → Equiv.Perm (Fin 8330)}
    {g : Nat → Nat → Nat} {P Lb : Nat → Nat} (ht : TreeOK ng N P Lb)
    (hg : ∀ k < ng, RepF 8330 (g k) (gpt k)) (hgs : ∀ k < ng, Rep 8330 gs[k]! (gpt k))
    (hm : ∀ k < ng, gpt k ∈ heP) {i : Nat} (hi : i < N) :
    ElF heP (treeArr 8330 gs P Lb i) (trV g P Lb N i) := by
  have hr := rep_treeArr ht hgs i hi
  unfold ElF
  rw [CFSG.RankThree.Native.permOfArr_eq_of_rep hr]
  exact ⟨CFSG.RankThree.Native.F2.validA_of_rep hr, repF_trV ht hg N i hi.le hi,
    (trQ_spec ht hmul hm (q0_iff hm) q0_lt N i hi.le hi).1⟩

theorem elQ : ∀ i < 7560, ElF heP (heTcCQ ()).pts[i]! (tq i) := fun i hi => by
  rw [ptsQ, getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]
  exact el_tree treeQ hgQ hgsQ memQ hi

theorem elK : ∀ i < 1080, ElF heP (heTcCK ()).pts[i]! (tk i) := fun i hi => by
  rw [ptsK, getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]
  exact el_tree treeK hgK hgsK memK hi

theorem bind_of {a : Array (Array Nat)} {m n w : Nat} {F : Nat → Nat} {g : Nat}
    (hs : a.size = m) (hg : g = m) (h : ∀ j < m, arrBind a[j]! n w (F j) = true) :
    BindA n w a g F := by
  subst hg
  exact ⟨hs, fun j hj => arrBind_sound (h j hj)⟩

theorem perm_of {m n w g : Nat} {F : Nat → Nat} (hg : g = m)
    (h : allN m (fun k => permB n w (F k)) = true) : ∀ k < g, permB n w (F k) = true := by
  subst hg
  exact allN_spec h

theorem hkeys7 : keys7.toList = List.range 7 := by decide +kernel

theorem hps7 : ∀ p ∈ keys7.toList, p < 7 := by
  rw [hkeys7]
  intro p hp
  exact List.mem_range.1 hp

theorem eS : enumOK 7 heTcD.sig (List.range 7) (heTcCS ()) = true ∧
    (heTcCS ()).pts.size = ES.N := by
  have h := enum_of (fuel := 4000)
    (bind_of (by decide +kernel) (Nat.eq_of_beq_eq_true nS) bS)
    (perm_of (Nat.eq_of_beq_eq_true nS) pS) ES.ok hps7 ES.keys (by decide +kernel)
  rw [hkeys7] at h
  exact ⟨h.1, h.2.1⟩

theorem reps_get {j : Nat} (h0 : 0 < j) (hj : j < 7) :
    heTcD.reps[j]! = unpack 8330 14 (HT (5 + j)) := by
  interval_cases j
  · have e : heTcD.reps[1]! = heThreeArr heTcR1 := by simp [heTcD]
    rw [e, wR1]
  · have e : heTcD.reps[2]! = heThreeArr heTcR2 := by simp [heTcD]
    rw [e, wR2]
  · have e : heTcD.reps[3]! = heThreeArr heTcR3 := by simp [heTcD]
    rw [e, wR3]
  · have e : heTcD.reps[4]! = heThreeArr heTcR4 := by simp [heTcD]
    rw [e, wR4]
  · have e : heTcD.reps[5]! = heThreeArr heTcR5 := by simp [heTcD]
    rw [e, wR5]
  · have e : heTcD.reps[6]! = heThreeArr heTcR6 := by simp [heTcD]
    rw [e, wR6]

theorem cu_get {i : Nat} (hi : i < 2) : heTcD.cu[i]! = unpack 8330 14 (HT (2 * i)) := by
  interval_cases i
  · have e : heTcD.cu[0]! = heThreeArr heTcU0 := by simp [heTcD]
    rw [e, wU0]
  · have e : heTcD.cu[1]! = heThreeArr heTcU1 := by simp [heTcD]
    rw [e, wU1]

theorem cv_get {i : Nat} (hi : i < 2) : heTcD.cv[i]! = unpack 8330 14 (HT (1 + 2 * i)) := by
  interval_cases i
  · have e : heTcD.cv[0]! = heThreeArr heTcV0 := by simp [heTcD]
    rw [e, wV0]
  · have e : heTcD.cv[1]! = heThreeArr heTcV1 := by simp [heTcD]
    rw [e, wV1]

theorem elX : ElF heP heThreeBA (t 14) := by
  rw [wB]
  exact (elT (k := 14) (by norm_num)).1

theorem tc_ok : tcOK 8330 7 heBase heThreeBA heTcD (heTcCQ ()) (heTcCK ()) (heTcCS ()) = true := by
  refine tcOK_of_F (bs := bs) bs_lt faithful elX (by simp [heTcD]) (fun i hi => ?_)
    (by simp [heTcD]) (fun i hi => ?_) (by simp [heTcD]) (fun i hi => ?_) (by simp [heTcD])
    (fun l hl => ?_) (by simp [heTcD]) (fun j hj => ?_) (by simp [heTcD]) (fun i _ j _ => rfl)
    enumQ sizeQ elQ enumK sizeK elK eS.1 eS.2 rest
  · have hr := repQ hi
    refine ⟨CFSG.RankThree.Native.F2.validA_of_rep hr, ?_, ?_⟩ <;>
      rw [CFSG.RankThree.Native.permOfArr_eq_of_rep hr]
    · exact hgQ i hi
    · exact memQ i hi
  · have hi2 : i < 2 := by simpa [heTcD] using hi
    rw [cu_get hi2]
    exact elT (by omega)
  · have hi2 : i < 2 := by simpa [heTcD] using hi
    rw [cv_get hi2]
    exact elT (by omega)
  · rw [gK_get hl]
    interval_cases l
    · rw [if_neg (by norm_num)]
      exact (elT (k := 4) (by norm_num)).1
    · rw [if_neg (by norm_num)]
      exact (elT (k := 5) (by norm_num)).1
    · rw [if_pos rfl]
      exact (elT (k := 14) (by norm_num)).1
  · interval_cases j
    · exact elF_id
    all_goals
      rw [reps_get (by norm_num) (by norm_num)]
      exact elT (by norm_num)

theorem cube_ok : allLt (heTcCY ()).pts.size
    (fun k => eqA 8330 (powArr 8330 (heTcCY ()).pts[k]! 3) (idA 8330)) = true := by
  rw [allLt_iff, sizeY]
  intro k hk
  rw [ptsY, getElem!_pos _ k (by simpa using hk), Array.getElem_ofFn]
  have hr := rep_treeArr treeY hgsY k hk
  have hf := repF_trV treeY hgY 27 k hk.le hk
  have hm := (trQ_spec treeY hmul memY (q0_iff memY) q0_lt 27 k hk.le hk).1
  exact eqA_P (rep_powArr hr 3) rep_idA (RepF.powF hf 3) RepF.one (heP.pow_mem hm 3) heP.one_mem
    (Orb.allN_iff.1 cubeY k hk)

theorem heTc_ok : heTcOK () = true := by
  have hl : ∀ k < 15, lettersOK 2 (wd k) = true := fun k hk => (arr hk).2
  unfold heTcOK
  rw [tc_ok, enumY, cube_ok, sizeY]
  have h0 : lettersOK 2 heTcU0 = true := hl 0 (by norm_num)
  have h1 : lettersOK 2 heTcV0 = true := hl 1 (by norm_num)
  have h2 : lettersOK 2 heTcU1 = true := hl 2 (by norm_num)
  have h3 : lettersOK 2 heTcV1 = true := hl 3 (by norm_num)
  have h4 : lettersOK 2 heTcK0 = true := hl 4 (by norm_num)
  have h5 : lettersOK 2 heTcK1 = true := hl 5 (by norm_num)
  have h6 : lettersOK 2 heTcR1 = true := hl 6 (by norm_num)
  have h7 : lettersOK 2 heTcR2 = true := hl 7 (by norm_num)
  have h8 : lettersOK 2 heTcR3 = true := hl 8 (by norm_num)
  have h9 : lettersOK 2 heTcR4 = true := hl 9 (by norm_num)
  have h10 : lettersOK 2 heTcR5 = true := hl 10 (by norm_num)
  have h11 : lettersOK 2 heTcR6 = true := hl 11 (by norm_num)
  have h12 : lettersOK 2 heTcS1 = true := hl 12 (by norm_num)
  have h13 : lettersOK 2 heTcS2 = true := hl 13 (by norm_num)
  rw [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13]
  rfl

end He

end CertificateChecks.KernelTc.He

end
