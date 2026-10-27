
module

public import Certificates.Kernel.Tc.RuK
public import Certificates.Kernel.Tc.RuSift
public import Certificates.Kernel.SporSch.Ru.JFacts
public import CFSG.Certificates.Kernel.TcFSound
public import CFSG.Certificates.Kernel.HeLoc.TreeSound
public import CFSG.Certificates.Kernel.Misc.HexFlatSound
public import CFSG.Certificates.Kernel.B3S3KSound
public import CFSG.Certificates.Kernel.Misc.ArrBind
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.ThetaSpor.RuThreeBase
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.RuSzCent

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelTc.Ru

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Raw.Orb CFSG.KS.Prim CFSG.KS.SporSch CFSG.KC.HeLoc
open CFSG.KC.TcF CFSG.KC.B3S3K CFSG.KC.Misc.ArrEnum CFSG.KC.Misc.HexFlat
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Mathieu CFSG.Monster.B.Fischer
open CFSG.RankThree.Native CFSG.Sporadic.RuSchreier CFSG.Sporadic.Schreier CFSG.Certificates.Native
open CFSG.AGLEmbeddingD2.Wilson.ThetaSpor CFSG.AGLEmbeddingD2.Wilson.Census219
open CertificateChecks.KernelSporSch

theorem unpackGet {p x : Nat} (hx : x < 4060) :
    (unpack 4060 12 p)[x]! = pg 12 (mask 12) p x := by
  rw [unpack, getElem!_pos _ x (by simpa using hx), Array.getElem_ofFn]

theorem repF_of_rep {p : Nat} {u : Equiv.Perm (Fin 4060)} (h : Rep 4060 (unpack 4060 12 p) u) :
    RepF 4060 (pg 12 (mask 12) p) u := fun x hx => by
  rw [← unpackGet hx]
  exact h ⟨x, hx⟩

theorem arr3 {k : Nat} (hk : k < 31) : ruArr3 k = unpack 4060 12 (R3.F k) := by
  rw [ruArr3, R3.eq]
  exact hexTable3_sound R3.all k hk

theorem arrT {k : Nat} (hk : k < 13) : ruTcArr k = unpack 4060 12 (RT.F k) := by
  rw [ruTcArr, RT.eq]
  exact hexTable3_sound RT.all k hk

theorem ok3_k {k : Nat} (hk : k < 3) :
    permOK 4060 12 (mask 12) (4060 * 12) (R3.F k) (I3 k) = true ∧
      allN 4060 (fun i => Nat.blt (pg 12 (mask 12) (R3.F k) i) 4060) = true := by
  have h := Orb.allN_iff.1 kOk3 k hk
  unfold ok3 at h
  exact (bAnd_iff _ _).1 h

theorem okT_k {k : Nat} (hk : k < 13) :
    permOK 4060 12 (mask 12) (4060 * 12) (RT.F k) (IT k) = true ∧
      allN 4060 (fun i => Nat.blt (pg 12 (mask 12) (RT.F k) i) 4060) = true := by
  have h := Orb.allN_iff.1 kOkT k hk
  unfold okT at h
  exact (bAnd_iff _ _).1 h

theorem hi_of_permOK {P R : Nat} (h : permOK 4060 12 (mask 12) (4060 * 12) P R = true) :
    Nat.shiftRight P (4060 * 12) = 0 := by
  unfold permOK at h
  exact Nat.eq_of_beq_eq_true ((bAnd_iff _ _).1 h).1

@[expose] noncomputable def gp3 (k : Nat) : Equiv.Perm (Fin 4060) :=
  permOfArr 4060 (unpack 4060 12 (R3.F k))

@[expose] noncomputable def gpT (k : Nat) : Equiv.Perm (Fin 4060) :=
  permOfArr 4060 (unpack 4060 12 (RT.F k))

theorem inv3 {k : Nat} (hk : k < 3) :
    invCand 4060 (unpack 4060 12 (R3.F k)) = unpack 4060 12 (I3 k) ∧
      isInvA 4060 (unpack 4060 12 (R3.F k)) (unpack 4060 12 (I3 k)) = true :=
  invEqK_sound (ok3_k hk).1

theorem invT {k : Nat} (hk : k < 13) :
    invCand 4060 (unpack 4060 12 (RT.F k)) = unpack 4060 12 (IT k) ∧
      isInvA 4060 (unpack 4060 12 (RT.F k)) (unpack 4060 12 (IT k)) = true :=
  invEqK_sound (okT_k hk).1

theorem valid3 {k : Nat} (hk : k < 3) : validA 4060 (unpack 4060 12 (R3.F k)) = true := by
  unfold validA
  rw [(inv3 hk).1]
  exact (inv3 hk).2

theorem validT {k : Nat} (hk : k < 13) : validA 4060 (unpack 4060 12 (RT.F k)) = true := by
  unfold validA
  rw [(invT hk).1]
  exact (invT hk).2

theorem rep3 {k : Nat} (hk : k < 3) : Rep 4060 (unpack 4060 12 (R3.F k)) (gp3 k) :=
  (rep_permOfArr (inv3 hk).2).1

theorem repT {k : Nat} (hk : k < 13) : Rep 4060 (unpack 4060 12 (RT.F k)) (gpT k) :=
  (rep_permOfArr (invT hk).2).1

theorem repF3 {k : Nat} (hk : k < 3) : RepF 4060 (t3 k) (gp3 k) := repF_of_rep (rep3 hk)

theorem repFT {k : Nat} (hk : k < 13) : RepF 4060 (tT k) (gpT k) := repF_of_rep (repT hk)

theorem repF3i {k : Nat} (hk : k < 3) : RepF 4060 (i3 k) (gp3 k)⁻¹ :=
  repF_of_rep (rep_permOfArr (inv3 hk).2).2

theorem repFTi {k : Nat} (hk : k < 13) : RepF 4060 (iT k) (gpT k)⁻¹ :=
  repF_of_rep (rep_permOfArr (invT hk).2).2

theorem sift3 {k : Nat} (hk : k < 3) :
    siftA 4060 (rawLevels 4060 (ruField4060 3) (ruBaseArr 4060 ruJoinBase))
      (ruBaseArr 4060 ruJoinBase) 0 (unpack 4060 12 (R3.F k)) = true :=
  siftK_soundR RuJ.bindsJ RuJ.permJ RuJS.hl rfl (hi_of_permOK (ok3_k hk).1) (ok3_k hk).2
    (Orb.allN_iff.1 kSift3 k hk)

theorem siftT {k : Nat} (hk : k < 13) :
    siftA 4060 (rawLevels 4060 (ruField4060 3) (ruBaseArr 4060 ruJoinBase))
      (ruBaseArr 4060 ruJoinBase) 0 (unpack 4060 12 (RT.F k)) = true :=
  siftK_soundR RuJ.bindsJ RuJ.permJ RuJS.hl rfl (hi_of_permOK (okT_k hk).1) (okT_k hk).2
    (Orb.allN_iff.1 kSiftT k hk)

section Ru

theorem mem3 {k : Nat} (hk : k < 3) : gp3 k ∈ ruP := mem_ruP_of_sift (rep3 hk) (sift3 hk)

theorem memT {k : Nat} (hk : k < 13) : gpT k ∈ ruP := mem_ruP_of_sift (repT hk) (siftT hk)

theorem bs_lt : ∀ b ∈ bs, b < 4060 := by decide

theorem keys_lt : ∀ p ∈ ruKeys, p < 4060 := by decide

theorem faithful : BaseFaithful ruP bs := by
  intro h hh hfix
  refine CFSG.EvenSporadicStandard.Induction.RuSz.eq_one_of_fix_base hh fun x hx => hfix x ?_
  have : (x : Nat) = 0 ∨ (x : Nat) = 1 ∨ (x : Nat) = 2 ∨ (x : Nat) = 3 := by omega
  rcases this with h0 | h0 | h0 | h0 <;> simp [bs, h0]

theorem hF2 : ∀ x ∈ ruP, ∀ y ∈ ruP, (x ∈ ruP ↔ y ∈ ruP) →
    (∀ b (hb : b ∈ bs), (x ⟨b, bs_lt b hb⟩ : Nat) = y ⟨b, bs_lt b hb⟩) → x = y := by
  intro x hx y hy _ h
  have h1 := faithful (y⁻¹ * x) (ruP.mul_mem (ruP.inv_mem hy) hx) fun z hz => by
    rw [Equiv.Perm.mul_apply, Equiv.Perm.inv_eq_iff_eq]
    exact Fin.ext (h z hz)
  exact (inv_mul_eq_one.1 h1).symm

theorem hmul : ∀ a ∈ ruP, ∀ b ∈ ruP, (a * b ∈ ruP ↔ (a ∈ ruP ↔ b ∈ ruP)) :=
  fun a ha b hb => iff_of_true (ruP.mul_mem ha hb) (iff_of_true ha hb)

theorem q0_iff {gpk : Nat → Equiv.Perm (Fin 4060)} {m : Nat} (h : ∀ k < m, gpk k ∈ ruP) :
    ∀ k < m, (gpk k ∈ ruP ↔ q0 k = 0) := fun k hk => iff_of_true (h k hk) rfl

theorem q0_lt {m : Nat} : ∀ k < m, q0 k < 2 := fun _ _ => Nat.zero_lt_two

theorem elF3 {k : Nat} (hk : k < 3) : ElFI ruP (unpack 4060 12 (R3.F k)) (t3 k) (i3 k) :=
  ⟨⟨valid3 hk, repF3 hk, mem3 hk⟩, repF3i hk⟩

theorem elFT {k : Nat} (hk : k < 13) : ElFI ruP (unpack 4060 12 (RT.F k)) (tT k) (iT k) :=
  ⟨⟨validT hk, repFT hk, memT hk⟩, repFTi hk⟩

theorem elF_id : ElFI ruP (idA 4060) (fun x => x) (fun x => x) := by
  have h1 : permOfArr 4060 (idA 4060) = 1 := CFSG.RankThree.Native.permOfArr_eq_of_rep rep_idA
  refine ⟨⟨CFSG.RankThree.Native.F2.validA_of_rep rep_idA, ?_, ?_⟩, ?_⟩
  · rw [h1]
    exact RepF.one
  · rw [h1]
    exact ruP.one_mem
  · rw [h1, inv_one]
    exact RepF.one

theorem any_of_memF {c : ArrCert} {N : Nat} {t : Nat → Nat → Nat} {a : Array Nat}
    {A : Equiv.Perm (Fin 4060)} {f : Nat → Nat} (hN : c.pts.size = N)
    (hp : ∀ i < N, ElF ruP c.pts[i]! (t i)) (ha : Rep 4060 a A) (hA : A ∈ ruP)
    (hf : RepF 4060 f A) (h : memF bs N t f = true) : c.pts.toList.any (eqA 4060 a) = true := by
  unfold memF at h
  cases hall : allN N fun i => bIf(eqOnL bs (t i) f, false, true)
  · have hex : ∃ i < N, eqOnL bs (t i) f = true := by
      by_contra hne
      have : allN N (fun i => bIf(eqOnL bs (t i) f, false, true)) = true :=
        Orb.allN_iff.2 fun i hi => by
          have e : eqOnL bs (t i) f = false := by
            cases e' : eqOnL bs (t i) f
            · rfl
            · exact absurd ⟨i, hi, e'⟩ hne
          rw [e]
      rw [hall] at this
      exact Bool.false_ne_true this
    obtain ⟨i, hi, he⟩ := hex
    obtain ⟨hv, hr, hm⟩ := hp i hi
    have hpe := eq_of_eqOnL faithful hr hf hm hA he
    rw [List.any_eq_true]
    refine ⟨c.pts[i]!, ?_, ?_⟩
    · rw [getElem!_pos c.pts i (by omega)]
      exact Array.getElem_mem_toList _
    · rw [eqA_iff ha (rep_of_validA hv), hpe]
  · rw [hall] at h
    exact absurd h Bool.false_ne_true

@[expose] noncomputable def gpq (k : Nat) : Equiv.Perm (Fin 4060) := gpT k
@[expose] noncomputable def gpk (k : Nat) : Equiv.Perm (Fin 4060) :=
  if k = 2 then gp3 0 else gpT (6 + k)
@[expose] noncomputable def gpc (k : Nat) : Equiv.Perm (Fin 4060) := gp3 (1 + k)

theorem gQ_get {k : Nat} (hk : k < 2) : ruTcD.gQ[k]! = unpack 4060 12 (RT.F k) := by
  rw [← arrT (by omega)]
  interval_cases k <;> rfl

theorem gK_get {k : Nat} (hk : k < 3) :
    ruTcD.gK[k]! = if k = 2 then unpack 4060 12 (R3.F 0) else unpack 4060 12 (RT.F (6 + k)) := by
  interval_cases k
  · rw [← arrT (by omega)]
    rfl
  · rw [← arrT (by omega)]
    rfl
  · rw [← arr3 (by omega)]
    rfl

theorem gC_get {k : Nat} (hk : k < 2) : ruGs[k]! = unpack 4060 12 (R3.F (1 + k)) := by
  rw [← arr3 (by omega)]
  interval_cases k <;> rfl

theorem hgsQ : ∀ k < 2, Rep 4060 ruTcD.gQ[k]! (gpq k) := fun k hk => by
  rw [gQ_get hk]
  exact repT (by omega)

theorem hgsK : ∀ k < 3, Rep 4060 ruTcD.gK[k]! (gpk k) := fun k hk => by
  rw [gK_get hk, gpk]
  split
  · exact rep3 (by omega)
  · exact repT (by omega)

theorem hgsC : ∀ k < 2, Rep 4060 ruGs[k]! (gpc k) := fun k hk => by
  rw [gC_get hk]
  exact rep3 (by omega)

theorem hgQ : ∀ k < 2, RepF 4060 (gq k) (gpq k) := fun k hk => repFT (by omega)

theorem hgK : ∀ k < 3, RepF 4060 (gk k) (gpk k) := fun k hk => by
  interval_cases k
  · rw [gpk, if_neg (by norm_num)]
    exact repFT (k := 6) (by norm_num)
  · rw [gpk, if_neg (by norm_num)]
    exact repFT (k := 7) (by norm_num)
  · rw [gpk, if_pos rfl]
    exact repF3 (k := 0) (by norm_num)

theorem hgC : ∀ k < 2, RepF 4060 (gc k) (gpc k) := fun k hk => repF3 (k := 1 + k) (by omega)

theorem memQ : ∀ k < 2, gpq k ∈ ruP := fun k hk => memT (by omega)

theorem memK : ∀ k < 3, gpk k ∈ ruP := fun k hk => by
  unfold gpk
  split
  · exact mem3 (by omega)
  · exact memT (by omega)

theorem memC : ∀ k < 2, gpc k ∈ ruP := fun k hk => mem3 (by omega)

theorem treeQ : TreeOK 2 1080 TQ.P TQ.L := treeOK_of fun i hi h0 => by
  have h := Orb.allN_iff.1 kTreeQ i hi
  rwa [CFSG.KC.HeLoc.beq_zero_false h0] at h

theorem treeK : TreeOK 3 180 TK.P TK.L := treeOK_of fun i hi h0 => by
  have h := Orb.allN_iff.1 kTreeK i hi
  rwa [CFSG.KC.HeLoc.beq_zero_false h0] at h

theorem treeC : TreeOK 2 2160 TC.P TC.L := treeOK_of fun i hi h0 => by
  have h := Orb.allN_iff.1 kTreeC i hi
  rwa [CFSG.KC.HeLoc.beq_zero_false h0] at h

theorem edgesQ : ∀ i < 1080, ∀ k < 2, EQ i k < 1080 ∧
    treeArr 4060 ruTcD.gQ TQ.P TQ.L (EQ i k) =
      compA 4060 ruTcD.gQ[k]! (treeArr 4060 ruTcD.gQ TQ.P TQ.L i) :=
  edges_of_edgeAtK treeQ hgQ hgsQ hmul memQ (q0_iff memQ) q0_lt bs_lt hF2
    fun i hi => Orb.allN_iff.1 kEdgeQ i hi

theorem edgesK : ∀ i < 180, ∀ k < 3, EK i k < 180 ∧
    treeArr 4060 ruTcD.gK TK.P TK.L (EK i k) =
      compA 4060 ruTcD.gK[k]! (treeArr 4060 ruTcD.gK TK.P TK.L i) :=
  edges_of_edgeAtK treeK hgK hgsK hmul memK (q0_iff memK) q0_lt bs_lt hF2
    fun i hi => Orb.allN_iff.1 kEdgeK i hi

theorem edgesC : ∀ i < 2160, ∀ k < 2, EC i k < 2160 ∧
    treeArr 4060 ruGs TC.P TC.L (EC i k) =
      compA 4060 ruGs[k]! (treeArr 4060 ruGs TC.P TC.L i) :=
  edges_of_edgeAtK treeC hgC hgsC hmul memC (q0_iff memC) q0_lt bs_lt hF2
    fun i hi => Orb.allN_iff.1 kEdgeC i hi

theorem keyQ : ∀ a < 1080, ∀ b < 1080, keyA 4060 ruKeys (treeArr 4060 ruTcD.gQ TQ.P TQ.L a) =
    keyA 4060 ruKeys (treeArr 4060 ruTcD.gQ TQ.P TQ.L b) → a = b := by
  have hk := keys_inj_of_sortAtK (key := kq) fun j hj => Orb.allN_iff.1 kSortQ j hj
  intro a ha b hb e
  rw [keyA_treeArr treeQ hgQ hgsQ keys_lt ha, keyA_treeArr treeQ hgQ hgsQ keys_lt hb] at e
  exact hk a ha b hb e

theorem keyK : ∀ a < 180, ∀ b < 180, keyA 4060 ruKeys (treeArr 4060 ruTcD.gK TK.P TK.L a) =
    keyA 4060 ruKeys (treeArr 4060 ruTcD.gK TK.P TK.L b) → a = b := by
  have hk := keys_inj_of_sortAtK (key := kk) fun j hj => Orb.allN_iff.1 kSortK j hj
  intro a ha b hb e
  rw [keyA_treeArr treeK hgK hgsK keys_lt ha, keyA_treeArr treeK hgK hgsK keys_lt hb] at e
  exact hk a ha b hb e

theorem keyC : ∀ a < 2160, ∀ b < 2160, keyA 4060 ruKeys (treeArr 4060 ruGs TC.P TC.L a) =
    keyA 4060 ruKeys (treeArr 4060 ruGs TC.P TC.L b) → a = b := by
  have hk := keys_inj_of_sortAtK (key := kc) fun j hj => Orb.allN_iff.1 kSortC j hj
  intro a ha b hb e
  rw [keyA_treeArr treeC hgC hgsC keys_lt ha, keyA_treeArr treeC hgC hgsC keys_lt hb] at e
  exact hk a ha b hb e

theorem ptsQ : (ruTcCQ ()).pts =
    Array.ofFn (n := 1080) fun i => treeArr 4060 ruTcD.gQ TQ.P TQ.L i.val :=
  enumBfs_tree treeQ hgsQ (by simp [ruTcD]) (by norm_num) (by norm_num) keyQ edgesQ kReplayQ

theorem ptsK : (ruTcCK ()).pts =
    Array.ofFn (n := 180) fun i => treeArr 4060 ruTcD.gK TK.P TK.L i.val :=
  enumBfs_tree treeK hgsK (by simp [ruTcD]) (by norm_num) (by norm_num) keyK edgesK kReplayK

theorem ptsC : (ruCCert ()).pts =
    Array.ofFn (n := 2160) fun i => treeArr 4060 ruGs TC.P TC.L i.val :=
  enumBfs_tree treeC hgsC (by simp [ruGs]) (by norm_num) (by norm_num) keyC edgesC kReplayC

theorem enumQ : enumOK 4060 ruTcD.gQ ruKeys (ruTcCQ ()) = true :=
  enumOK_tree treeQ hgsQ (by simp [ruTcD]) (by norm_num) (by norm_num) keyQ edgesQ

theorem enumK : enumOK 4060 ruTcD.gK ruKeys (ruTcCK ()) = true :=
  enumOK_tree treeK hgsK (by simp [ruTcD]) (by norm_num) (by norm_num) keyK edgesK

theorem enumC : enumOK 4060 ruGs ruKeys (ruCCert ()) = true :=
  enumOK_tree treeC hgsC (by simp [ruGs]) (by norm_num) (by norm_num) keyC edgesC

theorem sizeQ : (ruTcCQ ()).pts.size = 1080 := by rw [ptsQ, Array.size_ofFn]

theorem sizeK : (ruTcCK ()).pts.size = 180 := by rw [ptsK, Array.size_ofFn]

theorem sizeC : (ruCCert ()).pts.size = 2160 := by rw [ptsC, Array.size_ofFn]

theorem el_tree {ng N : Nat} {gs : Array (Array Nat)} {gpt : Nat → Equiv.Perm (Fin 4060)}
    {g : Nat → Nat → Nat} {P Lb : Nat → Nat} (ht : TreeOK ng N P Lb)
    (hg : ∀ k < ng, RepF 4060 (g k) (gpt k)) (hgs : ∀ k < ng, Rep 4060 gs[k]! (gpt k))
    (hm : ∀ k < ng, gpt k ∈ ruP) {i : Nat} (hi : i < N) :
    ElF ruP (treeArr 4060 gs P Lb i) (trV g P Lb N i) := by
  have hr := rep_treeArr ht hgs i hi
  unfold ElF
  rw [CFSG.RankThree.Native.permOfArr_eq_of_rep hr]
  exact ⟨CFSG.RankThree.Native.F2.validA_of_rep hr, repF_trV ht hg N i hi.le hi,
    (trQ_spec ht hmul hm (q0_iff hm) q0_lt N i hi.le hi).1⟩

theorem elQ : ∀ i < 1080, ElF ruP (ruTcCQ ()).pts[i]! (tq i) := fun i hi => by
  rw [ptsQ, getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]
  exact el_tree treeQ hgQ hgsQ memQ hi

theorem elK : ∀ i < 180, ElF ruP (ruTcCK ()).pts[i]! (tk i) := fun i hi => by
  rw [ptsK, getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]
  exact el_tree treeK hgK hgsK memK hi

theorem elC : ∀ i < 2160, ElF ruP (ruCCert ()).pts[i]! (tc i) := fun i hi => by
  rw [ptsC, getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]
  exact el_tree treeC hgC hgsC memC hi

theorem bind_of {a : Array (Array Nat)} {m n w : Nat} {F : Nat → Nat} {g : Nat}
    (hs : a.size = m) (hg : g = m) (h : ∀ j < m, arrBind a[j]! n w (F j) = true) :
    BindA n w a g F := by
  subst hg
  exact ⟨hs, fun j hj => arrBind_sound (h j hj)⟩

theorem perm_of {m n w g : Nat} {F : Nat → Nat} (hg : g = m)
    (h : allN m (fun k => permB n w (F k)) = true) : ∀ k < g, permB n w (F k) = true := by
  subst hg
  exact allN_spec h

theorem hkeys6 : keys6.toList = List.range 6 := by decide +kernel

theorem hps6 : ∀ p ∈ keys6.toList, p < 6 := by
  rw [hkeys6]
  intro p hp
  exact List.mem_range.1 hp

theorem eS : enumOK 6 ruTcD.sig (List.range 6) (ruTcCS ()) = true ∧
    (ruTcCS ()).pts.size = ES.N := by
  have h := enum_of (fuel := 500)
    (bind_of (by decide +kernel) (Nat.eq_of_beq_eq_true nS) bS)
    (perm_of (Nat.eq_of_beq_eq_true nS) pS) ES.ok hps6 ES.keys (by decide +kernel)
  rw [hkeys6] at h
  exact ⟨h.1, h.2.1⟩

theorem reps_get {j : Nat} (h0 : 0 < j) (hj : j < 6) :
    ruTcD.reps[j]! = unpack 4060 12 (RT.F (7 + j)) := by
  rw [← arrT (by omega)]
  interval_cases j <;> rfl

theorem elX : ElF ruP ruX (t3 0) := by
  rw [ruX, arr3 (by norm_num)]
  exact (elF3 (k := 0) (by norm_num)).1

theorem tc_ok : tcOK 4060 6 ruKeys ruX ruTcD (ruTcCQ ()) (ruTcCK ()) (ruTcCS ()) = true := by
  refine tcOK_of_F (bs := bs) bs_lt faithful elX (by simp [ruTcD]) (fun i hi => ?_)
    (by simp [ruTcD]) (fun i hi => ?_) (by simp [ruTcD]) (fun i hi => ?_) (by simp [ruTcD])
    (fun l hl => ?_) (by simp [ruTcD]) (fun j hj => ?_) (by simp [ruTcD]) (fun i _ j _ => rfl)
    enumQ sizeQ elQ enumK sizeK elK eS.1 eS.2 rest
  · rw [gQ_get hi]
    exact (elFT (by omega)).1
  · have e : ruTcD.cu[i]! = unpack 4060 12 (RT.F (2 + 2 * i)) := by
      rw [← arrT (by omega)]
      interval_cases i <;> rfl
    rw [e]
    exact elFT (by omega)
  · have e : ruTcD.cv[i]! = unpack 4060 12 (RT.F (3 + 2 * i)) := by
      rw [← arrT (by omega)]
      interval_cases i <;> rfl
    rw [e]
    exact elFT (by omega)
  · rw [gK_get hl]
    interval_cases l
    · rw [if_neg (by norm_num)]
      exact (elFT (k := 6) (by norm_num)).1
    · rw [if_neg (by norm_num)]
      exact (elFT (k := 7) (by norm_num)).1
    · rw [if_pos rfl]
      exact (elF3 (k := 0) (by norm_num)).1
  · interval_cases j
    · exact elF_id
    all_goals
      rw [reps_get (by norm_num) (by norm_num)]
      exact elFT (by norm_num)

theorem ruTc_ok : ruTcOK () = true := by
  unfold ruTcOK
  rw [tc_ok, Bool.true_and, Bool.and_eq_true, allLt_iff, allLt_iff]
  refine ⟨fun l hl => ?_, fun k hk => ?_⟩
  · have hl2 : l < 2 := by simpa [ruTcD] using hl
    rw [gQ_get hl2]
    exact any_of_memF sizeC elC (repT (by omega)) (memT (by omega)) (repFT (by omega))
      (Orb.allN_iff.1 inC l hl2)
  · have hk2 : k < 2 := by simpa [ruGs] using hk
    rw [allLt_iff]
    intro l hl
    have hl2 : l < 2 := by simpa [ruTcD] using hl
    rw [gC_get hk2, gQ_get hl2]
    have hr := rep_conjA (valid3 (k := 1 + k) (by omega)) (repT (k := l) (by omega))
    have hp : permOfArr 4060 (unpack 4060 12 (R3.F (1 + k))) = gp3 (1 + k) := rfl
    rw [hp] at hr
    refine any_of_memF sizeQ elQ hr
      (ruP.mul_mem (ruP.mul_mem (mem3 (by omega)) (memT (by omega))) (ruP.inv_mem (mem3 (by omega))))
      ?_ (Orb.allN_iff.1 (Orb.allN_iff.1 normQ k hk2) l hl2)
    rw [mul_assoc]
    exact (repF3 (k := 1 + k) (by omega)).comp ((repFT (k := l) (by omega)).comp
      (repF3i (k := 1 + k) (by omega)))

end Ru

end CertificateChecks.KernelTc.Ru

end
