module

public import Certificates.Kernel.Misc.Perm.HS100.BaseGlue
public import Certificates.Kernel.Misc.Perm.HS100.FiveChecks
public import CFSG.Certificates.Kernel.ConjOrbSound
public import CFSG.Certificates.Kernel.Misc.ChainTailSound

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelMisc.HS100.Five

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin CFSG.KC.PermWit
  CFSG.RankThree.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer
  CFSG.EvenSporadicStandard.HSStd CFSG.EvenSporadicStandard.HSStd.Zassenhaus.HSFive
  CFSG.KC.Misc.HexFlat
open CFSG.KC.Misc.ArrEnum (permB pp_of_permB conj_unpack' memK any_eqA_unpack')
open CertificateChecks.KernelMisc.HS100
open CFSG.KLie.CT (fget)

theorem tab_eq (k : ℕ) (hk : k < 21) : tab k = unpack 100 7 (FX.F k) := by
  rw [tab, FX.eq]
  exact hexTable3_sound FX.all k hk

theorem ppF {k : ℕ} (hk : k < 21) : PP 100 7 (FX.F k) := pp_of_permB sz (allN_spec fperm k hk)

theorem validF {k : ℕ} (hk : k < 21) : validA 100 (unpack 100 7 (FX.F k)) = true :=
  validA_unpack (allN_spec fperm k hk)

theorem inP {k : ℕ} (hk : k < 21) : s5InP (unpack 100 7 (FX.F k)) = true :=
  s5InP_unpack (allN_spec fsift k hk)

theorem hidA : idA 100 = unpack 100 7 (pidn 100 7) := idA_eq sz

theorem pidPP : PP 100 7 (pidn 100 7) := PP.id sz

theorem eqA_F {p q : ℕ} (hp : canonK 100 7 (mask 7) (100 * 7) p = true)
    (hq : canonK 100 7 (mask 7) (100 * 7) q = true) :
    eqA 100 (unpack 100 7 p) (unpack 100 7 q) = Nat.beq p q := eqA_unpack hp hq

theorem pw_eq (x : Array ℕ) : ∀ e, pw x e = CFSG.Monster.B.Mathieu.powArr 100 x e
  | 0 => rfl
  | e + 1 => by rw [pw, CFSG.Monster.B.Mathieu.powArr, pw_eq x e]

theorem ppow_succ (p e : ℕ) : ppow 100 7 (mask 7) (pidn 100 7) p (e + 1) =
    pcomp 100 7 (mask 7) p (ppow 100 7 (mask 7) (pidn 100 7) p e) :=
  CFSG.KS.PEnum.strictN_app' _ _

theorem ppow_canon {p : ℕ} (hp : canonK 100 7 (mask 7) (100 * 7) p = true) :
    ∀ e, canonK 100 7 (mask 7) (100 * 7) (ppow 100 7 (mask 7) (pidn 100 7) p e) = true
  | 0 => pidPP.1
  | e + 1 => by rw [ppow_succ]; exact canonK_pcomp hp (ppow_canon hp e)

theorem pw_unpack {p : ℕ} (hp : canonK 100 7 (mask 7) (100 * 7) p = true) :
    ∀ e, pw (unpack 100 7 p) e = unpack 100 7 (ppow 100 7 (mask 7) (pidn 100 7) p e)
  | 0 => hidA
  | e + 1 => by
    rw [pw, pw_unpack hp e, compA_unpack hp (ppow_canon hp e), ppow_succ]

theorem commA_F {p q : ℕ} (hp : canonK 100 7 (mask 7) (100 * 7) p = true)
    (hq : canonK 100 7 (mask 7) (100 * 7) q = true) :
    commA 100 (unpack 100 7 p) (unpack 100 7 q) =
      Nat.beq (pcomp 100 7 (mask 7) p q) (pcomp 100 7 (mask 7) q p) := by
  rw [commA, compA_unpack hp hq, compA_unpack hq hp, eqA_F (canonK_pcomp hp hq) (canonK_pcomp hq hp)]

theorem and_of {a b : Bool} (h : (a && b) = true) : a = true ∧ b = true := by
  simpa using h

theorem keysOK : ∀ p ∈ keys, p < 100 := by decide

theorem cu_get : ∀ k < CU.ng, cuGens[k]! = unpack 100 7 (CU.G k) := by
  intro k hk
  have hk3 : k < 3 := by have := and_of nums; simp_all
  rw [Nat.eq_of_beq_eq_true (allN_spec gCU k hk3)]
  interval_cases k
  · exact tab_eq 2 (by norm_num)
  · exact tab_eq 3 (by norm_num)
  · exact tab_eq 4 (by norm_num)

theorem nums' : CU.ng = 3 ∧ CU.N = 2880 ∧ CF.ng = 3 ∧ CF.N = 300 ∧ AA.ng = 2 ∧ AA.N = 60 ∧
    SS.ng = 2 ∧ SS.N = 9 ∧ U.ng = 2 ∧ U.N = 15400 ∧ U.r0 = 0 := by
  have h := nums
  simp only [Bool.and_eq_true, Nat.beq_eq] at h
  tauto

theorem cf_get : ∀ k < CF.ng, cfGens[k]! = unpack 100 7 (CF.G k) := by
  intro k hk
  rw [nums'.2.2.1] at hk
  rw [Nat.eq_of_beq_eq_true (allN_spec gCF k hk)]
  interval_cases k
  · exact tab_eq 5 (by norm_num)
  · exact tab_eq 6 (by norm_num)
  · exact tab_eq 7 (by norm_num)

theorem a_get : ∀ k < AA.ng, aGens[k]! = unpack 100 7 (AA.G k) := by
  intro k hk
  rw [nums'.2.2.2.2.1] at hk
  rw [Nat.eq_of_beq_eq_true (allN_spec gAA k hk)]
  interval_cases k
  · exact tab_eq 8 (by norm_num)
  · exact tab_eq 9 (by norm_num)

theorem s_get : ∀ k < SS.ng, sGens[k]! = unpack 100 7 (SS.G k) := by
  intro k hk
  rw [nums'.2.2.2.2.2.2.1] at hk
  rw [Nat.eq_of_beq_eq_true (allN_spec gSS k hk)]
  interval_cases k
  · exact tab_eq 10 (by norm_num)
  · exact tab_eq 11 (by norm_num)

theorem p_get : ∀ k < U.ng, pGens[k]! = unpack 100 7 (U.G k) := by
  intro k hk
  rw [nums'.2.2.2.2.2.2.2.2.1] at hk
  rw [Nat.eq_of_beq_eq_true (allN_spec gU k hk)]
  interval_cases k
  · exact hs100Arr_eq 0 (by norm_num)
  · exact hs100Arr_eq 1 (by norm_num)

theorem gperm {G : ℕ → ℕ} {lo m : ℕ} (hG : ∀ k < m, G k = FX.F (lo + k)) (hm : lo + m ≤ 21) :
    ∀ k < m, permOK 100 7 (mask 7) (100 * 7) (G k) (pinvS 100 7 (mask 7) (G k)) = true := by
  intro k hk
  rw [hG k hk]
  exact allN_spec fperm (lo + k) (by omega)

theorem cuPts : cuCert.pts = Array.ofFn (n := CU.N) fun i => unpack 100 7 (CU.T i.val) :=
  enumBfs_pts_base (by rw [nums'.1]; rfl) cu_get CU.ok keysOK kCU (by rw [nums'.2.1]; omega)

theorem cuOK : enumOK 100 cuGens keys cuCert = true :=
  enumOK_of_bfsK_base (by rw [nums'.1]; rfl) cu_get
    (gperm (lo := 2) (fun k hk => (Nat.eq_of_beq_eq_true (allN_spec gCU k (nums'.1 ▸ hk))))
      (by rw [nums'.1]; norm_num))
    CU.ok keysOK kCU (by rw [nums'.2.1]; omega)

theorem cfPts : cfCert.pts = Array.ofFn (n := CF.N) fun i => unpack 100 7 (CF.T i.val) :=
  enumBfs_pts_base (by rw [nums'.2.2.1]; rfl) cf_get CF.ok keysOK kCF
    (by rw [nums'.2.2.2.1]; omega)

theorem cfOK : enumOK 100 cfGens keys cfCert = true :=
  enumOK_of_bfsK_base (by rw [nums'.2.2.1]; rfl) cf_get
    (gperm (lo := 5) (fun k hk => (Nat.eq_of_beq_eq_true (allN_spec gCF k (nums'.2.2.1 ▸ hk))))
      (by rw [nums'.2.2.1]; norm_num))
    CF.ok keysOK kCF (by rw [nums'.2.2.2.1]; omega)

theorem aPts : aCert.pts = Array.ofFn (n := AA.N) fun i => unpack 100 7 (AA.T i.val) :=
  enumBfs_pts_base (by rw [nums'.2.2.2.2.1]; rfl) a_get AA.ok keysOK kAA
    (by rw [nums'.2.2.2.2.2.1]; omega)

theorem aOK : enumOK 100 aGens keys aCert = true :=
  enumOK_of_bfsK_base (by rw [nums'.2.2.2.2.1]; rfl) a_get
    (gperm (lo := 8)
      (fun k hk => (Nat.eq_of_beq_eq_true (allN_spec gAA k (nums'.2.2.2.2.1 ▸ hk))))
      (by rw [nums'.2.2.2.2.1]; norm_num))
    AA.ok keysOK kAA (by rw [nums'.2.2.2.2.2.1]; omega)

theorem sPts : sCert.pts = Array.ofFn (n := SS.N) fun i => unpack 100 7 (SS.T i.val) :=
  enumBfs_pts_base (by rw [nums'.2.2.2.2.2.2.1]; rfl) s_get SS.ok keysOK kSS
    (by rw [nums'.2.2.2.2.2.2.2.1]; omega)

theorem sOK : enumOK 100 sGens keys sCert = true :=
  enumOK_of_bfsK_base (by rw [nums'.2.2.2.2.2.2.1]; rfl) s_get
    (gperm (lo := 10)
      (fun k hk => (Nat.eq_of_beq_eq_true (allN_spec gSS k (nums'.2.2.2.2.2.2.1 ▸ hk))))
      (by rw [nums'.2.2.2.2.2.2.1]; norm_num))
    SS.ok keysOK kSS (by rw [nums'.2.2.2.2.2.2.2.1]; omega)

theorem u0_eq : u0 = unpack 100 7 (FX.F 0) := tab_eq 0 (by norm_num)

theorem f0_eq : f0 = unpack 100 7 (FX.F 1) := tab_eq 1 (by norm_num)

theorem a3_eq : a3 = unpack 100 7 (FX.F 12) := tab_eq 12 (by norm_num)

theorem uOrb : arrCertOK (fun k a => conjA 100 pGens[k]! a) pGens.size (validA 100)
      (keyA 100 keys) u0 uOrbit = true ∧ uOrbit.pts.size = 15400 := by
  have hng : pGens.size = U.ng := by rw [nums'.2.2.2.2.2.2.2.2.1]; rfl
  have hN := nums'.2.2.2.2.2.2.2.2.2.1
  have hr := nums'.2.2.2.2.2.2.2.2.2.2
  unfold uOrbit
  obtain ⟨h1, -, h3⟩ := CFSG.KC.ConjOrb.arrBfs_of_orb (ng := pGens.size) (ngc := U.ng)
    (fuel := 20000) (act := fun k a => conjA 100 pGens[k]! a) (root := u0) (hng ▸ le_refl _)
    (fun k hk => p_get k (hng ▸ hk)) (fun _ _ _ => rfl) U.h
    (fun i hi => U.cl i (by rw [hN] at hi; omega)) (fun i hi => U.tr0 i (by rw [hN] at hi; omega))
    (by rw [hN, hr]; norm_num) (by rw [Nat.eq_of_beq_eq_true rootU]; exact u0_eq)
    (by rw [u0_eq]; exact validF (by norm_num)) keysOK U.k (by rw [hN]; norm_num)
  exact ⟨h1, h3.trans hN⟩

theorem prods' : Nat.beq (pcomp 100 7 (mask 7) (FX.F 0) (FX.F 0)) (pidn 100 7) = true ∧
    Nat.beq (FX.F 0) (pidn 100 7) = false ∧ Nat.beq (fP 5) (pidn 100 7) = true ∧
    Nat.beq (FX.F 1) (pidn 100 7) = false ∧
    Nat.beq (pcomp 100 7 (mask 7) (FX.F 1) (FX.F 0)) (pcomp 100 7 (mask 7) (FX.F 0) (FX.F 1)) =
      true ∧
    Nat.beq (ppow 100 7 (mask 7) (pidn 100 7) (FX.F 12) 3) (pidn 100 7) = true ∧
    Nat.beq (FX.F 12) (pidn 100 7) = false ∧ memK SS.N SS.T (FX.F 12) = true ∧
    memK AA.N AA.T (FX.F 0) = true := by
  have h := prods
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
  tauto

theorem cF (k : ℕ) (hk : k < 21) : canonK 100 7 (mask 7) (100 * 7) (FX.F k) = true := (ppF hk).1

theorem c4 : eqA 100 (compA 100 u0 u0) (idA 100) = true := by
  rw [u0_eq, compA_unpack (cF 0 (by norm_num)) (cF 0 (by norm_num)), hidA,
    eqA_F (canonK_pcomp (cF 0 (by norm_num)) (cF 0 (by norm_num))) pidPP.1]
  exact prods'.1

theorem c5 : (!eqA 100 u0 (idA 100)) = true := by
  rw [u0_eq, hidA, eqA_F (cF 0 (by norm_num)) pidPP.1, prods'.2.1]
  rfl

theorem c1 : allLt pGens.size (fun k => validA 100 pGens[k]!) = true := by
  rw [allLt_iff]
  intro k hk
  have hk' : k < 2 := hk
  rw [p_get k (by rw [nums'.2.2.2.2.2.2.2.2.1]; exact hk'),
    Nat.eq_of_beq_eq_true (allN_spec gU k hk')]
  exact validA_unpack (allN_spec hperm k hk')

theorem hcu : ∀ i < CU.N, canonK 100 7 (mask 7) (100 * 7) (CU.T i) = true := bfsK_canon CU.ok

theorem cuList : cuCert.pts.toList = (List.range CU.N).map fun i => unpack 100 7 (CU.T i) := by
  rw [cuPts]
  exact pts_toList (fun i => unpack 100 7 (CU.T i))

theorem cuWit : (cuCert.pts.toList.all fun x => !eqA 100 (pw x 5) (idA 100) ||
    eqA 100 x (idA 100) || cuCert.pts.toList.any fun y =>
      eqA 100 (compA 100 y x) (compA 100 f0 y)) = true := by
  rw [cuList, List.all_eq_true]
  intro x hx
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
  have hi' := List.mem_range.1 hi
  have hc := hcu i hi'
  have hw := allN_spec hW5 i hi'
  unfold ordWitPt at hw
  rw [CFSG.KC.ConjOrb.strictB_eq, CFSG.KC.ConjOrb.strictB_eq] at hw
  rw [pw_unpack hc, hidA, eqA_F (ppow_canon hc 5) pidPP.1, eqA_F hc pidPP.1]
  simp only [Bool.or_eq_true, Bool.and_eq_true, Nat.blt_eq] at hw ⊢
  rcases hw with (h | h) | ⟨hj, he⟩
  · exact Or.inl (Or.inl h)
  · exact Or.inl (Or.inr h)
  · refine Or.inr (List.any_eq_true.2 ⟨_, List.mem_map.2 ⟨_, List.mem_range.2 hj, rfl⟩, ?_⟩)
    rw [f0_eq, compA_unpack (hcu _ hj) hc, compA_unpack (cF 1 (by norm_num)) (hcu _ hj),
      eqA_F (canonK_pcomp (hcu _ hj) hc) (canonK_pcomp (cF 1 (by norm_num)) (hcu _ hj))]
    exact he

theorem c8 : allLt cuGens.size (fun k => commA 100 cuGens[k]! u0 && s5InP cuGens[k]!) = true := by
  rw [allLt_iff]
  intro k hk
  have hk3 : k < 3 := hk
  have hk' : Nat.add 2 k < 21 := by simp only [Nat.add_eq]; omega
  rw [cu_get k (by rw [nums'.1]; exact hk3), Nat.eq_of_beq_eq_true (allN_spec gCU k hk3), u0_eq,
    commA_F (cF _ hk') (cF 0 (by norm_num)), inP hk', Bool.and_true]
  have h := (and_of (and_of comms).1).1
  exact allN_spec h k hk3

theorem c9 : validA 100 f0 = true ∧ s5InP f0 = true ∧ eqA 100 (pw f0 5) (idA 100) = true ∧
    (!eqA 100 f0 (idA 100)) = true ∧ commA 100 f0 u0 = true := by
  rw [f0_eq, u0_eq]
  refine ⟨validF (by norm_num), inP (by norm_num), ?_, ?_, ?_⟩
  · rw [pw_unpack (cF 1 (by norm_num)), hidA, eqA_F (ppow_canon (cF 1 (by norm_num)) 5) pidPP.1]
    exact prods'.2.2.1
  · rw [hidA, eqA_F (cF 1 (by norm_num)) pidPP.1, prods'.2.2.2.1]
    rfl
  · rw [commA_F (cF 1 (by norm_num)) (cF 0 (by norm_num))]
    exact prods'.2.2.2.2.1

theorem centralizerOK_true : centralizerOK = true := by
  unfold centralizerOK
  have c2 : validA 100 u0 = true := by rw [u0_eq]; exact validF (by norm_num)
  have c3 : s5InP u0 = true := by rw [u0_eq]; exact inP (by norm_num)
  have hsz : cuCert.pts.size = 2880 := by rw [cuPts, Array.size_ofFn, nums'.2.1]
  rw [c1, c2, c3, c4, c5, uOrb.1, uOrb.2, cuOK, c8, c9.1, c9.2.1, c9.2.2.1, c9.2.2.2.1,
    c9.2.2.2.2, cuWit, hsz]
  rfl

theorem f1 : relsOK 100 hs100BaseArr f0 rels = true := by
  rw [f0_eq]
  decide +kernel

theorem f3 : allLt cfGens.size (fun k => commA 100 cfGens[k]! f0 && s5InP cfGens[k]!) = true := by
  rw [allLt_iff]
  intro k hk
  have hk3 : k < 3 := hk
  have hk' : Nat.add 5 k < 21 := by simp only [Nat.add_eq]; omega
  rw [cf_get k (by rw [nums'.2.2.1]; exact hk3), Nat.eq_of_beq_eq_true (allN_spec gCF k hk3), f0_eq,
    commA_F (cF _ hk') (cF 1 (by norm_num)), inP hk', Bool.and_true]
  have h := (and_of (and_of comms).1).2
  exact allN_spec h k hk3

theorem f6 : allLt aGens.size (fun k => commA 100 aGens[k]! f0 && s5InP aGens[k]!) = true := by
  rw [allLt_iff]
  intro k hk
  have hk2 : k < 2 := hk
  have hk' : Nat.add 8 k < 21 := by simp only [Nat.add_eq]; omega
  rw [a_get k (by rw [nums'.2.2.2.2.1]; exact hk2), Nat.eq_of_beq_eq_true (allN_spec gAA k hk2), f0_eq,
    commA_F (cF _ hk') (cF 1 (by norm_num)), inP hk', Bool.and_true]
  have h := (and_of comms).2
  exact allN_spec h k hk2

theorem cfList : cfCert.pts.toList = (List.range CF.N).map fun i => unpack 100 7 (CF.T i) := by
  rw [cfPts]
  exact pts_toList (fun i => unpack 100 7 (CF.T i))

theorem aList : aCert.pts.toList = (List.range AA.N).map fun i => unpack 100 7 (AA.T i) := by
  rw [aPts]
  exact pts_toList (fun i => unpack 100 7 (AA.T i))

theorem sList : sCert.pts.toList = (List.range SS.N).map fun i => unpack 100 7 (SS.T i) := by
  rw [sPts]
  exact pts_toList (fun i => unpack 100 7 (SS.T i))

theorem hcf : ∀ i < CF.N, canonK 100 7 (mask 7) (100 * 7) (CF.T i) = true := bfsK_canon CF.ok

theorem ha : ∀ i < AA.N, canonK 100 7 (mask 7) (100 * 7) (AA.T i) = true := bfsK_canon AA.ok

theorem hs : ∀ i < SS.N, canonK 100 7 (mask 7) (100 * 7) (SS.T i) = true := bfsK_canon SS.ok

theorem f4 : ptailOK 100 s5Levels hs100BaseArr f0 (pow5A 100 f0) rels cfCert.pts.toList
    hs100BaseArr.size 0 (idA 100) = true := by
  have hb : hs100BaseArr.size = 5 := by decide
  have hp5 : (pow5A 100 f0).size = 5 := by simp [pow5A]
  rw [hb]
  unfold s5Levels
  refine CFSG.KC.Misc.ChainTail.ptailK_sound c_binds cperm C.hl f0_eq (allN_spec fperm 1 (by norm_num))
    (XP := fP) (fun e he => ?_) (fun r hr => ?_) cfList (fun e he => allN_spec (and_of tperm).1 e he)
    (by norm_num) (fun k hk => allN_spec br k ?_)
  · rw [hp5] at he
    rw [getElem!_pos _ e (by rw [hp5]; exact he)]
    simp only [pow5A, Array.getElem_ofFn]
    rw [f0_eq, CFSG.KC.Misc.ArrEnum.pow_unpack' sz (allN_spec fperm 1 (by norm_num)) e]
    rfl
  · rw [hp5]
    revert r
    decide
  · rw [Nat.eq_of_beq_eq_true rc] at hk
    exact hk

theorem keyInj {N : ℕ} {T : ℕ → ℕ} {SK : List ℕ} (hK : keysSK 100 7 keys N T SK = true) :
    ∀ i < N, ∀ j < N, keyA 100 keys (unpack 100 7 (T i)) = keyA 100 keys (unpack 100 7 (T j)) →
      i = j := by
  intro i hi j hj e
  rw [keyA_unpack keysOK, keyA_unpack keysOK] at e
  exact keysSK_spec hK i hi j hj e

theorem f7 : conjSimpleOK 100 keys aCert = true := by
  refine conjSimpleOK_of_ctree (WT := WT) sz keysOK aOK aPts (fun i hi => allN_spec (and_of tperm).2 i hi)
    (Nat.eq_of_beq_eq_true (and_of (and_of misc).1).1) (keyInj kAA) (fun k hk => ?_)
  have h := allN_spec ctree k hk
  rw [Bool.or_eq_true] at h
  exact h.imp id fun h' => allN_spec h'

theorem any_mem {N : ℕ} {T : ℕ → ℕ} (hT : ∀ i < N, canonK 100 7 (mask 7) (100 * 7) (T i) = true)
    {t : ℕ} (ht : canonK 100 7 (mask 7) (100 * 7) t = true) (hm : memK N T t = true) :
    ((List.range N).map fun i => unpack 100 7 (T i)).any (eqA 100 (unpack 100 7 t)) = true := by
  unfold memK at hm
  rw [CFSG.KC.Misc.ArrEnum.anyNP_eq, List.any_eq_true] at hm
  obtain ⟨i, hi, he⟩ := hm
  have hi' := List.mem_range.1 hi
  refine List.any_eq_true.2 ⟨_, List.mem_map.2 ⟨i, hi, rfl⟩, ?_⟩
  rw [eqA_F ht (hT i hi')]
  exact he

theorem f8 : aCert.pts.toList.any (eqA 100 u0) = true := by
  rw [aList, u0_eq]
  exact any_mem ha (cF 0 (by norm_num)) prods'.2.2.2.2.2.2.2.2

theorem f9 : (cfCert.pts.toList.all fun x => (List.range 5).any fun e =>
    aCert.pts.toList.any fun a => eqA 100 x (compA 100 (pw f0 e) a)) = true := by
  rw [cfList, aList, List.all_eq_true]
  intro x hx
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
  have hi' := List.mem_range.1 hi
  have hw := allN_spec hWF i hi'
  rw [CFSG.KC.ConjOrb.strictB_eq] at hw
  simp only [Bool.and_eq_true, Nat.blt_eq] at hw
  obtain ⟨⟨he, hj⟩, hq⟩ := hw
  refine List.any_eq_true.2 ⟨_, List.mem_range.2 he, List.any_eq_true.2
    ⟨_, List.mem_map.2 ⟨_, List.mem_range.2 hj, rfl⟩, ?_⟩⟩
  rw [f0_eq, pw_unpack (cF 1 (by norm_num)), compA_unpack (ppow_canon (cF 1 (by norm_num)) _) (ha _ hj),
    eqA_F (hcf i hi') (canonK_pcomp (ppow_canon (cF 1 (by norm_num)) _) (ha _ hj))]
  exact hq

theorem card_filter_fin (m : ℕ) (f : ℕ → Bool) :
    (Finset.univ.filter fun i : Fin m => f i.1 = true).card = (List.range m).countP f := by
  have e : (Finset.univ.filter fun i : Fin m => f i.1 = true).map Fin.valEmbedding =
      (Finset.range m).filter fun i => f i = true := by
    ext x
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Fin.valEmbedding_apply,
      Finset.mem_range]
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact ⟨i.2, hi⟩
    · rintro ⟨hx, hf⟩
      exact ⟨⟨x, hx⟩, hf, rfl⟩
  rw [← Finset.card_map Fin.valEmbedding, e, Finset.card_filter]
  clear e
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih, List.range_succ, List.countP_append]
    cases h : f m <;> simp [h]

theorem aGet : ∀ i < AA.N, aCert.pts[i]! = unpack 100 7 (AA.T i) := by
  intro i hi
  rw [aPts, getElem!_pos _ i (by rw [Array.size_ofFn]; exact hi), Array.getElem_ofFn]

theorem f10 : (aCommCount == 4) = true := by
  have e := card_filter_fin aCert.pts.size (fun i => commA 100 u0 aCert.pts[i]!)
  have hsz : aCert.pts.size = AA.N := by rw [aPts, Array.size_ofFn]
  have hc : (List.range AA.N).countP (fun i => commA 100 u0 aCert.pts[i]!) =
      cntK AA.N (fun i => Nat.beq (pcomp 100 7 (mask 7) (FX.F 0) (AA.T i))
        (pcomp 100 7 (mask 7) (AA.T i) (FX.F 0))) := by
    rw [cntK_eq]
    apply List.countP_congr
    intro i hi
    have hi' := List.mem_range.1 hi
    rw [aGet i hi', u0_eq, commA_F (cF 0 (by norm_num)) (ha i hi')]
  unfold aCommCount
  rw [e, hsz, hc, Nat.eq_of_beq_eq_true acnt]
  rfl

theorem fiveCentralizerOK_true : fiveCentralizerOK = true := by
  unfold fiveCentralizerOK
  have h1 : cfCert.pts.size = 300 := by rw [cfPts, Array.size_ofFn, nums'.2.2.2.1]
  have h2 : aCert.pts.size = 60 := by rw [aPts, Array.size_ofFn, nums'.2.2.2.2.2.1]
  rw [f1, cfOK, h1, f3, f4, aOK, h2, f6, f7, f8, f9, f10]
  rfl

theorem s2 : allLt sGens.size (fun k => s5InP sGens[k]!) = true := by
  rw [allLt_iff]
  intro k hk
  have hk2 : k < 2 := hk
  have hk' : Nat.add 10 k < 21 := by simp only [Nat.add_eq]; omega
  rw [s_get k (by rw [nums'.2.2.2.2.2.2.1]; exact hk2), Nat.eq_of_beq_eq_true (allN_spec gSS k hk2)]
  exact inP hk'

theorem s3 : validA 100 a3 = true ∧ eqA 100 (pw a3 3) (idA 100) = true ∧
    (!eqA 100 a3 (idA 100)) = true ∧ sCert.pts.toList.any (eqA 100 a3) = true := by
  rw [a3_eq]
  refine ⟨validF (by norm_num), ?_, ?_, ?_⟩
  · rw [pw_unpack (cF 12 (by norm_num)), hidA, eqA_F (ppow_canon (cF 12 (by norm_num)) 3) pidPP.1]
    exact prods'.2.2.2.2.2.1
  · rw [hidA, eqA_F (cF 12 (by norm_num)) pidPP.1, prods'.2.2.2.2.2.2.1]
    rfl
  · rw [sList]
    exact any_mem hs (cF 12 (by norm_num)) prods'.2.2.2.2.2.2.2.1

theorem conjs_get {c : ℕ} (hc : c < 8) : conjs[c]! = unpack 100 7 (FX.F (Nat.add 13 c)) := by
  rw [conjs, getElem!_pos _ c (by simpa using hc), Array.getElem_ofFn]
  exact tab_eq _ (by simp only [Nat.add_eq]; omega)

theorem s4 : (sCert.pts.toList.all fun s => eqA 100 s (idA 100) ||
    conjs.toList.any fun c => validA 100 c && s5InP c && eqA 100 (conjA 100 c a3) s) = true := by
  rw [sList, List.all_eq_true]
  intro x hx
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
  have hi' := List.mem_range.1 hi
  have hw := allN_spec hWS i hi'
  rw [Bool.or_eq_true, CFSG.KC.ConjOrb.strictB_eq] at hw
  rw [hidA, eqA_F (hs i hi') pidPP.1, Bool.or_eq_true]
  rcases hw with h | h
  · exact Or.inl h
  · simp only [Bool.and_eq_true, Nat.blt_eq] at h
    obtain ⟨hc, he⟩ := h
    have hk : Nat.add 13 (WS i) < 21 := by simp only [Nat.add_eq]; omega
    refine Or.inr (List.any_eq_true.2 ⟨conjs[WS i]!, ?_, ?_⟩)
    · have hcs : conjs.size = 8 := by simp [conjs]
      rw [getElem!_pos _ _ (by rw [hcs]; exact hc)]
      exact Array.getElem_mem_toList _
    · rw [conjs_get hc, a3_eq, validF hk, inP hk, Bool.true_and, Bool.true_and,
        conj_unpack' sz (allN_spec fperm _ hk) (allN_spec fperm 12 (by norm_num)),
        eqA_F (canonK_pcomp (cF _ hk) (canonK_pcomp (cF 12 (by norm_num)) (ppF hk).inv.1)) (hs i hi')]
      exact he

theorem sylowThreeOK_true : sylowThreeOK = true := by
  unfold sylowThreeOK
  have h1 : sCert.pts.size = 9 := by rw [sPts, Array.size_ofFn, nums'.2.2.2.2.2.2.2.1]
  rw [sOK, h1, s2, s3.1, s3.2.1, s3.2.2.1, s3.2.2.2, s4]
  rfl

theorem hsFiveOK_true : hsFiveOK = true := by
  unfold hsFiveOK
  rw [centralizerOK_true, fiveCentralizerOK_true, sylowThreeOK_true]
  rfl

end CertificateChecks.KernelMisc.HS100.Five

end
