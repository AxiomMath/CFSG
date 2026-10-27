module

public import Certificates.Kernel.SporSch.Ly.SylLoc
public import Certificates.Kernel.SporSch.Ly.R3E2187
public import Certificates.Kernel.SporSch.Ly.Cover2184
public import CFSG.Certificates.Kernel.SporSch.LySylSound
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.LySyF

open CFSG.KC.Enum CFSG.KS CFSG.KC.Ord CFSG.KS.SporSch.LyM CFSG.KD.OrdLy CFSG.KS.SporSch.LySyl
open CFSG.Sporadic.LySchreier.Native CFSG.Sporadic.He.Native CFSG.Sporadic.Ly.Native
open CertificateChecks.KernelSporSch CertificateChecks.KernelSporSch.LyBS
open CertificateChecks.KernelSporSch.LyBSF CertificateChecks.KernelSporSch.LyR3E

local notation "U" X:max => unpackL 111 12 1332 X

theorem chain_at {Q : Nat → Bool} {nG R : Nat}
    (h : ∀ g < nG, ∀ r < R, Q (Nat.add (Nat.mul g R) r) = true) {t : Nat} (ht : t < nG * R) :
    Q t = true := by
  have hR : 0 < R := Nat.pos_of_ne_zero fun e => by simp [e] at ht
  have e : Nat.add (Nat.mul (t / R) R) (t % R) = t := Nat.div_add_mod' t R
  rw [← e]
  exact h _ (Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm])) _ (Nat.mod_lt _ hR)

theorem chain_atB {Q : Nat → Bool} {nG R : Nat}
    (h : ∀ g < nG, ∀ r < R, Q (Nat.add (Nat.mul g R) r) = true) {t B : Nat} (ht : t < B)
    (hB : B ≤ nG * R := by decide) : Q t = true :=
  chain_at h (Nat.lt_of_lt_of_le ht hB)

theorem lenLL_eq : ∀ L : List (List Nat), LySt.lenLL L = L.length
  | [] => rfl
  | _ :: L => congrArg Nat.succ (lenLL_eq L)

theorem getL_eq : ∀ (L : List (List Nat)) (t : Nat), LySt.getL L t = L.getD t []
  | [], _ => by simp [LySt.getL]
  | _ :: _, 0 => rfl
  | _ :: L, t + 1 => by
    rw [List.getD_cons_succ, ← getL_eq L t]
    rfl

theorem getN_eq : ∀ (l : List Nat) (t : Nat) (h : t < l.length), LySL.getN l t = l[t]
  | _ :: _, 0, _ => rfl
  | _ :: l, t + 1, h => by
    rw [List.getElem_cons_succ, ← getN_eq l t (by simpa using h)]
    rfl

theorem getC_eq : ∀ (l : List (Nat × List Int)) (t : Nat) (h : t < l.length), LySL.getC l t = l[t]
  | _ :: _, 0, _ => rfl
  | _ :: l, t + 1, h => by
    rw [List.getElem_cons_succ, ← getC_eq l t (by simpa using h)]
    rfl

theorem allLL_mem {n : Nat} : ∀ L : List (List Nat), LySt.allLL n L = true →
    ∀ E ∈ L, incL E = true ∧ CFSG.KS.Mathieu.allLtN n E = true
  | [], _ => by simp
  | E :: L, h => by
    have h' : bAnd(incL E, bAnd(CFSG.KS.Mathieu.allLtN n E, LySt.allLL n L)) = true := h
    obtain ⟨h1, h2⟩ := andOf h'
    obtain ⟨h2, h3⟩ := andOf h2
    intro E' hE'
    rcases List.mem_cons.mp hE' with rfl | hE'
    · exact ⟨h1, h2⟩
    · exact allLL_mem L h3 E' hE'

theorem tm_lt (MT : Nat → Nat) (i j : Nat) : tmK MT i j < 256 := by
  unfold tmK b8
  exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)

theorem tbl_get {MT : Nat → Nat} {n i j : Nat} (hi : i < n) (hj : j < n) :
    ((TBL MT n)[i]!)[j]! = tmK MT i j := by
  unfold TBL
  rw [getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn,
    getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn]

theorem ea_of {L L' : List (List Nat)} {NM CT : Nat → Nat} {nN nG R nG' R' : Nat}
    (hL : LySt.allLL 256 L = true)
    (hr : ∀ g < nG, ∀ r < R, LySt.eaQ L NM CT nN (Nat.add (Nat.mul g R) r) = true)
    (hm : ∀ g < nG', ∀ r < R', LySt.nmQ L' NM nN (Nat.add (Nat.mul g R') r) = true)
    (hl : L.length ≤ nG * R) (hl' : nN ≤ nG' * R') (hC0 : Nat.beq (CT 0) 0 = true)
    (hCn : Nat.beq (CT (LySt.lenLL L)) nN = true) (hlen : Nat.beq (LySt.lenLL L') nN = true)
    (hnN : nN < 1048576) :
    nextEA (TBL LySt.MT 256) 256 L = L' ∧ extOK (TBL LySt.MT 256) 256 L L' = true := by
  have e := Nat.eq_of_beq_eq_true hlen
  have eC := Nat.eq_of_beq_eq_true hCn
  rw [lenLL_eq] at e eC
  refine nextEA_sound (NM := NM) (by decide) (fun _ _ _ _ => tm_lt _ _ _) (allLL_mem L hL)
    (fun t ht => ?_)
    (Nat.eq_of_beq_eq_true hC0) eC hnN e (fun j hj => ?_)
  · have c := chain_at hr (t := t) (by omega)
    unfold LySt.eaQ at c
    rw [lenLL_eq, bl ht, getL_eq] at c
    exact Nat.eq_of_beq_eq_true c
  · have c := chain_at hm (t := j) (by omega)
    unfold LySt.nmQ at c
    rw [bl hj, getL_eq] at c
    exact c

theorem e6 : Nat.beq (LySy.E 6) A = true := by quickRfl

theorem keys : (LySt.CL.map (·.1) ==
    (List.range 256).filter (fun i => (i != 0 && tmK LySt.MT i i == 0) && i != 6)) = true := by
  decide +kernel

theorem key_lt {e : Nat × List Int} (he : e ∈ LySt.CL) : e.1 < 256 := by
  have h := keys
  rw [beq_iff_eq] at h
  have m : e.1 ∈ LySt.CL.map (·.1) := List.mem_map.mpr ⟨e, he, rfl⟩
  rw [h, List.mem_filter, List.mem_range] at m
  exact m.1

theorem qall : qIndices.toList.all (· < 256) = true := by decide +kernel

theorem qlen : qIndices.toList.length = 64 := by decide +kernel

theorem convEnd : (LyCJ.chars.getLast? == some '\n') = true := by quickRfl

theorem invC : invConjugators = LySt.CL := by
  unfold invConjugators
  rw [LyCJ.eq]
  exact conv_sound (fun c hc => by
    rw [beq_iff_eq.1 convEnd, Option.mem_some_iff] at hc; exact hc.symm) LySL.conv

@[expose] noncomputable def UGx (k : Nat) : Nat := if k < 6 then LySy.UG k else ONE

theorem wordFromM_congr {g gi g' gi' : Nat → Mat} (w : List Int) : ∀ (X : Mat),
    (∀ l ∈ w, letterM g gi l = letterM g' gi' l) → wordFromM g gi X w = wordFromM g' gi' X w := by
  induction w with
  | nil =>
    intro X _
    simp only [wordFromM, List.foldl_nil]
  | cons l w ih =>
    intro X h
    unfold wordFromM at ih ⊢
    rw [List.foldl_cons, List.foldl_cons, h l (by simp)]
    exact ih _ fun l' hl' => h l' (by simp [hl'])

theorem wordR_congr {G GI G' GI' : Nat → Nat} : ∀ (w : List Int) (X : Nat),
    (∀ l ∈ w, letterR G GI l = letterR G' GI' l) →
    wordR 5 12 1332 111 8 L H CM RM G GI X w = wordR 5 12 1332 111 8 L H CM RM G' GI' X w
  | [], _, _ => rfl
  | l :: w, X, h => by
    have e : ∀ (a b : Nat → Nat) (Y : Nat), wordR 5 12 1332 111 8 L H CM RM a b Y (l :: w) =
        wordR 5 12 1332 111 8 L H CM RM a b (mulR 5 12 1332 111 8 L H CM RM Y (letterR a b l)) w :=
      fun a b Y => strictN_val _ (fun X => wordR 5 12 1332 111 8 L H CM RM a b X w)
    rw [e, e, h l (by simp)]
    exact wordR_congr w _ fun l' hl' => h l' (by simp [hl'])

theorem qword (w : List Int) (hw : ∀ l ∈ w, 0 < l ∧ l ≤ 6) :
    evalWordM (fun k => (sylowGens (cStarArr (U B4)))[k]!)
        (fun k => (sylowGens (cStarArr (U B4)))[k]!) w =
      U (wordR 5 12 1332 111 8 L H CM RM LySy.UG LySy.UG ONE w) ∧
    vld (wordR 5 12 1332 111 8 L H CM RM LySy.UG LySy.UG ONE w) = true := by
  have hG : ∀ i, vld (UGx i) = true := fun i => by
    unfold UGx
    split
    · exact vUGk (by assumption)
    · exact vOne
  have e1 : evalWordM (fun k => (sylowGens (cStarArr (U B4)))[k]!)
      (fun k => (sylowGens (cStarArr (U B4)))[k]!) w =
      evalWordM (fun k => U (UGx k)) (fun k => U (UGx k)) w := by
    unfold evalWordM
    refine wordFromM_congr w _ fun l hl => ?_
    obtain ⟨h1, h2⟩ := hw l hl
    unfold letterM
    rw [ite_eq_left h1, ite_eq_left h1]
    dsimp only
    rw [us_get _ (by omega)]
    unfold UGx
    rw [ite_eq_left (by omega)]
  have e2 : wordR 5 12 1332 111 8 L H CM RM UGx UGx ONE w =
      wordR 5 12 1332 111 8 L H CM RM LySy.UG LySy.UG ONE w := by
    refine wordR_congr w _ fun l hl => ?_
    obtain ⟨h1, h2⟩ := hw l hl
    obtain ⟨k, rfl⟩ : ∃ k : Nat, l = ((k + 1 : Nat) : Int) := ⟨l.toNat - 1, by omega⟩
    have a : ∀ G GI : Nat → Nat, letterR G GI ((k + 1 : Nat) : Int) = G k := fun _ _ => rfl
    rw [a, a]
    unfold UGx
    rw [ite_eq_left (by omega)]
  rw [e1, ← e2]
  exact word_of (fun _ => rfl) (fun _ => rfl) hG hG w

theorem vWW : vld LySL.WW = true := by quickRfl
theorem vWI : vld LySL.WI = true := by quickRfl
theorem vX : vld LySL.X = true := by quickRfl
theorem vZX : vld LySL.ZX = true := by quickRfl
theorem vXF : vld LySL.XF = true := by quickRfl
theorem vGG : vld LySL.GG = true := by quickRfl

theorem n1 : Nat.beq (LySt.lenLL LySt.L1) LySt.nN1 = true := by quickRfl
theorem n2 : Nat.beq (LySt.lenLL LySt.L2) LySt.nN2 = true := by quickRfl
theorem n3 : Nat.beq (LySt.lenLL LySt.L3) LySt.nN3 = true := by quickRfl
theorem n4 : Nat.beq (LySt.lenLL LySt.L4) LySt.nN4 = true := by quickRfl
theorem b1 : Nat.ble (LySt.lenLL LySt.L1) 256 = true := by quickRfl
theorem b2 : Nat.ble (LySt.lenLL LySt.L2) 256 = true := by quickRfl
theorem b3 : Nat.ble (LySt.lenLL LySt.L3) 256 = true := by quickRfl
theorem b4 : Nat.ble (LySt.lenLL LySt.L4) 256 = true := by quickRfl
theorem b5 : Nat.blt LySt.nN4 1048576 = true := by quickRfl
theorem dt0 : Nat.beq (LySt.DT 0) 0 = true := by quickRfl
theorem c1 : Nat.beq (LySt.CT1 0) 0 = true := by quickRfl
theorem c2 : Nat.beq (LySt.CT2 0) 0 = true := by quickRfl
theorem c3 : Nat.beq (LySt.CT3 0) 0 = true := by quickRfl
theorem c4 : Nat.beq (LySt.CT4 0) 0 = true := by quickRfl
theorem d1 : Nat.beq (LySt.CT1 (LySt.lenLL [[0]])) LySt.nN1 = true := by quickRfl
theorem d2 : Nat.beq (LySt.CT2 (LySt.lenLL LySt.L1)) LySt.nN2 = true := by quickRfl
theorem d3 : Nat.beq (LySt.CT3 (LySt.lenLL LySt.L2)) LySt.nN3 = true := by quickRfl
theorem d4 : Nat.beq (LySt.CT4 (LySt.lenLL LySt.L3)) LySt.nN4 = true := by quickRfl

theorem local_ok : localOK (U B4) (cStarArr (U B4)) (sylowGens (cStarArr (U B4)))
    (TBL LySt.MT 256) (Array.ofFn (n := 256) fun i => U (LySy.E i.val)) = true := by
  have vw := vWW
  have vwi := vWI
  have vx := vX
  have vzx := vZX
  have vxf := vXF
  have vg := vGG
  have vc := (vCFi (i := 11) (by omega)).2
  have hf : (Array.ofFn (n := 256) fun i => U (LySy.E i.val))[fIndex ()]! = U (LySy.E 113) :=
    get_ofFn (i := fIndex ()) (by decide)
  have hh : (pairAt (cStarArr (U B4)) 11).2 = U (CI 11) := by
    rw [csCI]
    unfold CIx
    rw [bl (by norm_num)]
  have hg : ∀ i, seedM i = U (GS i) := fun i => by
    cases i with
    | zero => exact matA_eq
    | succ i => exact matB_eq
  have hgi : ∀ i, seedMInv (U B4) i = U (GSI i) := fun i => by
    cases i with
    | zero => exact matA_eq
    | succ i => rfl
  have hG : ∀ i, vld (GS i) = true := fun i => by
    cases i with
    | zero => exact vA
    | succ i => exact vB
  have hGI : ∀ i, vld (GSI i) = true := fun i => by
    cases i with
    | zero => exact vA
    | succ i => exact vB4
  have hw : evalWordM seedM (seedMInv (U B4)) (fusionWord ()) = U LySL.WW :=
    (word_of hg hgi hG hGI [1, 2]).1
  have hwi : invM 5 111 (U LySL.WW) = U LySL.WI :=
    invM_eq Nat.prime_five consts (hv vw) (hv vwi) LySL.wwi
  have hx : mulM 5 111 (mulM 5 111 (U LySL.WW) (U A)) (U LySL.WI) = U LySL.X := by
    rw [mulE vw vA, mulE (mulV vw vA) vwi]
    rfl
  have hzx : mulM 5 111 (U A) (U LySL.X) = U LySL.ZX := (mulE vA vx).trans rfl
  have hxf : mulM 5 111 (U LySL.X) (U (LySy.E 113)) = U LySL.XF := (mulE vx vF).trans rfl
  have p7 := powM_eq consts (hv vxf) 7
  have p4 := powM_eq consts (hv vzx) 4
  have p9 := powM_eq consts (hv vzx) 9
  have p15 := powM_eq consts (hv vxf) 15
  have hgg : mulM 5 111 (powM 5 111 (U LySL.XF) 7) (powM 5 111 (U LySL.ZX) 4) = U LySL.GG := by
    rw [p7.1, p4.1, mulE p7.2 p4.2]
    rfl
  unfold localOK
  simp only []
  rw [hf, hh, hw, hwi, matA_eq, hx, hzx, hxf, hgg, idE]
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · have hfl : (List.range 256).filter (fun i => isInv (TBL LySt.MT 256) i && i != 6) =
        (List.range 256).filter (fun i => (i != 0 && tmK LySt.MT i i == 0) && i != 6) := by
      apply List.filter_congr
      intro i hi
      rw [List.mem_range] at hi
      unfold isInv tm
      rw [tbl_get hi hi]
    rw [invC, hfl]
    exact keys
  · rw [invC, List.all_eq_true]
    intro e he
    obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem he
    have hk := key_lt (List.getElem_mem ht)
    have ht' : t < 58 := by rwa [LySL.clLen] at ht
    have c := chain_atB LySL.cjAll ht'
    unfold LySL.cjQ at c
    rw [bl ht', getC_eq _ _ ht] at c
    generalize LySt.CL[t] = e at c hk ⊢
    obtain ⟨k, w⟩ := e
    have c' : strictB (wordR 5 12 1332 111 8 L H CM RM (CFx 12) (CIx 12) ONE w) (fun M =>
        Nat.beq (mul M (LySy.E 113)) (mul (LySy.E k) M)) = true := c
    rw [CFSG.KS.Raw.strictB_eq] at c'
    dsimp only at hk ⊢
    obtain ⟨ew, vw'⟩ := word_of csCF csCI (fun i => (vCFx le_rfl i).1) (fun i => (vCFx le_rfl i).2) w
    rw [ew, get_ofFn hk]
    simp only []
    rw [mulE vw' vF, mulE (vEi hk) vw', beqE (mulV vw' vF) (mulV (vEi hk) vw')]
    exact c'
  · rw [mulE vc vc, mulE vc (mulV vc vc), beqE (mulV vc (mulV vc vc)) vOne]
    exact LySL.h3
  · rw [diffMod5_eq consts (hv vc) (hv vOne)]
    exact LySL.hne
  · rw [← Array.all_toList, List.all_eq_true]
    intro q hq
    obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem hq
    have hql : qIndices.toList[t] < 256 :=
      of_decide_eq_true (List.all_eq_true.mp qall _ (List.getElem_mem ht))
    have c := chain_atB LySL.hqAll (B := 64) (by rw [qlen] at ht; exact ht)
    have c' : strictB (LySL.getN qIndices.toList t) (fun q =>
        Nat.beq (mul (CI 11) (LySy.E q)) (mul (LySy.E q) (CI 11))) = true := c
    rw [CFSG.KS.Raw.strictB_eq, getN_eq _ _ ht] at c'
    rw [get_ofFn hql]
    simp only []
    rw [mulE vc (vEi hql), mulE (vEi hql) vc, beqE (mulV vc (vEi hql)) (mulV (vEi hql) vc)]
    exact c'
  · rw [mulE vw vwi, beqE (mulV vw vwi) vOne]
    exact LySL.wwi
  · rw [p9.1, beqE p9.2 vOne]
    exact LySL.z9
  · rw [p15.1, beqE p15.2 vOne]
    exact LySL.x15
  · rw [mulE vg vA, mulE vF vg, beqE (mulV vg vA) (mulV vF vg)]
    exact LySL.gA
  · rw [List.all_eq_true]
    intro e he
    simp only [qWords, List.mem_cons, List.mem_nil_iff, or_false] at he
    rcases he with rfl | rfl | rfl | rfl
    · obtain ⟨ew, vw'⟩ := qword [3, 1, 3, 2, 1] (by decide)
      dsimp only
      rw [ew, get_ofFn (i := 155) (by omega)]
      simp only []
      rw [beqE vw' (vEi (by omega))]
      exact LySL.qw0
    · obtain ⟨ew, vw'⟩ := qword [1, 3, 4, 1] (by decide)
      dsimp only
      rw [ew, get_ofFn (i := 101) (by omega)]
      simp only []
      rw [beqE vw' (vEi (by omega))]
      exact LySL.qw1
    · obtain ⟨ew, vw'⟩ := qword [4, 3, 2] (by decide)
      dsimp only
      rw [ew, get_ofFn (i := 49) (by omega)]
      simp only []
      rw [beqE vw' (vEi (by omega))]
      exact LySL.qw2
    · obtain ⟨ew, vw'⟩ := qword [2, 3] (by decide)
      dsimp only
      rw [ew, get_ofFn (i := 18) (by omega)]
      simp only []
      rw [beqE vw' (vEi (by omega))]
      exact LySL.qw3

theorem facts : sylowCertificate () = true := by
  have hpl : ∀ j < 256, plOK LySy.W LySt.PL 256 j = true := fun j hj => allN_spec LySt.plAll j hj
  have hB := bfs_sound (kg := 6) (c := 256) (cap := 256) (nS := 32) (Hh := 8) (UG := LySy.UG)
    (E := LySy.E) (W := LySy.W) (PL := LySt.PL) (SO := LySy.ST) (SOI := LySy.SIT) (C := LySy.C)
    consts (fun k hk => hv (vUGk hk)) (fun i hi => hv (vEi hi)) (Nat.eq_of_beq_eq_true LySy.e0)
    (by decide) (fun i hi => allN_spec LySy.srt i hi) rfl rfl rfl (Nat.eq_of_beq_eq_true LySy.c0)
    (Nat.eq_of_beq_eq_true LySy.cN) LySy.hrun hpl (Nat.eq_of_beq_eq_true LySt.pl0)
    ⟨us_size, us_get⟩
  have hT := mulTab_sound (n := 256) (MT := LySt.MT) (W := LySy.W) (PL := LySt.PL) (by decide)
    (by decide) hpl
    (fun i hi => chain_atB LySt.rowAll hi)
  have hrows : ∀ i < 256, Nat.blt (LySt.MT i) (Nat.shiftLeft 1 (Nat.mul 8 256)) = true ∧
      ∀ j < 256, tmK LySt.MT i j < 256 := fun i hi => by
    have c : LySt.rowQ i = true := chain_atB LySt.rowAll hi
    unfold LySt.rowQ rowOK at c
    rw [CFSG.KS.Raw.strictB_eq] at c
    exact ⟨(andOf c).1, fun j _ => tm_lt _ _ _⟩
  have hD := derived_sound (n := 256) (nC := LySt.nC) (nD := LySt.nD) (nS := 16) (len := 4096)
    (MT := LySt.MT) (CM := LySt.CM) (DT := LySt.DT) (ST := LySt.ST) (IV := LySt.IV) (by decide)
    (by decide) (fun i hi => (andOf (chain_atB LySt.chkAll hi)).1) hrows rfl
    (Nat.eq_of_beq_eq_true LySt.st0)
    (fun s hs => Nat.eq_of_beq_eq_true (chain_atB LySt.cmAll hs))
    (Nat.eq_of_beq_eq_true LySt.nCk) (Nat.blt_eq.mp LySt.nClt) (Nat.eq_of_beq_eq_true dt0)
    (Nat.eq_of_beq_eq_true LySt.dtOK)
  have e1 := Nat.eq_of_beq_eq_true n1
  have e2 := Nat.eq_of_beq_eq_true n2
  have e3 := Nat.eq_of_beq_eq_true n3
  have e4 := Nat.eq_of_beq_eq_true n4
  have f1 := Nat.le_of_ble_eq_true b1
  have f2 := Nat.le_of_ble_eq_true b2
  have f3 := Nat.le_of_ble_eq_true b3
  have f4 := Nat.le_of_ble_eq_true b4
  rw [lenLL_eq] at e1 e2 e3 e4 f1 f2 f3 f4
  have q : (256 : Nat) ≤ 64 * 4 := by decide
  have E1 := ea_of (L := [[0]]) (L' := LySt.L1) LySt.l0 LySt.ea1All LySt.nm1All (by decide)
    (Nat.le_trans (m := 256) (by omega) q) c1 d1 n1 (by omega)
  have E2 := ea_of (L := LySt.L1) (L' := LySt.L2) LySt.l1 LySt.ea2All LySt.nm2All
    (Nat.le_trans (m := 256) (by omega) q) (Nat.le_trans (m := 256) (by omega) q) c2 d2 n2
    (by omega)
  have E3 := ea_of (L := LySt.L2) (L' := LySt.L3) LySt.l2 LySt.ea3All LySt.nm3All
    (Nat.le_trans (m := 256) (by omega) q) (Nat.le_trans (m := 256) (by omega) q) c3 d3 n3
    (by omega)
  have E4 := ea_of (L := LySt.L3) (L' := LySt.L4) LySt.l3 LySt.ea4All LySt.nm4All
    (Nat.le_trans (m := 256) (by omega) q) (Nat.le_trans (m := 256) (by omega) q) c4 d4 n4
    (Nat.blt_eq.mp b5)
  unfold sylowCertificate
  simp only []
  rw [b4_eq, hB.1]
  have hS := hB.2
  dsimp only [recOf] at hS ⊢
  rw [hT.1, hD, E1.1, E2.1, E3.1, E4.1]
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨⟨?_, LyCvF.invPairs⟩, hS⟩, ?_⟩, hT.2⟩, ?_⟩, local_ok⟩
  · rw [matB_eq, mulE vB vB4, idE, beqE (mulV vB vB4) vOne]
    exact LyCv.bB
  · rw [get_ofFn (i := 6) (by omega)]
    simp only []
    rw [matA_eq, beqE (vEi (by omega)) vA]
    exact e6
  · exact table_sound rfl (fun i hi => chain_atB LySt.chkAll hi)
      (fun i hi => (hrows i hi).2) LySt.dCk LySt.l4eq LySt.e0 LySt.e1 LySt.q E1.2 E2.2 E3.2 E4.2

end CertificateChecks.KernelSporSch.LySyF

end
