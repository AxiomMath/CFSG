
module

public import Certificates.Kernel.SporSch.HN.PtCL
public import Certificates.Kernel.SporSch.HN.Pt2094K
public import Certificates.Kernel.SporSch.HN.Pt2094P1
public import Certificates.Kernel.SporSch.HN.Pt2094P6a
public import Certificates.Kernel.SporSch.HN.Pt2094P6b
public import Certificates.Kernel.SporSch.HN.Pt2094P6c
public import Certificates.Kernel.SporSch.HN.Pt2094P2
public import Certificates.Kernel.SporSch.HN.FixK.P2094G0
public import Certificates.Kernel.SporSch.HN.FixK.P2094G1
public import Certificates.Kernel.SporSch.HN.FixK.P2094G2
public import Certificates.Kernel.SporSch.HN.FixK.Spec
public import CFSG.Certificates.Kernel.SporSch.HNXPtSSound
public import Certificates.Kernel.Sporadic.OddCore.HND0
public import Certificates.Kernel.Sporadic.OddCore.HND2
public import CFSG.Sporadic.HNOddCore.XCheckInputs
public import CFSG.Certificates.Kernel.Spor.RawOrbEval
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelSporSch.HNPt2094

open CFSG.KC.Enum CFSG.KC.LL CFSG.KC.LL.HNX CFSG.KS CFSG.KS.SporSch CFSG.KS.HNArr CFSG.KS.Ord
open CFSG.Sporadic.HNSchreier CFSG.Sporadic.HNSchreier.Native CFSG.ONSchreier.Native
open CFSG.ONSchreier CFSG.Sporadic.HNOddCore CFSG.Sporadic.HNOddCore.Native
open CertificateChecks.KernelSporSch CertificateChecks.KernelSporSch.HNArrS
open CertificateChecks.KernelSporSch.HNPt2103 CertificateChecks.KernelSporSch.HNPtC
open CFSG.KD.HNPt2094 Matrix

local notation "OM" => ordMat 5 133 13 1729

@[expose] def invZ (w : List ℤ) : List ℤ := (w.map fun l => -l).reverse

theorem wJ_append (gs : ℕ → JH) : ∀ u v : List ℤ, wJ gs (u ++ v) = wJ gs u * wJ gs v
  | [], v => by rw [List.nil_append, HNArr.wJ, one_mul]
  | l :: u, v => by rw [List.cons_append, HNArr.wJ, HNArr.wJ, wJ_append gs u v, mul_assoc]

theorem lJ_neg (gs : ℕ → JH) {l : ℤ} (hl : l ≠ 0) : lJ gs (-l) = (lJ gs l)⁻¹ := by
  unfold lJ
  by_cases hp : 0 < l
  · rw [ite_eq_right (by omega), ite_eq_left hp, neg_neg]
  · rw [ite_eq_left (by omega), ite_eq_right hp, inv_inv]

theorem wJ_invZ (gs : ℕ → JH) : ∀ w : List ℤ, (∀ l ∈ w, l ≠ 0) → wJ gs (invZ w) = (wJ gs w)⁻¹
  | [], _ => by rw [invZ, List.map_nil, List.reverse_nil, HNArr.wJ, inv_one]
  | l :: w, hw => by
    have e : invZ (l :: w) = invZ w ++ [-l] := by
      rw [invZ, invZ, List.map_cons, List.reverse_cons]
    rw [e, wJ_append, wJ_invZ gs w fun z hz => hw z (List.mem_cons_of_mem l hz), HNArr.wJ,
      HNArr.wJ, mul_one, lJ_neg gs (hw l List.mem_cons_self), HNArr.wJ, _root_.mul_inv_rev]

@[expose] def seedInv (w : List ℕ) : List ℕ :=
  (w.reverse.map fun l => if l = 1 then [1] else [2, 2]).flatten

theorem seedJ_append : ∀ u v : List ℕ, seedJ (u ++ v) = seedJ u * seedJ v
  | [], v => by rw [List.nil_append, seedJ, one_mul]
  | l :: u, v => by rw [List.cons_append, seedJ, seedJ, seedJ_append u v, mul_assoc]

theorem seedInv_letters (w : List ℕ) : ∀ l ∈ seedInv w, l = 1 ∨ l = 2 := by
  intro l hl
  rw [seedInv, List.mem_flatten] at hl
  obtain ⟨s, hs, hl⟩ := hl
  obtain ⟨a, -, rfl⟩ := List.mem_map.1 hs
  split_ifs at hl <;> simp_all

theorem mulJ_one (g : JH) : g * 1 = g := mul_one g

theorem invJ_of {g h : JH} (e : g * h = 1) : g⁻¹ = h := inv_eq_of_mul_eq_one_right e

theorem seedJ_one (l : ℕ) : seedJ [l] = if l = 1 then aJ else bJ := by
  rw [seedJ, seedJ, mulJ_one]

theorem seedJ_two : seedJ [2, 2] = bJ * bJ := by
  change (if 2 = 1 then aJ else bJ) * seedJ [2] = bJ * bJ
  rw [seedJ_one, ite_eq_right (by decide)]

theorem seed_letter_inv (hA : aJ * aJ = 1) (hB : bJ * (bJ * bJ) = 1) (l : ℕ) :
    (if l = 1 then aJ else bJ)⁻¹ = seedJ (if l = 1 then [1] else [2, 2]) := by
  by_cases h : l = 1
  · rw [ite_eq_left h, ite_eq_left h, seedJ_one, ite_eq_left rfl]
    exact invJ_of hA
  · rw [ite_eq_right h, ite_eq_right h, seedJ_two]
    exact invJ_of hB

theorem seedJ_inv (hA : aJ * aJ = 1) (hB : bJ * (bJ * bJ) = 1) :
    ∀ w : List ℕ, (∀ l ∈ w, l = 1 ∨ l = 2) → (seedJ w)⁻¹ = seedJ (seedInv w)
  | [], _ => by rw [seedJ, inv_one, seedInv, List.reverse_nil, List.map_nil, List.flatten_nil, seedJ]
  | l :: w, hw => by
    have e : seedInv (l :: w) = seedInv w ++ (if l = 1 then [1] else [2, 2]) := by
      rw [seedInv, seedInv, List.reverse_cons, List.map_append, List.flatten_append, List.map_cons,
        List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil]
    rw [e, seedJ_append, ← seedJ_inv hA hB w fun z hz => hw z (List.mem_cons_of_mem l hz), seedJ,
      _root_.mul_inv_rev, seed_letter_inv hA hB l]

@[expose] noncomputable def runProgI : (ℕ → JH) → List (Bool × ℕ × ℕ × ℕ) → ℕ → JH
  | G, [] => G
  | G, (true, a, b, c) :: rest => runProgI (Function.update G c (G a * G b)) rest
  | G, (false, a, b, _) :: rest => runProgI (Function.update G b (G a)⁻¹) rest

@[expose] def progW : (ℕ → List ℕ) → List (Bool × ℕ × ℕ × ℕ) → ℕ → List ℕ
  | ws, [] => ws
  | ws, (true, a, b, c) :: rest => progW (Function.update ws c (ws a ++ ws b)) rest
  | ws, (false, a, b, _) :: rest => progW (Function.update ws b (seedInv (ws a))) rest

theorem progRun_false_snd (n : ℕ) (regs : Array (Array ℕ)) (a b d : ℕ)
    (rest : List (Bool × ℕ × ℕ × ℕ)) :
    (progRun n regs ((false, a, b, d) :: rest)).2 =
      (pisInv n regs[a]! (pinvCand n regs[a]!) &&
        (progRun n (regs.set! b (pinvCand n regs[a]!)) rest).2) := by
  rw [progRun]

theorem progRun_false_fst (n : ℕ) (regs : Array (Array ℕ)) (a b d : ℕ)
    (rest : List (Bool × ℕ × ℕ × ℕ)) :
    (progRun n regs ((false, a, b, d) :: rest)).1 =
      (progRun n (regs.set! b (pinvCand n regs[a]!)) rest).1 := by
  rw [progRun]

theorem progRun_arrJ : ∀ (prog : List (Bool × ℕ × ℕ × ℕ)) (regs : Array (Array ℕ)) (G : ℕ → JH),
    (∀ t ∈ prog, t.2.1 < 11 ∧ t.2.2.1 < 11 ∧ t.2.2.2 < 11) → regs.size = 11 →
    (∀ k < 11, regs[k]! = arrJ (G k)) →
      (progRun nPts regs prog).2 = true ∧
        ∀ k < 11, (progRun nPts regs prog).1[k]! = arrJ (runProgI G prog k)
  | [], regs, G, _, _, hg => by
    rw [progRun, runProgI]
    exact ⟨rfl, hg⟩
  | (true, a, b, c) :: rest, regs, G, hp, hs, hg => by
    obtain ⟨ha, hb, hc⟩ := hp _ List.mem_cons_self
    rw [progRun, runProgI]
    refine progRun_arrJ rest _ _ (fun t ht => hp t (List.mem_cons_of_mem _ ht)) (by simp [hs])
      fun k hk => ?_
    rw [Array.set!_eq_setIfInBounds, getElem!_pos _ k (by simp [hs]; exact hk),
      Array.getElem_setIfInBounds (by simp [hs]; exact hk)]
    by_cases e : c = k
    · subst e
      rw [ite_eq_left rfl, Function.update_self, hg a ha, hg b hb, pcomp_arrJ]
    · rw [ite_eq_right e, Function.update_of_ne (Ne.symm e), ← getElem!_pos regs k (by omega),
        hg k hk]
  | (false, a, b, d) :: rest, regs, G, hp, hs, hg => by
    obtain ⟨ha, hb, -⟩ := hp _ List.mem_cons_self
    have ih := progRun_arrJ rest (regs.set! b (pinvCand nPts regs[a]!)) (Function.update G b (G a)⁻¹)
      (fun t ht => hp t (List.mem_cons_of_mem _ ht)) (by simp [hs]) fun k hk => by
        rw [Array.set!_eq_setIfInBounds, getElem!_pos _ k (by simp [hs]; exact hk),
          Array.getElem_setIfInBounds (by simp [hs]; exact hk)]
        by_cases e : b = k
        · subst e
          rw [ite_eq_left rfl, Function.update_self, hg a ha, pinvCand_arrJ]
        · rw [ite_eq_right e, Function.update_of_ne (Ne.symm e), ← getElem!_pos regs k (by omega),
            hg k hk]
    refine ⟨?_, ?_⟩
    · rw [progRun_false_snd, ih.1, hg a ha, pinvCand_arrJ, pisInv_arrJ]
      rfl
    · rw [progRun_false_fst, runProgI]
      exact ih.2

theorem runProgI_seed (hA : aJ * aJ = 1) (hB : bJ * (bJ * bJ) = 1) :
    ∀ (prog : List (Bool × ℕ × ℕ × ℕ)) (G : ℕ → JH) (ws : ℕ → List ℕ),
    (∀ k, G k = seedJ (ws k) ∧ ∀ l ∈ ws k, l = 1 ∨ l = 2) →
      ∀ k, runProgI G prog k = seedJ (progW ws prog k) ∧ ∀ l ∈ progW ws prog k, l = 1 ∨ l = 2
  | [], _, _, h => h
  | (true, a, b, c) :: rest, G, ws, h => by
    rw [runProgI, progW]
    refine runProgI_seed hA hB rest _ _ fun k => ?_
    by_cases e : k = c
    · subst e
      rw [Function.update_self, Function.update_self, (h a).1, (h b).1, seedJ_append]
      refine ⟨rfl, fun l hl => ?_⟩
      rcases List.mem_append.1 hl with hl | hl
      · exact (h a).2 l hl
      · exact (h b).2 l hl
    · rw [Function.update_of_ne e, Function.update_of_ne e]
      exact h k
  | (false, a, b, _) :: rest, G, ws, h => by
    rw [runProgI, progW]
    refine runProgI_seed hA hB rest _ _ fun k => ?_
    by_cases e : k = b
    · subst e
      rw [Function.update_self, Function.update_self, (h a).1, seedJ_inv hA hB _ (h a).2]
      exact ⟨rfl, seedInv_letters _⟩
    · rw [Function.update_of_ne e, Function.update_of_ne e]
      exact h k

@[expose] def initW (k : ℕ) : List ℕ := if k = 1 then [1] else if k = 2 then [2] else []

theorem initW_eq (k : ℕ) : seedJ (initW k) = if k = 1 then aJ else if k = 2 then bJ else 1 := by
  unfold initW
  split_ifs with h1 h2
  · exact (seedJ_one 1).trans (ite_eq_left rfl)
  · exact (seedJ_one 2).trans (ite_eq_right (by decide))
  · rfl

theorem initW_letters (k : ℕ) : ∀ l ∈ initW k, l = 1 ∨ l = 2 := by
  intro l hl
  unfold initW at hl
  split_ifs at hl
  · exact Or.inl (List.mem_singleton.1 hl)
  · exact Or.inr (List.mem_singleton.1 hl)
  · exact absurd hl List.not_mem_nil

theorem initJ_seed (k : ℕ) : initJ k = seedJ (initW k) ∧ ∀ l ∈ initW k, l = 1 ∨ l = 2 :=
  ⟨(initW_eq k).symm, initW_letters k⟩

@[expose] noncomputable def elR
    (k : ℕ) : RH :=
  if k = 0 then cR else jR ((ecF k).map genJ).prod

theorem ec_lt : ∀ k < 40, ∀ c ∈ ecF (k + 1), c < 36 := by decide +kernel

theorem EL_mat {k : ℕ} (hk : k < 41) :
    Canon 5 133 13 (EL k) ∧ OM (EL k) = matR (elR k) := by
  rcases Nat.eq_zero_or_pos k with rfl | hpos
  · rw [Nat.eq_of_beq_eq_true e_EL0, elR, ite_eq_left rfl]
    refine ⟨GT_canon (by norm_num), ?_⟩
    rw [genR_mat (by norm_num), genR, ite_eq_right (by norm_num), ite_eq_right (by norm_num)]
  · obtain ⟨K, rfl⟩ : ∃ K, k = K + 1 := ⟨k - 1, by omega⟩
    have e : wordC CFSG.KD.HNPt.R (ecF (K + 1)) = EL (K + 1) :=
      Nat.eq_of_beq_eq_true (allN_spec w_EL K (by omega))
    rw [← e, elR, ite_eq_right (by omega), matR_jR]
    exact mat_word (ec_lt K (by omega))

theorem TT_eq {k : ℕ} (hk : k < 41) : trM (EL k) = TT k :=
  Nat.eq_of_beq_eq_true (allN_spec t_TT k hk)

theorem elR_word {k : ℕ} (hk : 0 < k)
    {w : List ℤ} (hc : ecF k = w.map scode) (hw : ∀ l ∈ w, l ≠ 0 ∧ l.natAbs ≤ 17) :
    elR k = jR (wJ sL w) := by
  rw [elR, ite_eq_right (by omega), hc, prod_scode _ hw]

theorem codes_ok : (∀ j < 9, ecF (1 + j) = InvData.c1Words[j]!.map scode ∧
      ∀ l ∈ InvData.c1Words[j]!, l ≠ 0 ∧ l.natAbs ≤ 17) ∧
    (∀ j < 9, ecF (10 + j) = InvData.c4Words[j]!.map scode) ∧
    ecF 19 = InvData.x4Root.map (33 + ·) ++ InvData.x4H.map scode ∧
    ecF 20 = InvData.t4Word.map scode ∧ ecF 21 = [34] ∧
    (∀ j < 10, ecF (22 + j) = InvData.c6Words[j]!.map scode ∧
      ∀ l ∈ InvData.c6Words[j]!, l ≠ 0 ∧ l.natAbs ≤ 17) ∧
    ecF 34 = InvData.t2Word.map scode ∧ (∀ l ∈ InvData.t2Word, l ≠ 0 ∧ l.natAbs ≤ 17) ∧
    (∀ j < 6, ecF (35 + j) = InvData.a8Words[j]!.map scode ∧
      ∀ l ∈ InvData.a8Words[j]!, l ≠ 0 ∧ l.natAbs ≤ 17) ∧
    InvData.c1Words.size = 9 ∧ InvData.c6Words.size = 10 ∧ InvData.a8Words.size = 6 := by
  decide +kernel

theorem codes_e : (∀ i < 2, ecF (32 + i) = (invZ InvData.m2ConjH).map scode ++
      (seedInv InvData.m2ConjRoot ++ progW initW InvData.m2Prog (1 + i) ++
        InvData.m2ConjRoot).map (33 + ·) ++ InvData.m2ConjH.map scode) ∧
    (∀ l ∈ invZ InvData.m2ConjH, l ≠ 0 ∧ l.natAbs ≤ 17) ∧
    (∀ l ∈ InvData.m2ConjH, l ≠ 0 ∧ l.natAbs ≤ 17) ∧
    (∀ l ∈ InvData.m2ConjRoot, l = 1 ∨ l = 2) ∧
    (∀ t ∈ InvData.m2Prog, t.2.1 < 11 ∧ t.2.2.1 < 11 ∧ t.2.2.2 < 11) := by
  decide +kernel

theorem seeds_J : aJ * aJ = 1 ∧ bJ * (bJ * bJ) = 1 := by
  have cA := R_canon (c := 34) (by norm_num)
  have cB := R_canon (c := 35) (by norm_num)
  have mA := R_mat (c := 34) (by norm_num)
  have mB := R_mat (c := 35) (by norm_num)
  rw [genJ, ite_eq_right (by norm_num), ite_eq_right (by norm_num), ite_eq_left rfl] at mA
  rw [genJ, ite_eq_right (by norm_num), ite_eq_right (by norm_num),
    ite_eq_right (by norm_num)] at mB
  have e1 := congrArg OM (Nat.eq_of_beq_eq_true seeds.1)
  have e2 := congrArg OM (Nat.eq_of_beq_eq_true seeds.2)
  rw [(HNXP.mm_sound cA cA).2, mA, HNXP.one_ord, ← HNArr.matJ_mul] at e1
  rw [(HNXP.mm_sound cB (HNXP.mm_sound cB cB).1).2, (HNXP.mm_sound cB cB).2, mB, HNXP.one_ord,
    ← HNArr.matJ_mul, ← HNArr.matJ_mul] at e2
  exact ⟨matJ_injective (e1.trans HNArr.matJ_one.symm),
    matJ_injective (e2.trans HNArr.matJ_one.symm)⟩

noncomputable abbrev regJ (i : ℕ) : JH := runProgI initJ InvData.m2Prog i

noncomputable abbrev gJ : JH := seedJ InvData.m2ConjRoot * wJ sL InvData.m2ConjH

theorem elR_e {i : ℕ} (hi : i < 2) :
    elR (32 + i) = jR (gJ⁻¹ * (regJ (1 + i) * gJ)) := by
  obtain ⟨c1, c2, c3, c4, -⟩ := codes_e
  obtain ⟨hA, hB⟩ := seeds_J
  obtain ⟨hr, hl⟩ := runProgI_seed hA hB InvData.m2Prog initJ initW initJ_seed (1 + i)
  have hB' : ∀ l ∈ seedInv InvData.m2ConjRoot ++ progW initW InvData.m2Prog (1 + i) ++
      InvData.m2ConjRoot, l = 1 ∨ l = 2 := fun l h => by
    rcases List.mem_append.1 h with h | h
    · rcases List.mem_append.1 h with h | h
      · exact seedInv_letters _ l h
      · exact hl l h
    · exact c4 l h
  have p1 : (((invZ InvData.m2ConjH).map scode).map genJ).prod = (wJ sL InvData.m2ConjH)⁻¹ := by
    rw [prod_scode _ c2, wJ_invZ _ _ fun l hl => (c3 l hl).1]
  have p2 : (((seedInv InvData.m2ConjRoot ++ progW initW InvData.m2Prog (1 + i) ++
      InvData.m2ConjRoot).map (33 + ·)).map genJ).prod =
      (seedJ InvData.m2ConjRoot)⁻¹ * (regJ (1 + i) * seedJ InvData.m2ConjRoot) := by
    rw [prod_seed _ hB', seedJ_append, seedJ_append, ← seedJ_inv hA hB _ c4, ← hr, mul_assoc]
  have p3 : ((InvData.m2ConjH.map scode).map genJ).prod = wJ sL InvData.m2ConjH :=
    prod_scode _ c3
  rw [elR, ite_eq_right (by omega), c1 i hi,
    List.map_append (f := genJ) (l₁ := (invZ InvData.m2ConjH).map scode ++
      (seedInv InvData.m2ConjRoot ++ progW initW InvData.m2Prog (1 + i) ++
        InvData.m2ConjRoot).map (33 + ·)) (l₂ := InvData.m2ConjH.map scode),
    List.map_append (f := genJ) (l₁ := (invZ InvData.m2ConjH).map scode)
      (l₂ := (seedInv InvData.m2ConjRoot ++ progW initW InvData.m2Prog (1 + i) ++
        InvData.m2ConjRoot).map (33 + ·)),
    List.prod_append, List.prod_append, p1, p2, p3]
  simp only [_root_.mul_inv_rev, mul_assoc]

structure ListData (F : Array ℕ) (N P : ℕ) : Prop where
  size : F.size = N
  fld : ∀ k < N, fldW P (21 * k) 21 = F[k]!
  lt : ∀ k < N, F[k]! < nPts
  sorted : (F.toList.zip F.toList.tail).all (fun p => decide (p.1 < p.2)) = true

theorem listData_of {F : Array ℕ} {N P : ℕ} (hp : HNXP.packW 21 F.toList = P)
    (hb : F.toList.all (fun x => decide (x < 1140000)) = true)
    (hs : (F.toList.zip F.toList.tail).all (fun p => decide (p.1 < p.2)) = true)
    (hN : F.size = N) : ListData F N P := by
  have hb' : ∀ x ∈ F.toList, x < 1140000 := fun x hx => of_decide_eq_true (List.all_eq_true.1 hb x hx)
  refine ⟨hN, fun k hk => ?_, fun k hk => ?_, hs⟩
  · rw [← hp, HNXP.fld_packW (fun x hx => lt_trans (hb' x hx) (by norm_num))
      (by rw [Array.length_toList]; omega), HNXP.arr_get_toList]
  · rw [HNXP.arr_get_toList, getElem!_pos F.toList k (by rw [Array.length_toList]; omega)]
    exact hb' _ (List.getElem_mem _)

theorem posData {s : Array ℕ} {N S : ℕ} (hS : HNXP.packW 14 s.toList = S)
    (hb : s.toList.all (fun x => decide (x < N)) = true) (hN : N ≤ 16384) (hs : s.size = N) :
    ∀ k < N, fldW S (14 * k) 14 = s[k]! ∧ s[k]! < N := by
  have hb' : ∀ x ∈ s.toList, x < N := fun x hx => of_decide_eq_true (List.all_eq_true.1 hb x hx)
  intro k hk
  rw [← hS, HNXP.fld_packW (fun x hx => lt_of_lt_of_le (hb' x hx) (by norm_num; omega))
    (by rw [Array.length_toList]; omega), HNXP.arr_get_toList]
  refine ⟨rfl, ?_⟩
  rw [getElem!_pos s.toList k (by rw [Array.length_toList]; omega)]
  exact hb' _ (List.getElem_mem _)

theorem restrict_row {F : Array ℕ}
    {N P : ℕ} (hF : ListData F N P) {s : Array ℕ} {S : ℕ}
    (hS : ∀ k < N, fldW S (14 * k) 14 = s[k]! ∧ s[k]! < N) {t : Array ℕ} {r : RH} {W TW nc : ℕ}
    (ht : PRep hnsData.n t (permR r)) (hW : Canon 5 133 13 W) (hm : OM W = matR r)
    (hT : trM W = TW) (hN : N ≤ 64 * nc)
    (h : allN nc (fun m => ptsImg CFSG.KD.LgHNX.TX CFSG.KD.LgHNX.MS CFSG.KD.LgHNX.CM3
      CFSG.KD.LgHNX.M TW (sliceP P m) (imgP P S m (cntP N m)) (cntP N m)) = true) :
    restrictOK t F (posArr nPts F) s = true := by
  refine restrictOK_of (fun i hi => hF.lt i (by rw [← hF.size]; exact hi)) hF.sorted
    fun k hk => ?_
  rw [hF.size] at hk
  obtain ⟨e1, e2⟩ := hS k hk
  refine ⟨by rw [hF.size]; exact e2, ?_⟩
  have h1 : fldW P (21 * k) 21 < nPts := by rw [hF.fld k hk]; exact hF.lt k hk
  have h2 : fldW P (21 * fldW S (14 * k) 14) 21 < nPts := by
    rw [e1, hF.fld _ e2]; exact hF.lt _ e2
  have := chunk_perm hW hm hT hN h hk h1 h2
  rw [e1, hF.fld _ e2] at this
  rw [ht.apply (hF.lt k hk), permR_apply]
  have e : (⟨F[k]!, hF.lt k hk⟩ : X) = ⟨fldW P (21 * k) 21, h1⟩ := Fin.ext (hF.fld k hk).symm
  rw [e]
  exact this

theorem fix_pts {F : Array ℕ}
    {N P : ℕ} (hF : ListData F N P) {t : Array ℕ} {r : RH} {W TW nc : ℕ}
    (ht : PRep hnsData.n t (permR r)) (hW : Canon 5 133 13 W) (hm : OM W = matR r)
    (hT : trM W = TW) (hN : N ≤ 64 * nc)
    (h : allN nc (fun m => ptsImg CFSG.KD.LgHNX.TX CFSG.KD.LgHNX.MS CFSG.KD.LgHNX.CM3
      CFSG.KD.LgHNX.M TW (sliceP P m) (sliceP P m) (cntP N m)) = true) {k : ℕ} (hk : k < N) :
    t[F[k]!]! = F[k]! := by
  have h1 : fldW P (21 * k) 21 < nPts := by rw [hF.fld k hk]; exact hF.lt k hk
  have := chunk_list hW hm hT hN h hk h1 h1
  rw [ht.apply (hF.lt k hk), permR_apply]
  have e : (⟨F[k]!, hF.lt k hk⟩ : X) = ⟨fldW P (21 * k) 21, h1⟩ := Fin.ext (hF.fld k hk).symm
  rw [e, this, hF.fld k hk]

theorem fix_row {F : Array ℕ}
    {N P : ℕ} (hF : ListData F N P) {t : Array ℕ} {r : RH} {W TW nc G : ℕ}
    (ht : PRep hnsData.n t (permR r)) (hW : Canon 5 133 13 W) (hm : OM W = matR r)
    (hT : trM W = TW) (hN : N ≤ 64 * nc)
    (h : allN nc (fun m => ptsImg CFSG.KD.LgHNX.TX CFSG.KD.LgHNX.MS CFSG.KD.LgHNX.CM3
      CFSG.KD.LgHNX.M TW (sliceP P m) (sliceP P m) (cntP N m)) = true)
    (hG : trM (CFSG.KC.LL.HN.subI W) = G)
    (hs : ∑ b ∈ Finset.range 17813, fixLeaf CFSG.KD.LgHNX.TX 464 CFSG.KD.LgHNX.CM3
      CFSG.KD.LgHNX.M [G] b (hnxC b) = N) :
    fixListOK nPts t F.toList = true := by
  refine fixListOK_of hF.sorted (fun x hx => ?_) (by rw [countP_fix ht hW hm hG hs,
    Array.length_toList, hF.size])
  obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 hx
  rw [Array.length_toList, hF.size] at hk
  rw [← getElem!_pos F.toList k (by rw [Array.length_toList, hF.size]; exact hk),
    ← HNXP.arr_get_toList]
  exact ⟨hF.lt k hk, fix_pts hF ht hW hm hT hN h hk⟩

theorem data1 : ListData InvData.f1Arr 1156 PL1 ∧ ListData InvData.f4Arr 800 PL4 := by
  have h : (HNXP.packW 21 InvData.f1Arr.toList = PL1 ∧
      InvData.f1Arr.toList.all (fun x => decide (x < 1140000)) = true ∧
      (InvData.f1Arr.toList.zip InvData.f1Arr.toList.tail).all (fun p => decide (p.1 < p.2)) =
        true ∧ InvData.f1Arr.size = 1156) ∧
      (HNXP.packW 21 InvData.f4Arr.toList = PL4 ∧
      InvData.f4Arr.toList.all (fun x => decide (x < 1140000)) = true ∧
      (InvData.f4Arr.toList.zip InvData.f4Arr.toList.tail).all (fun p => decide (p.1 < p.2)) =
        true ∧ InvData.f4Arr.size = 800) := by
    rw [CertificateChecks.KernelSpor.HND.f1Arr_eq, CertificateChecks.KernelSpor.HND.f4Arr_eq]
    decide +kernel
  exact ⟨listData_of h.1.1 h.1.2.1 h.1.2.2.1 h.1.2.2.2, listData_of h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2⟩

theorem data6 : ListData InvData.f6Arr 8800 PL6 := by
  have h : HNXP.packW 21 InvData.f6Arr.toList = PL6 ∧
      InvData.f6Arr.toList.all (fun x => decide (x < 1140000)) = true ∧
      (InvData.f6Arr.toList.zip InvData.f6Arr.toList.tail).all (fun p => decide (p.1 < p.2)) =
        true ∧ InvData.f6Arr.size = 8800 := by
    rw [CertificateChecks.KernelSpor.HND.f6Arr_eq]
    decide +kernel
  exact listData_of h.1 h.2.1 h.2.2.1 h.2.2.2

@[expose] noncomputable def pk14R (L : List ℕ) : ℕ :=
  List.rec (motive := fun _ => ℕ) 0 (fun x _ ih => Nat.add x (Nat.mul 16384 ih)) L

@[expose] noncomputable def ltAllR (N : ℕ) (L : List ℕ) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun x _ ih => and (Nat.blt x N) ih) L

@[expose] noncomputable def len94R {α : Type} (L : List α) : ℕ :=
  List.rec (motive := fun _ => ℕ) 0 (fun _ _ ih => Nat.succ ih) L

@[expose] noncomputable def spChkR (N : ℕ) (SP : ℕ → ℕ) (E : List (List ℕ)) : ℕ → Bool :=
  List.rec (motive := fun _ => ℕ → Bool) (fun _ => true)
    (fun L _ ih j => and (and (Nat.beq (pk14R L) (SP j)) (ltAllR N L))
      (and (Nat.beq (len94R L) N) (ih (Nat.succ j)))) E

theorem pk14R_eq : ∀ L : List ℕ, pk14R L = HNXP.packW 14 L
  | [] => rfl
  | x :: L => by
    change Nat.add x (Nat.mul 16384 (pk14R L)) = x + 2 ^ 14 * HNXP.packW 14 L
    rw [pk14R_eq L]
    rfl

theorem ltAllR_spec {N : ℕ} : ∀ {L : List ℕ}, ltAllR N L = true →
    L.all (fun x => decide (x < N)) = true
  | [], _ => rfl
  | x :: L, h => by
    have h' : (Nat.blt x N && ltAllR N L) = true := h
    rw [Bool.and_eq_true, Nat.blt_eq] at h'
    rw [List.all_cons, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨h'.1, ltAllR_spec h'.2⟩

theorem len94R_eq {α : Type} : ∀ L : List α, len94R L = L.length
  | [] => rfl
  | _ :: L => by
    change Nat.succ (len94R L) = _
    rw [len94R_eq L, List.length_cons]

theorem spChkR_spec {N : ℕ} {SP : ℕ → ℕ} : ∀ {E : List (List ℕ)} {j : ℕ}, spChkR N SP E j = true →
    ∀ i < E.length, HNXP.packW 14 E[i]! = SP (j + i) ∧
      E[i]!.all (fun x => decide (x < N)) = true ∧ E[i]!.length = N
  | [], _, _, i, hi => absurd hi (Nat.not_lt_zero _)
  | L :: E, j, h, i, hi => by
    have h' : ((Nat.beq (pk14R L) (SP j) && ltAllR N L) &&
        (Nat.beq (len94R L) N && spChkR N SP E (Nat.succ j))) = true := h
    simp only [Bool.and_eq_true, Nat.beq_eq] at h'
    obtain ⟨⟨h1, h2⟩, h3, h4⟩ := h'
    rcases i with _ | i
    · rw [List.getElem!_cons_zero, ← pk14R_eq, ← len94R_eq, Nat.add_zero]
      exact ⟨h1, ltAllR_spec h2, h3⟩
    · rw [List.getElem!_cons_succ, show j + (i + 1) = Nat.succ j + i by omega]
      exact spChkR_spec h4 i (by simpa using hi)

theorem sdata_of {A : Array (Array ℕ)} {E : List (List ℕ)} {n N : ℕ} {SP : ℕ → ℕ}
    (hA : A = (E.map List.toArray).toArray) (hn : Nat.beq (len94R E) n = true)
    (h : spChkR N SP E 0 = true) :
    A.size = n ∧ ∀ j < n, HNXP.packW 14 (A[j]!).toList = SP j ∧
      (A[j]!).toList.all (fun x => decide (x < N)) = true ∧ (A[j]!).size = N := by
  subst hA
  have hn' : E.length = n := by rw [← len94R_eq]; exact Nat.eq_of_beq_eq_true hn
  subst hn'
  refine ⟨by simp, fun j hj => ?_⟩
  have e : (E.map List.toArray).toArray[j]! = (E[j]!).toArray := by
    rw [getElem!_pos _ j (by simpa using hj), List.getElem_toArray, List.getElem_map,
      getElem!_pos E j hj]
  obtain ⟨h1, h2, h3⟩ := spChkR_spec h j hj
  rw [e, List.toList_toArray, List.size_toArray]
  rw [Nat.zero_add] at h1
  exact ⟨h1, h2, h3⟩

theorem sdata1 : InvData.s1Perms.size = 9 ∧ ∀ j < 9,
    HNXP.packW 14 (InvData.s1Perms[j]!).toList = SP1 j ∧
    (InvData.s1Perms[j]!).toList.all (fun x => decide (x < 1156)) = true ∧
    (InvData.s1Perms[j]!).size = 1156 :=
  sdata_of CertificateChecks.KernelSpor.HND.s1_eq (by quickRfl) (by quickRfl)

theorem sdata4 : InvData.s4Perms.size = 11 ∧ ∀ j < 11,
    HNXP.packW 14 (InvData.s4Perms[j]!).toList = SP4 j ∧
    (InvData.s4Perms[j]!).toList.all (fun x => decide (x < 800)) = true ∧
    (InvData.s4Perms[j]!).size = 800 :=
  sdata_of CertificateChecks.KernelSpor.HND.s4_eq (by quickRfl) (by quickRfl)

theorem sdata6 : InvData.s6Perms.size = 12 ∧ ∀ j < 12,
    HNXP.packW 14 (InvData.s6Perms[j]!).toList = SP6 j ∧
    (InvData.s6Perms[j]!).toList.all (fun x => decide (x < 8800)) = true ∧
    (InvData.s6Perms[j]!).size = 8800 :=
  sdata_of CertificateChecks.KernelSpor.HND.s6_eq (by quickRfl) (by quickRfl)

theorem sd1 {j : ℕ} (hj : j < 9) : ∀ k < 1156,
    fldW (SP1 j) (14 * k) 14 = (InvData.s1Perms[j]!)[k]! ∧ (InvData.s1Perms[j]!)[k]! < 1156 :=
  posData (sdata1.2 j hj).1 (sdata1.2 j hj).2.1 (by norm_num) (sdata1.2 j hj).2.2

theorem sd4 {j : ℕ} (hj : j < 11) : ∀ k < 800,
    fldW (SP4 j) (14 * k) 14 = (InvData.s4Perms[j]!)[k]! ∧ (InvData.s4Perms[j]!)[k]! < 800 :=
  posData (sdata4.2 j hj).1 (sdata4.2 j hj).2.1 (by norm_num) (sdata4.2 j hj).2.2

theorem sd6 {j : ℕ} (hj : j < 12) : ∀ k < 8800,
    fldW (SP6 j) (14 * k) 14 = (InvData.s6Perms[j]!)[k]! ∧ (InvData.s6Perms[j]!)[k]! < 8800 :=
  posData (sdata6.2 j hj).1 (sdata6.2 j hj).2.1 (by norm_num) (sdata6.2 j hj).2.2

theorem fixS_spec {Vm G W J GO SC SD : ℕ} {V : ℕ → ℕ} {m : ℕ} (hV : Canon 5 133 13 Vm)
    (hG : trM Vm = G) (hp : sPreOK CFSG.KD.LgHNX.CM3 Vm W J GO SC SD = true) {k : ℕ}
    (h : CFSG.KD.HNXK.fixOkS G W J GO V m k = true) :
    Nat.beq (fixSum CFSG.KD.LgHNX.TX CFSG.KD.LgHNX.CM3 CFSG.KD.LgHNX.M G (2227 * k)
      (CFSG.KD.HNXK.fixLen k)) (V (8 * m + k)) = true := by
  subst hG
  unfold CFSG.KD.HNXK.fixOkS at h
  rwa [HNXP.fixSumS_eq consts_parts.1 hV (HNXP.sLane_of_ok consts_parts.1 hV hp)] at h

theorem fixSR_spec {Vm G W J GO SC SD lo n v : ℕ} (hV : Canon 5 133 13 Vm)
    (hG : trM Vm = G) (hp : sPreOK CFSG.KD.LgHNX.CM3 Vm W J GO SC SD = true)
    (h : CFSG.KD.HNXK.fixOkR G W J GO lo n v = true) :
    Nat.beq (fixSum CFSG.KD.LgHNX.TX CFSG.KD.LgHNX.CM3 CFSG.KD.LgHNX.M G lo n) v = true := by
  subst hG
  unfold CFSG.KD.HNXK.fixOkR at h
  rwa [HNXP.fixSumS_eq consts_parts.1 hV (HNXP.sLane_of_ok consts_parts.1 hV hp)] at h

theorem fixSum_split {T : ℕ → ℕ} {CM3 M G lo a lo' b u v : ℕ}
    (h1 : Nat.beq (fixSum T CM3 M G lo a) u = true) (h2 : Nat.beq (fixSum T CM3 M G lo' b) v = true)
    (hl : lo + a = lo') : Nat.beq (fixSum T CM3 M G lo (a + b)) (u + v) = true := by
  subst hl
  have e : fixSum T CM3 M G lo (a + b) = u + v := by
    rw [← Nat.eq_of_beq_eq_true h1, ← Nat.eq_of_beq_eq_true h2, HNXP.fixSum_eq, HNXP.fixSum_eq,
      HNXP.fixSum_eq, Finset.sum_range_add]
    simp only [Nat.add_assoc]
  rw [e]
  exact Nat.beq_refl _

theorem subEL_canon {k : ℕ} (hk : k < 41) : Canon 5 133 13 (CFSG.KC.LL.HN.subI (EL k)) :=
  (subI_mat (EL_mat hk).1).1

open CFSG.KD.HNXK in
theorem sum_c : ∑ b ∈ Finset.range 17813, fixLeaf CFSG.KD.LgHNX.TX 464 CFSG.KD.LgHNX.CM3
    CFSG.KD.LgHNX.M [GC] b (hnxC b) = 1156 := by
  have hV := subEL_canon (k := 0) (by norm_num)
  have hG := Nat.eq_of_beq_eq_true g_fix.1
  exact (total8' (fixS_spec hV hG pre2094_0 F2094_0.c0) (fixS_spec hV hG pre2094_0 F2094_0.c1)
    (fixS_spec hV hG pre2094_0 F2094_0.c2) (fixS_spec hV hG pre2094_0 F2094_0.c3)
    (fixS_spec hV hG pre2094_0 F2094_0.c4) (fixS_spec hV hG pre2094_0 F2094_0.c5)
    (fixS_spec hV hG pre2094_0 F2094_0.c6) (fixS_spec hV hG pre2094_0 F2094_0.c7)).trans
    (by decide +kernel)

open CFSG.KD.HNXK in
theorem sum_4 : ∑ b ∈ Finset.range 17813, fixLeaf CFSG.KD.LgHNX.TX 464 CFSG.KD.LgHNX.CM3
    CFSG.KD.LgHNX.M [G4] b (hnxC b) = 800 := by
  have hV := subEL_canon (k := 20) (by norm_num)
  have hG := Nat.eq_of_beq_eq_true g_fix.2.1
  exact (total8' (fixS_spec hV hG pre2094_1 F2094_1.c0) (fixS_spec hV hG pre2094_1 F2094_1.c1)
    (fixS_spec hV hG pre2094_1 F2094_1.c2) (fixS_spec hV hG pre2094_1 F2094_1.c3)
    (fixS_spec hV hG pre2094_1 F2094_1.c4) (fixS_spec hV hG pre2094_1 F2094_1.c5)
    (fixS_spec hV hG pre2094_1 F2094_1.c6) (fixS_spec hV hG pre2094_1 F2094_1.c7)).trans
    (by decide +kernel)

open CFSG.KD.HNXK in
theorem sum_A : ∑ b ∈ Finset.range 17813, fixLeaf CFSG.KD.LgHNX.TX 464 CFSG.KD.LgHNX.CM3
    CFSG.KD.LgHNX.M [GA] b (hnxC b) = 8800 := by
  have hV := subEL_canon (k := 21) (by norm_num)
  have hG := Nat.eq_of_beq_eq_true g_fix.2.2.1
  exact (total8' (fixS_spec hV hG pre2094_2 F2094_2.c0) (fixS_spec hV hG pre2094_2 F2094_2.c1)
    (fixS_spec hV hG pre2094_2 F2094_2.c2) (fixS_spec hV hG pre2094_2 F2094_2.c3)
    (fixS_spec hV hG pre2094_2 F2094_2.c4) (fixS_spec hV hG pre2094_2 F2094_2.c5)
    (fixS_spec hV hG pre2094_2 F2094_2.c6) (fixSum_split
      (fixSR_spec hV hG pre2094_2 F2094_2T.c0) (fixSR_spec hV hG pre2094_2 F2094_2T.c1) rfl)).trans
    (by decide +kernel)

theorem prep_el {k : ℕ} {g : JH}
    (he : elR k = jR g) : PRep hnsData.n (arrJ g) (permR (elR k)) := by
  rw [he]
  exact prep_arrJ g

theorem prep_c :
    PRep hnsData.n cRec (permR (elR 0)) := by
  rw [elR, ite_eq_left rfl]
  exact HNCTab.prep_cRec'

theorem comm_of {k1 k2 : ℕ}
    {g1 g2 : JH} (hk1 : k1 < 41) (hk2 : k2 < 41) (h1 : elR k1 = jR g1) (h2 : elR k2 = jR g2)
    (hc : Nat.beq (CFSG.KC.LL.HN.mm (EL k1) (EL k2)) (CFSG.KC.LL.HN.mm (EL k2) (EL k1)) = true) :
    g1 * g2 = g2 * g1 := by
  obtain ⟨c1, m1⟩ := EL_mat hk1
  obtain ⟨c2, m2⟩ := EL_mat hk2
  have e := congrArg OM (Nat.eq_of_beq_eq_true hc)
  rw [(HNXP.mm_sound c1 c2).2, (HNXP.mm_sound c2 c1).2, m1, m2, h1, h2, matR_jR, matR_jR,
    ← HNArr.matJ_mul, ← HNArr.matJ_mul] at e
  exact matJ_injective e

theorem el_c4 {j : ℕ} (hj : j < 9) :
    elR (10 + j) = jR (c4J j) :=
  elR_word (by omega) (codes_ok.2.1 j hj) (letters_c4.2.1 j hj)

theorem el_x4 :
    elR 19 = jR x4J := by
  rw [elR, ite_eq_right (by norm_num), codes_ok.2.2.1, List.map_append, List.prod_append,
    prod_seed _ letters_c4.2.2.2.1, prod_scode _ letters_c4.2.2.1]

theorem el_t4 :
    elR 20 = jR t4J :=
  elR_word (by norm_num) codes_ok.2.2.2.1 letters_c4.2.2.2.2

theorem genJ_34 : genJ 34 = aJ := by
  unfold genJ
  rw [ite_eq_right (by norm_num), ite_eq_right (by norm_num)]
  exact ite_eq_left rfl

theorem el_A : elR 21 = jR aJ := by
  have e : ((ecF 21).map genJ).prod = aJ := by
    rw [codes_ok.2.2.2.2.1, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mulJ_one,
      genJ_34]
  rw [elR, ite_eq_right (by norm_num), e]

theorem row1_ok :
    row1OK nPts SJ (pinvs nPts SJ) cRec (posArr nPts InvData.f1Arr) = true := by
  obtain ⟨d1, -⟩ := data1
  have m0 := EL_mat (k := 0) (by norm_num)
  unfold row1OK
  simp only [Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨⟨⟨fix_row d1 prep_c m0.1 m0.2 (TT_eq (by norm_num)) (by norm_num) fix1
    (Nat.eq_of_beq_eq_true g_fix.1) sum_c, pointsOK_of (fun i hi => d1.lt i (by
      rw [← d1.size]; exact hi)) d1.sorted⟩, sdata1.1⟩, codes_ok.2.2.2.2.2.2.2.2.2.1⟩,
    allBelowN_iff.2 fun j hj => ?_⟩
  obtain ⟨ec, lt⟩ := codes_ok.1 j hj
  have m := EL_mat (k := 1 + j) (by omega)
  rw [pword_SJ lt]
  exact restrict_row d1 (sd1 hj) (prep_el (elR_word (by omega) ec lt)) m.1 m.2
    (TT_eq (by omega)) (by norm_num) (allN_spec gen1 j hj)

theorem row4_ok :
    row4OK nPts SJ (pinvs nPts SJ) cRec (pword nPts SJ (pinvs nPts SJ) InvData.t4Word)
      (pcomp nPts (seedWordArr nPts (arrJ aJ) (arrJ bJ) InvData.x4Root)
        (pword nPts SJ (pinvs nPts SJ) InvData.x4H)) (posArr nPts InvData.f4Arr) = true := by
  obtain ⟨-, d4⟩ := data1
  have m0 := EL_mat (k := 0) (by norm_num)
  have m19 := EL_mat (k := 19) (by norm_num)
  have m20 := EL_mat (k := 20) (by norm_num)
  have hx : pcomp nPts (seedWordArr nPts (arrJ aJ) (arrJ bJ) InvData.x4Root)
      (pword nPts SJ (pinvs nPts SJ) InvData.x4H) = arrJ x4J := by
    rw [seedWordArr_arrJ, pword_SJ letters_c4.2.2.1, pcomp_arrJ]
  have hcomm : x4J * t4J = t4J * x4J := comm_of (by norm_num) (by norm_num) el_x4 el_t4 comm.1
  unfold row4OK
  simp only [Bool.and_eq_true, beq_iff_eq]
  rw [hx, pword_SJ letters_c4.2.2.2.2, pcomp_arrJ, pcomp_arrJ, hcomm]
  refine ⟨⟨⟨⟨⟨⟨⟨fix_row d4 (prep_el el_t4) m20.1 m20.2 (TT_eq (by norm_num)) (by norm_num) fix4
    (Nat.eq_of_beq_eq_true g_fix.2.1) sum_4, pointsOK_of (fun i hi => d4.lt i (by
      rw [← d4.size]; exact hi)) d4.sorted⟩, sdata4.1⟩, letters_c4.1⟩,
    allBelowN_iff.2 fun j hj => ?_⟩, ?_⟩, ?_⟩, peq_refl _ _⟩
  · have m := EL_mat (k := 10 + j) (by omega)
    rw [pword_SJ (letters_c4.2.1 j hj)]
    exact restrict_row d4 (sd4 (by omega)) (prep_el (el_c4 hj)) m.1 m.2 (TT_eq (by omega))
      (by norm_num) (allN_spec gen4 j (by omega))
  · exact restrict_row d4 (sd4 (by norm_num)) (prep_el el_x4) m19.1 m19.2 (TT_eq (by norm_num))
      (by norm_num) (allN_spec gen4 9 (by norm_num))
  · exact restrict_row d4 (sd4 (by norm_num)) prep_c m0.1 m0.2 (TT_eq (by norm_num))
      (by norm_num) gen4c

theorem gen6 {j : ℕ} (hj : j < 12) : allN 138 (fun m => ptsImg CFSG.KD.LgHNX.TX CFSG.KD.LgHNX.MS
    CFSG.KD.LgHNX.CM3 CFSG.KD.LgHNX.M (TT (22 + j)) (sliceP PL6 m)
      (imgP PL6 (SP6 j) m (cntP 8800 m)) (cntP 8800 m)) = true := by
  rcases Nat.lt_or_ge j 4 with h | h
  · exact allN_spec gen6a j h
  rcases Nat.lt_or_ge j 8 with h' | h'
  · obtain ⟨i, rfl⟩ : ∃ i, j = 4 + i := ⟨j - 4, by omega⟩
    have e : 22 + (4 + i) = 26 + i := by omega
    rw [e]
    exact allN_spec gen6b i (by omega)
  · obtain ⟨i, rfl⟩ : ∃ i, j = 8 + i := ⟨j - 8, by omega⟩
    have e : 22 + (8 + i) = 30 + i := by omega
    rw [e]
    exact allN_spec gen6c i (by omega)

theorem row6_ok :
    row6Run nPts (arrJ aJ) SJ (pinvs nPts SJ)
      (progRun nPts (initRegs nPts (arrJ aJ) (arrJ bJ)) InvData.m2Prog)
      (pcomp nPts (seedWordArr nPts (arrJ aJ) (arrJ bJ) InvData.m2ConjRoot)
        (pword nPts SJ (pinvs nPts SJ) InvData.m2ConjH)) = true := by
  obtain ⟨-, -, c3, -, cp⟩ := codes_e
  obtain ⟨hr2, hr1⟩ := progRun_arrJ InvData.m2Prog (initRegs nPts (arrJ aJ) (arrJ bJ)) initJ cp
    (initRegs_get rfl rfl).1 (initRegs_get rfl rfl).2
  have hg : pcomp nPts (seedWordArr nPts (arrJ aJ) (arrJ bJ) InvData.m2ConjRoot)
      (pword nPts SJ (pinvs nPts SJ) InvData.m2ConjH) = arrJ gJ := by
    rw [seedWordArr_arrJ, pword_SJ fun l hl => c3 l hl, pcomp_arrJ]
  have d6 := data6
  have m21 := EL_mat (k := 21) (by norm_num)
  have e1 : elR 32 = jR (gJ⁻¹ * (regJ 1 * gJ)) := elR_e (i := 0) (by norm_num)
  have e2 : elR 33 = jR (gJ⁻¹ * (regJ 2 * gJ)) := elR_e (i := 1) (by norm_num)
  have k1 := comm_of (by norm_num) (by norm_num) e1 el_A comm.2.1
  have k2 := comm_of (by norm_num) (by norm_num) e2 el_A comm.2.2
  unfold row6Run row6OK
  simp only [Bool.and_eq_true, beq_iff_eq]
  rw [hg, hr2, hr1 1 (by norm_num), hr1 2 (by norm_num), pinvCand_arrJ, pcomp_arrJ, pcomp_arrJ,
    pcomp_arrJ, pcomp_arrJ, pcomp_arrJ, pcomp_arrJ, pcomp_arrJ, pcomp_arrJ, k1, k2]
  refine ⟨⟨rfl, pisInv_arrJ _⟩, ⟨⟨⟨⟨⟨⟨⟨⟨fix_row d6 (prep_el el_A) m21.1 m21.2
    (TT_eq (by norm_num)) (by norm_num) fix6 (Nat.eq_of_beq_eq_true g_fix.2.2.1) sum_A,
    pointsOK_of (fun i hi => d6.lt i (by rw [← d6.size]; exact hi)) d6.sorted⟩, sdata6.1⟩,
    codes_ok.2.2.2.2.2.2.2.2.2.2.1⟩, allBelowN_iff.2 fun j hj => ?_⟩, ?_⟩, ?_⟩, peq_refl _ _⟩,
    peq_refl _ _⟩⟩
  · obtain ⟨ec, lt⟩ := codes_ok.2.2.2.2.2.1 j hj
    have m := EL_mat (k := 22 + j) (by omega)
    rw [pword_SJ lt]
    exact restrict_row d6 (sd6 (by omega)) (prep_el (elR_word (by omega) ec lt)) m.1 m.2
      (TT_eq (by omega)) (by norm_num) (gen6 (by omega))
  · have m := EL_mat (k := 32) (by norm_num)
    exact restrict_row d6 (sd6 (by norm_num)) (prep_el e1) m.1 m.2 (TT_eq (by norm_num))
      (by norm_num) (gen6 (j := 10) (by norm_num))
  · have m := EL_mat (k := 33) (by norm_num)
    exact restrict_row d6 (sd6 (by norm_num)) (prep_el e2) m.1 m.2 (TT_eq (by norm_num))
      (by norm_num) (gen6 (j := 11) (by norm_num))

theorem pl2_lt : allN 8800 (fun k => Nat.blt (fldW PL2 (Nat.mul 21 k) 21) 1140000) = true ∧
    fldW PL2 0 21 = 0 := by
  refine ⟨?_, ?_⟩
  · quickRfl
  · decide +kernel

theorem filter_zero : ∀ n : ℕ, (List.range (n + 1)).filter (fun i => i == 0) = [0]
  | 0 => rfl
  | n + 1 => by
    rw [List.range_succ, List.filter_append, filter_zero n]
    simp

theorem fixedSet_eq {n : ℕ} {gens : Array (Array ℕ)} (hn : 0 < n)
    (h : ∀ i < n, (gens.all fun g => g[i]! == i) = true ↔ i = 0) : fixedSet n gens = [0] := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  unfold fixedSet
  rw [← filter_zero m]
  refine List.filter_congr fun i hi => ?_
  have hi' := List.mem_range.1 hi
  rw [Bool.eq_iff_iff, h i hi', beq_iff_eq]

theorem t2_pts {k : ℕ} (hk : k < 8800) :
    fldW PL2 (21 * k) 21 < nPts ∧ gi (wJ sL InvData.t2Word) (fldW PL2 (21 * k) 21) =
      fldW PL2 (21 * k) 21 := by
  have h1 : fldW PL2 (21 * k) 21 < nPts := Nat.le_of_ble_eq_true (allN_spec pl2_lt.1 k hk)
  have m34 := EL_mat (k := 34) (by norm_num)
  have e34 := elR_word (k := 34) (by norm_num) codes_ok.2.2.2.2.2.2.1 codes_ok.2.2.2.2.2.2.2.1
  refine ⟨h1, ?_⟩
  rw [gi_of_lt _ h1, ← jR_smul, ← e34]
  exact chunk_list m34.1 m34.2 (TT_eq (by norm_num)) (by norm_num) fix2 hk h1 h1

theorem a8_img {j : ℕ} (hj : j < 6) {i : ℕ} (hi : i < n2 j)
    (h1 : fldW (FL2 j) (21 * i) 21 < nPts) :
    gi (wJ sL InvData.a8Words[j]!) (fldW (FL2 j) (21 * i) 21) = fldW (QL2 j) (21 * i) 21 := by
  have h2 : fldW (QL2 j) (21 * i) 21 < nPts :=
    Nat.le_of_ble_eq_true (allN_spec (allN_spec q2_lt j hj) i hi)
  obtain ⟨ec, lt⟩ := codes_ok.2.2.2.2.2.2.2.2.1 j hj
  have m := EL_mat (k := 35 + j) (by omega)
  rw [gi_of_lt _ h1, ← jR_smul, ← elR_word (by omega) ec lt]
  exact chunk_list (N := n2 j) (nc := (n2 j + 63) / 64) m.1 m.2 (TT_eq (by omega)) (by omega)
    (allN_spec gen2 j hj) hi h1 h2

theorem a8_zero {j : ℕ} (hj : j < 6) : gi (wJ sL InvData.a8Words[j]!) 0 = 0 := by
  have h1 : fldW PL2 (21 * 0) 21 < nPts := (t2_pts (k := 0) (by norm_num)).1
  obtain ⟨ec, lt⟩ := codes_ok.2.2.2.2.2.2.2.2.1 j hj
  have m := EL_mat (k := 35 + j) (by omega)
  have key : gi (wJ sL InvData.a8Words[j]!) (fldW PL2 (21 * 0) 21) = fldW PL2 (21 * 0) 21 := by
    rw [gi_of_lt _ h1, ← jR_smul, ← elR_word (by omega) ec lt]
    exact chunk_list (N := 1) (nc := 1) m.1 m.2 (TT_eq (by omega)) (by norm_num)
      (allN_spec fix0 j hj) (by norm_num) h1 h1
  rw [show 21 * 0 = 0 from rfl, pl2_lt.2] at key
  exact key

theorem a8_moved {K : ℕ} (hK : K < 8799) : ∃ j < 6,
    gi (wJ sL InvData.a8Words[j]!) (fldW PL2 (21 * (K + 1)) 21) ≠ fldW PL2 (21 * (K + 1)) 21 := by
  have hc := allN_spec cov2 K hK
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨hj, hi⟩, hf⟩, hq⟩ := hc
  have hj' : wj K < 6 := Nat.le_of_ble_eq_true hj
  have hi' : wi K < n2 (wj K) := Nat.le_of_ble_eq_true hi
  have hf' : fldW (FL2 (wj K)) (21 * wi K) 21 = fldW PL2 (21 * (K + 1)) 21 :=
    Nat.eq_of_beq_eq_true hf
  change Bool.not (Nat.beq (fldW (QL2 (wj K)) (21 * wi K) 21) (fldW PL2 (21 * (K + 1)) 21)) =
    true at hq
  rw [Bool.not_eq_true', ← Bool.not_eq_true] at hq
  have hq' : fldW (QL2 (wj K)) (21 * wi K) 21 ≠ fldW PL2 (21 * (K + 1)) 21 := fun e =>
    hq (by rw [e]; exact Nat.beq_refl _)
  have h1 : fldW (FL2 (wj K)) (21 * wi K) 21 < nPts := by
    rw [hf']
    exact Nat.le_of_ble_eq_true (allN_spec pl2_lt.1 (K + 1) (by omega))
  refine ⟨wj K, hj', fun e => ?_⟩
  rw [← hf', a8_img hj' hi' h1] at e
  exact hq' (e.trans hf')

theorem t2_inj {k k' : ℕ} (hk : k < 8800) (hk' : k' < 8800)
    (h : fldW PL2 (21 * k) 21 = fldW PL2 (21 * k') 21) : k = k' := by
  have inc : ∀ i j, i < j → j < 8800 → fldW PL2 (21 * i) 21 < fldW PL2 (21 * j) 21 :=
    incr_lt (L := fun k => fldW PL2 (21 * k) 21) fun i hi =>
      Nat.le_of_ble_eq_true (allN_spec pl2 i (by omega))
  rcases Nat.lt_trichotomy k k' with e | e | e
  · exact absurd h (Nat.ne_of_lt (inc _ _ e hk'))
  · exact e
  · exact absurd h.symm (Nat.ne_of_lt (inc _ _ e hk))

@[expose] def conjA2W : List ℕ :=
  List.replicate 19 19 ++ ([21, 19, 34] ++ List.replicate 19 19) ++
    ([21, 19, 34] ++ List.replicate 19 19)

theorem conjA2W_lt : ∀ k ∈ conjA2W, k < 41 := by decide

theorem cj_chk : Nat.beq (CFSG.KC.LL.HN.mm (wordC EL conjA2W) (EL 21))
    (CFSG.KC.LL.HN.mm (EL 34) (wordC EL conjA2W)) = true := by quickRfl

theorem wordC_EL {l : List ℕ} (hl : ∀ k ∈ l, k < 41) :
    Canon 5 133 13 (wordC EL l) ∧ OM (wordC EL l) = matR (l.map elR).prod := by
  obtain ⟨h1, h2⟩ := HNXP.wordC_sound l fun c hc => (EL_mat (hl c hc)).1
  refine ⟨h1, h2.trans ?_⟩
  clear h1 h2
  induction l with
  | nil => exact matR_one.symm
  | cons c l ih =>
    rw [List.map_cons, List.prod_cons, List.map_cons, List.prod_cons, matR_mul,
      (EL_mat (hl c List.mem_cons_self)).2, ih fun c' hc' => hl c' (List.mem_cons_of_mem _ hc')]

theorem perm_cj : permR (elR 34) * permR (conjA2W.map elR).prod =
    permR (conjA2W.map elR).prod * permR (elR 21) := by
  obtain ⟨c1, m1⟩ := wordC_EL conjA2W_lt
  obtain ⟨c21, m21⟩ := EL_mat (k := 21) (by norm_num)
  obtain ⟨c34, m34⟩ := EL_mat (k := 34) (by norm_num)
  have e := congrArg OM (Nat.eq_of_beq_eq_true cj_chk)
  rw [(HNXP.mm_sound c1 c21).2, (HNXP.mm_sound c34 c1).2, m1, m21, m34, ← matR_mul,
    ← matR_mul] at e
  rw [← map_mul, ← map_mul]
  refine Equiv.ext fun i => vL_injective ?_
  rw [permR_apply, permR_apply, vL_smul, vL_smul, e]

theorem countP_fixCard {t : Array ℕ} {g : Equiv.Perm X} (ht : PRep hnsData.n t g) :
    (List.range nPts).countP (fun x => t[x]! == x) = Fintype.card {x : X // g x = x} := by
  rw [countP_range, Fintype.card_subtype]
  symm
  refine Finset.card_bij (fun x _ => x.val) ?_ ?_ ?_
  · intro x hx
    rw [Finset.mem_filter] at hx ⊢
    exact ⟨Finset.mem_range.2 x.isLt, by rw [ht x, hx.2, beq_self_eq_true]⟩
  · intro x _ y _ hxy
    exact Fin.ext hxy
  · intro i hi
    have hi' := Finset.mem_filter.1 hi
    have hin : i < nPts := Finset.mem_range.1 hi'.1
    refine ⟨⟨i, hin⟩, Finset.mem_filter.2 ⟨Finset.mem_univ _, Fin.ext ?_⟩, rfl⟩
    rw [← ht ⟨i, hin⟩]
    exact beq_iff_eq.1 hi'.2

theorem countP_fixConj {t t' : Array ℕ} {g g' s : Equiv.Perm X} (ht : PRep hnsData.n t g)
    (ht' : PRep hnsData.n t' g') (hc : g' * s = s * g) :
    (List.range nPts).countP (fun x => t'[x]! == x) =
      (List.range nPts).countP (fun x => t[x]! == x) := by
  rw [countP_fixCard ht, countP_fixCard ht']
  have e : ∀ y, g' (s y) = s (g y) := fun y => by
    rw [← Equiv.Perm.mul_apply, hc, Equiv.Perm.mul_apply]
  refine Fintype.card_congr (Equiv.subtypeEquiv s.symm fun x => ?_)
  constructor
  · intro h
    apply s.injective
    rw [← e, Equiv.apply_symm_apply]
    exact h
  · intro h
    rw [← s.apply_symm_apply x, e, h]

theorem row2_ok :
    row2OK nPts SJ (pinvs nPts SJ) (pword nPts SJ (pinvs nPts SJ) InvData.t2Word) = true := by
  have lt2 := codes_ok.2.2.2.2.2.2.2.1
  have e34 := elR_word (k := 34) (by norm_num) codes_ok.2.2.2.2.2.2.1 lt2
  have m21 := EL_mat (k := 21) (by norm_num)
  have hc : (List.range nPts).countP
      (fun x => (arrJ (wJ sL InvData.t2Word))[x]! == x) = 8800 := by
    rw [countP_fixConj (prep_el el_A) (prep_el e34) perm_cj]
    exact countP_fix (prep_el el_A) m21.1 m21.2 (Nat.eq_of_beq_eq_true g_fix.2.2.1) sum_A
  unfold row2OK
  simp only [Bool.and_eq_true, beq_iff_eq]
  rw [pword_SJ lt2]
  refine ⟨⟨by rw [fixCount, ← List.countP_eq_length_filter]; exact hc,
    codes_ok.2.2.2.2.2.2.2.2.2.2.2⟩, fixedSet_eq (by norm_num) fun i hi => ?_⟩
  have hsz : (InvData.a8Words.map (pword nPts SJ (pinvs nPts SJ))).size = 6 := by
    rw [Array.size_map, codes_ok.2.2.2.2.2.2.2.2.2.2.2]
  have ha8 : ∀ j < 6, (InvData.a8Words.map (pword nPts SJ (pinvs nPts SJ)))[j]! =
      arrJ (wJ sL InvData.a8Words[j]!) := fun j hj => by
    rw [getElem!_pos _ j (by rw [hsz]; exact hj), Array.getElem_map,
      ← getElem!_pos InvData.a8Words j (by rw [codes_ok.2.2.2.2.2.2.2.2.2.2.2]; exact hj),
      pword_SJ (codes_ok.2.2.2.2.2.2.2.2.1 j hj).2]
  have hone : (#[arrJ (wJ sL InvData.t2Word)].all fun g => g[i]! == i) = true ↔
      (arrJ (wJ sL InvData.t2Word))[i]! = i := by
    rw [Array.all_eq_true]
    constructor
    · intro h
      have h0 := h 0 (by rw [Array.size_singleton]; omega)
      rw [Array.getElem_singleton] at h0
      exact beq_iff_eq.1 h0
    · intro h j hj
      rw [Array.getElem_singleton]
      exact beq_iff_eq.2 h
  rw [Array.all_append, Bool.and_eq_true, hone, Array.all_eq_true, arrJ_get _ hi]
  constructor
  · rintro ⟨hf, ha⟩
    have hf' : (arrJ (wJ sL InvData.t2Word))[i]! = i := by rw [arrJ_get _ hi]; exact hf
    have hcount : (List.range nPts).countP (fun x => (arrJ (wJ sL InvData.t2Word))[x]! == x) =
        8800 := hc
    obtain ⟨k, hk, rfl⟩ := fix_listed hcount (fun k hk => ⟨(t2_pts hk).1, by
      rw [arrJ_get _ (t2_pts hk).1]; exact (t2_pts hk).2⟩) (fun k hk k' hk' e => t2_inj hk hk' e)
      hi hf'
    rcases Nat.eq_zero_or_pos k with rfl | hpos
    · exact pl2_lt.2
    · exfalso
      obtain ⟨K, rfl⟩ : ∃ K, k = K + 1 := ⟨k - 1, by omega⟩
      obtain ⟨j, hj, hne⟩ := a8_moved (K := K) (by omega)
      have hfix := ha j (by rw [hsz]; exact hj)
      rw [← getElem!_pos _ j (by rw [hsz]; exact hj), ha8 j hj, beq_iff_eq,
        arrJ_get _ (t2_pts hk).1] at hfix
      exact hne hfix
  · rintro rfl
    have p0 := t2_pts (k := 0) (by norm_num)
    rw [show 21 * 0 = 0 from rfl, pl2_lt.2] at p0
    refine ⟨p0.2, fun j hj => ?_⟩
    rw [← getElem!_pos _ j hj, ha8 j (by rw [← hsz]; exact hj), beq_iff_eq, arrJ_get _ hi]
    exact a8_zero (by rw [← hsz]; exact hj)

theorem xChecks_ok :
    xChecksO (hnsData.orbit ()) = true := by
  unfold xChecksO xChecksR xChecksS
  rw [← hRegs_eq, ← hStrongArr_eq, HNCTab.cTab_eq, hStrongArr_SJ, hns_n, natTab_alpha, natTab_beta]
  unfold xChecksH
  simp only [Bool.and_eq_true]
  exact ⟨⟨⟨row1_ok, row4_ok⟩, row6_ok⟩, row2_ok⟩

end CertificateChecks.KernelSporSch.HNPt2094

end
