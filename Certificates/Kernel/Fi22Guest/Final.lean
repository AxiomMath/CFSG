module

public import Certificates.Kernel.Fi22Guest.Data
public import Certificates.Kernel.Fi22Rho.Final
import Certificates.Kernel.Fi22Guest.Checks
import Certificates.Kernel.Fi22Core.OrbData
import CFSG.Certificates.Kernel.Spor.RawOrbEval

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelFi22Guest

open CFSG.KC.Enum CFSG.KS CFSG.KS.TW CFSG.KS.Fi22L CFSG.KS.RelTR CFSG.Sporadic.Th.Native
  CFSG.Sporadic.Bridge.TwoGen.Native CFSG.Sporadic.Fi22.Native
  CFSG.AGLEmbedding.KFactProofs.Fi22Guest CertificateChecks.KernelFi22Rho

theorem eq_of_TR {n : Nat} {s t : Table} {f g : Nat → Nat} (hs : TR n s f) (ht : TR n t g)
    (hfg : ∀ i < n, f i = g i) : s = t := by
  refine Array.ext (by rw [hs.1, ht.1]) fun i h1 h2 => ?_
  have hi : i < n := by rw [hs.1] at h1; exact h1
  have e1 := (hs.2 i hi).1
  have e2 := (ht.2 i hi).1
  unfold ap at e1 e2
  rw [getElem!_pos s i h1] at e1
  rw [getElem!_pos t i h2] at e2
  exact UInt32.toNat_inj.1 (by rw [e1, e2, hfg i hi])

theorem movesPt_of {n : Nat} {T : Table} {f : Nat → Nat} (h : TR n T f) {w : Nat} (hw : w < n)
    (hf : f w ≠ w) : movesPt n T = true := by
  unfold movesPt
  rw [Bool.not_eq_true']
  rw [Bool.eq_false_iff]
  intro ha
  have := (allIn_iff.1 ha) w hw
  rw [beq_iff_eq, (h.2 w hw).1] at this
  exact hf this

theorem movesK_spec {f : Nat → Nat} (h : movesK f = true) : ∃ w < 3510, f w ≠ w := by
  unfold movesK at h
  rw [Raw.Orb.strictB_eq, bAnd_iff, Nat.blt_eq, Bool.not_eq_true', Bool.eq_false_iff] at h
  exact ⟨_, h.1, fun e => h.2 (by rw [e]; exact Nat.beq_refl _)⟩

theorem iterK_succ (f : Nat → Nat) (m y : Nat) : iterK f (m + 1) y = f (iterK f m y) := by
  change strictN (iterK f m y) f = _
  rw [Raw.Orb.strictN_eq]

theorem iterK_congr {f g : Nat → Nat} (hfg : ∀ z < 3510, f z = g z ∧ g z < 3510) :
    ∀ (m : Nat) {y : Nat}, y < 3510 → iterK f m y = iterK g m y ∧ iterK g m y < 3510
  | 0, _, hy => ⟨rfl, hy⟩
  | m + 1, y, hy => by
    obtain ⟨e, hl⟩ := iterK_congr hfg m hy
    rw [iterK_succ, iterK_succ, e]
    exact hfg _ hl

theorem compT_TR' {n : Nat} {P Q : Table} {f g : Nat → Nat} (hP : TR n P f) (hQ : TR n Q g) :
    TR n (compT n P Q) fun x => f (g x) := compT_TR hP hQ

theorem powT_TR {n : Nat} (hn : n < 2 ^ 32) {P : Table} {f : Nat → Nat} (hP : TR n P f) :
    ∀ e, TR n (powT n e P) (iterK f e)
  | 0 => idT_TR hn
  | e + 1 => by
    have h := compT_TR hP (powT_TR hn hP e)
    exact TR_congr h fun i _ => (iterK_succ f e i).symm

theorem letter_inv (l : Nat × Bool) {y : Nat} (hy : y < 3510) : F (l.1, !l.2) (F l y) = y := by
  obtain ⟨i, b⟩ := l
  have hg := gen_facts CertificateChecks.KernelFi22.Letters.gen_ok hy
  unfold F letterF
  by_cases hi : i = 0
  · subst hi
    have h0 := (CertificateChecks.KernelFi22C.tree_facts hy).2.2.1
    cases b <;> simp only [↓reduceIte, reg_lk (show (0 : Nat) < 2 by norm_num)] <;> exact h0
  · cases b
    · simp only [hi, ↓reduceIte, Bool.not_false]
      exact hg.2.2.2.2
    · simp only [hi, ↓reduceIte, Bool.not_true, Bool.false_eq_true]
      exact hg.2.2.2.1

theorem winv_cons (l : Nat × Bool) (w : Word) : winv (l :: w) = winv w ++ [(l.1, !l.2)] := by
  unfold winv
  rw [List.map_cons, List.reverse_cons]

theorem winv_left : ∀ (w : Word) {y : Nat}, y < 3510 → wordF F (winv w) (wordF F w y) = y
  | [], _, _ => rfl
  | l :: w, y, hy => by
    rw [winv_cons, wordF_append, wordF_cons]
    change wordF F (winv w) (F (l.1, !l.2) (F l (wordF F w y))) = y
    rw [letter_inv l (wordF_lt w hy)]
    exact winv_left w hy

theorem winv_right : ∀ (w : Word) {y : Nat}, y < 3510 → wordF F w (wordF F (winv w) y) = y
  | [], _, _ => rfl
  | l :: w, y, hy => by
    rw [winv_cons, wordF_append, wordF_cons]
    change F l (wordF F w (wordF F (winv w) (F (l.1, !l.2) y))) = y
    rw [winv_right w (F_lt _ hy)]
    have := letter_inv (l.1, !l.2) hy
    rwa [Bool.not_not] at this

theorem wpow_eq (w : Word) : ∀ (k : Nat) (y : Nat), wordF F (wpow w k) y = iterK (wordF F w) k y
  | 0, _ => rfl
  | k + 1, y => by
    change wordF F (w ++ wpow w k) y = _
    rw [wordF_append, wpow_eq w k, iterK_succ]

theorem tb_eq {k : Nat} (hk : k < 20) {x : Nat} (hx : x < 3510) :
    tb k x = wordF F (List.getD gWords k []) x := by
  have hs : 6 * k + x / 585 < 120 := by omega
  have h := wAll (6 * k + x / 585) hs
  unfold wSl at h
  have e1 : Nat.div (6 * k + x / 585) 6 = k := by
    change (6 * k + x / 585) / 6 = k
    omega
  have e2 : Nat.mul (Nat.mod (6 * k + x / 585) 6) 585 = x / 585 * 585 := by
    change (6 * k + x / 585) % 6 * 585 = x / 585 * 585
    congr 1
    omega
  rw [Raw.Orb.strictB_eq, Raw.Orb.strictB_eq, e1, e2] at h
  have h' := allN_spec h (x % 585) (Nat.mod_lt _ (by norm_num))
  have e3 : Nat.add (x / 585 * 585) (x % 585) = x := by
    change x / 585 * 585 + x % 585 = x
    omega
  rw [e3] at h'
  rw [Nat.eq_of_beq_eq_true h', wordK_eq]

theorem tb_lt {k : Nat} (hk : k < 20) {x : Nat} (hx : x < 3510) : tb k x < 3510 := by
  rw [tb_eq hk hx]
  exact wordF_lt _ hx

theorem gWords_n_all : ∀ j < 18, List.getD gWords (2 + j) [] = nWord j := by decide +kernel

theorem nT_eq {j : Nat} (hj : j < 18) {x : Nat} (hx : x < 3510) :
    nT j x = wordF F (nWord j) x := by
  unfold nT
  rw [← gWords_n_all j hj]
  exact tb_eq (by change 2 + j < 20; omega) hx

theorem nI_facts {j : Nat} (hj : j < 18) {x : Nat} (hx : x < 3510) :
    nI j x < 3510 ∧ nT j (nI j x) = x := by
  have h := allN_spec (allN_spec inv_ok j hj) x hx
  rw [bAnd_iff, Nat.blt_eq] at h
  exact ⟨h.1, Nat.eq_of_beq_eq_true h.2⟩

theorem nI_eq {j : Nat} (hj : j < 18) {x : Nat} (hx : x < 3510) :
    nI j x = wordF F (winv (nWord j)) x := by
  obtain ⟨h1, h2⟩ := nI_facts hj hx
  rw [nT_eq hj h1] at h2
  calc nI j x = wordF F (winv (nWord j)) (wordF F (nWord j) (nI j x)) := (winv_left _ h1).symm
    _ = wordF F (winv (nWord j)) x := by rw [h2]

theorem eData_ok : ∀ i < 4, ∀ s ∈ List.getD eData i [], s ≠ 0 ∧ s.natAbs ≤ 18 := by
  decide +kernel

theorem lmap_eq {s : Int} (hs : s ≠ 0 ∧ s.natAbs ≤ 18) {y : Nat} (hy : y < 3510) :
    lmap s y = wordF F (eLetterWord s) y := by
  obtain ⟨h0, h18⟩ := hs
  rcases s with k | k
  · have hk : 0 < k := by
      rcases k with _ | k
      · exact absurd rfl h0
      · omega
    have hk' : k ≤ 18 := by simpa using h18
    change nT (Nat.pred k) y = _
    unfold eLetterWord
    rw [if_pos (by simp only [Int.ofNat_eq_coe]; omega),
      nT_eq (by rw [Nat.pred_eq_sub_one]; omega) hy]
    rfl
  · have hk' : k < 18 := by simp at h18; omega
    change nI k y = _
    unfold eLetterWord
    rw [if_neg (by simp), nI_eq hk' hy]
    rfl

theorem eFold_TR {ss : List Int} (hss : ∀ s ∈ ss, s ≠ 0 ∧ s.natAbs ≤ 18) :
    TR 3510 (ss.foldr (fun s T => compT 3510 (wordTab 3510 orbL.alpha orbL.alpha orbL.beta
      (invT 3510 orbL.beta) (eLetterWord s)) T) (idT 3510))
      (fun y => List.rec (motive := fun _ => Nat) y (fun s _ ih => strictN ih fun z => lmap s z)
        ss) := by
  induction ss with
  | nil => exact idT_TR (by norm_num)
  | cons s ss ih =>
    have h := compT_TR (wordTab_TR (by norm_num) hL (eLetterWord s))
      (ih fun t ht => hss t (List.mem_cons_of_mem s ht))
    refine TR_congr h fun y hy => ?_
    have hin := ((ih fun t ht => hss t (List.mem_cons_of_mem s ht)).2 y hy).2
    change wordF F (eLetterWord s)
        (List.rec (motive := fun _ => Nat) y (fun s _ ih => strictN ih fun z => lmap s z) ss) =
      strictN (List.rec (motive := fun _ => Nat) y (fun s _ ih => strictN ih fun z => lmap s z) ss)
        fun z => lmap s z
    rw [Raw.Orb.strictN_eq, lmap_eq (hss s List.mem_cons_self) hin]

theorem eT_TR {i : Nat} (hi : i < 4) :
    TR 3510 (eTab 3510 orbL.alpha orbL.alpha orbL.beta (invT 3510 orbL.beta) i) (eT i) := by
  have h := eFold_TR (eData_ok i hi)
  refine TR_congr h fun y hy => ?_
  exact (Nat.eq_of_beq_eq_true (allN_spec (allN_spec e_ok i hi) y hy)).symm

theorem eT_lt {i : Nat} (hi : i < 4) {y : Nat} (hy : y < 3510) : eT i y < 3510 :=
  ((eT_TR hi).2 y hy).2

theorem e_checks : eChecks 3510
    (eTab 3510 orbL.alpha orbL.alpha orbL.beta (invT 3510 orbL.beta) 0)
    (eTab 3510 orbL.alpha orbL.alpha orbL.beta (invT 3510 orbL.beta) 1)
    (eTab 3510 orbL.alpha orbL.alpha orbL.beta (invT 3510 orbL.beta) 2)
    (eTab 3510 orbL.alpha orbL.alpha orbL.beta (invT 3510 orbL.beta) 3) = true := by
  have hE : ∀ i < 4, TR 3510 (eTab 3510 orbL.alpha orbL.alpha orbL.beta (invT 3510 orbL.beta) i)
      (eT i) := fun i hi => eT_TR hi
  have h3 : ∀ i < 4, (powT 3510 3
      (eTab 3510 orbL.alpha orbL.alpha orbL.beta (invT 3510 orbL.beta) i) == idT 3510) = true :=
    fun i hi => by
      rw [beq_iff_eq]
      exact eq_idT_of_TR (by norm_num) (powT_TR (by norm_num) (hE i hi) 3) fun y hy =>
        Nat.eq_of_beq_eq_true (allN_spec (allN_spec e3_ok i hi) y hy)
  have hc : ∀ i < 4, ∀ j < 4,
      (compT 3510 (eTab 3510 orbL.alpha orbL.alpha orbL.beta (invT 3510 orbL.beta) i)
        (eTab 3510 orbL.alpha orbL.alpha orbL.beta (invT 3510 orbL.beta) j) ==
      compT 3510 (eTab 3510 orbL.alpha orbL.alpha orbL.beta (invT 3510 orbL.beta) j)
        (eTab 3510 orbL.alpha orbL.alpha orbL.beta (invT 3510 orbL.beta) i)) = true :=
    fun i hi j hj => by
      rw [beq_iff_eq]
      exact eq_of_TR (compT_TR (hE i hi) (hE j hj)) (compT_TR (hE j hj) (hE i hi))
        fun y hy => Nat.eq_of_beq_eq_true (allN_spec (allN_spec (allN_spec comm_ok i hi) j hj) y hy)
  unfold eChecks
  rw [Bool.and_eq_true, Bool.and_eq_true]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · refine List.all_eq_true.2 fun E hE => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hE
    rcases hE with rfl | rfl | rfl | rfl <;> exact h3 _ (by norm_num)
  · refine List.all_eq_true.2 fun E hE => List.all_eq_true.2 fun G hG => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hE hG
    rcases hE with rfl | rfl | rfl | rfl <;> rcases hG with rfl | rfl | rfl | rfl <;>
      exact hc _ (by norm_num) _ (by norm_num)
  · have hp : ∀ a < 3, ∀ b < 3, ∀ c < 3, ∀ d < 3,
        (a == 0 && b == 0 && c == 0 && d == 0) = false →
        movesPt 3510 (compT 3510 (powT 3510 a
          (eTab 3510 orbL.alpha orbL.alpha orbL.beta (invT 3510 orbL.beta) 0))
          (compT 3510 (powT 3510 b
            (eTab 3510 orbL.alpha orbL.alpha orbL.beta (invT 3510 orbL.beta) 1))
            (compT 3510 (powT 3510 c
              (eTab 3510 orbL.alpha orbL.alpha orbL.beta (invT 3510 orbL.beta) 2))
              (powT 3510 d
                (eTab 3510 orbL.alpha orbL.alpha orbL.beta (invT 3510 orbL.beta) 3))))) =
          true := by
      intro a ha b hb c hc d hd hz
      have ht : 0 < 27 * a + 9 * b + 3 * c + d := by
        rcases Nat.eq_zero_or_pos (27 * a + 9 * b + 3 * c + d) with h | h
        · have h0 : a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 := by omega
          obtain ⟨rfl, rfl, rfl, rfl⟩ := h0
          exact absurd hz (by decide)
        · exact h
      have h80 : 27 * a + 9 * b + 3 * c + d - 1 < 80 := by omega
      have hm := allN_spec prod_ok (27 * a + 9 * b + 3 * c + d - 1) h80
      rw [Nat.succ_eq_add_one, Nat.sub_add_cancel ht] at hm
      obtain ⟨w, hw, hf⟩ := movesK_spec hm
      have hT := compT_TR (powT_TR (by norm_num) (hE 0 (by norm_num)) a)
        (compT_TR (powT_TR (by norm_num) (hE 1 (by norm_num)) b)
          (compT_TR (powT_TR (by norm_num) (hE 2 (by norm_num)) c)
            (powT_TR (by norm_num) (hE 3 (by norm_num)) d)))
      refine movesPt_of hT hw fun e => hf ?_
      unfold prodMap
      have e1 : Nat.div (27 * a + 9 * b + 3 * c + d) 27 = a := by
        change (27 * a + 9 * b + 3 * c + d) / 27 = a
        omega
      have e2 : Nat.mod (Nat.div (27 * a + 9 * b + 3 * c + d) 9) 3 = b := by
        change (27 * a + 9 * b + 3 * c + d) / 9 % 3 = b
        omega
      have e3 : Nat.mod (Nat.div (27 * a + 9 * b + 3 * c + d) 3) 3 = c := by
        change (27 * a + 9 * b + 3 * c + d) / 3 % 3 = c
        omega
      have e4 : Nat.mod (27 * a + 9 * b + 3 * c + d) 3 = d := by
        change (27 * a + 9 * b + 3 * c + d) % 3 = d
        omega
      rw [e1, e2, e3, e4]
      exact e
    refine List.all_eq_true.2 fun a ha => List.all_eq_true.2 fun b hb =>
      List.all_eq_true.2 fun c hc => List.all_eq_true.2 fun d hd => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha hb hc hd
    have ha' : a < 3 := by omega
    have hb' : b < 3 := by omega
    have hc' : c < 3 := by omega
    have hd' : d < 3 := by omega
    rw [Bool.or_eq_true]
    cases hz : (a == 0 && b == 0 && c == 0 && d == 0)
    · exact Or.inr (hp a ha' b hb' c hc' d hd' hz)
    · exact Or.inl rfl

theorem x_eq {z : Nat} (hz : z < 3510) : tb 0 z = wordF F wx z := tb_eq (by norm_num) hz

theorem y_eq {z : Nat} (hz : z < 3510) : tb 1 z = wordF F wy z := tb_eq (by norm_num) hz

theorem qWord_eq {j : Nat} (hj : j ≤ 5) {z : Nat} (hz : z < 3510) :
    qMap j z = wordF F (qWord j) z := by
  unfold qMap
  rcases j with _ | _ | k
  · exact x_eq hz
  · exact y_eq hz
  · have e0 : Nat.beq (k + 2) 0 = false := rfl
    have e1 : Nat.beq (k + 2) 1 = false := rfl
    rw [e0, e1]
    change tb 0 (iterK (tb 1) (k + 1) z) = wordF F (wx ++ wpow wy (k + 1)) z
    rw [wordF_append, wpow_eq]
    have hi := iterK_congr (f := tb 1) (g := wordF F wy)
      (fun y hy => ⟨y_eq hy, wordF_lt _ hy⟩) (k + 1) hz
    rw [hi.1, x_eq hi.2]

theorem nData_ok : ∀ k < 18, (List.getD nData k (0, 0, [])).1 ≤ 5 := by decide +kernel

theorem rel_ok' : relChk = true := rel_ok

theorem rel_pt {z : Nat} (hz : z < 3510) :
    iterK (tb 0) 5 z = z ∧ iterK (tb 1) 5 z = z ∧ tb 0 (tb 1 z) = tb 1 (tb 0 z) := by
  have h := rel_ok'
  rw [relChk.eq_1, bAnd_iff] at h
  have h1 := allN_spec h.1 z hz
  rw [bAnd_iff, bAnd_iff] at h1
  exact ⟨Nat.eq_of_beq_eq_true h1.1, Nat.eq_of_beq_eq_true h1.2.1, Nat.eq_of_beq_eq_true h1.2.2⟩

theorem rel_nq {k : Nat} (hk : k < 18) {z : Nat} (hz : z < 3510) :
    nT k (qMap (List.getD nData k (0, 0, [])).1 z) =
      iterK (qMap (List.getD nData k (0, 0, [])).1) (List.getD nData k (0, 0, [])).2.1
        (nT k z) := by
  have h := rel_ok'
  rw [relChk.eq_1, bAnd_iff] at h
  have h2 := allN_spec h.2 k hk
  rw [Raw.Orb.strictB_eq, Raw.Orb.strictB_eq] at h2
  exact Nat.eq_of_beq_eq_true (allN_spec h2 z hz)

theorem rel_x5 {z : Nat} (hz : z < 3510) : wordF F (wpow wx 5) z = z := by
  have hi := iterK_congr (f := tb 0) (g := wordF F wx) (fun y hy => ⟨x_eq hy, wordF_lt _ hy⟩) 5 hz
  rw [wpow_eq, ← hi.1]
  exact (rel_pt hz).1

theorem rel_y5 {z : Nat} (hz : z < 3510) : wordF F (wpow wy 5) z = z := by
  have hi := iterK_congr (f := tb 1) (g := wordF F wy) (fun y hy => ⟨y_eq hy, wordF_lt _ hy⟩) 5 hz
  rw [wpow_eq, ← hi.1]
  exact (rel_pt hz).2.1

theorem rel_comm {z : Nat} (hz : z < 3510) :
    wordF F (wx ++ wy ++ winv wx ++ winv wy) z = z := by
  have hu : wordF F (winv wy) z < 3510 := wordF_lt _ hz
  have hv : wordF F (winv wx) (wordF F (winv wy) z) < 3510 := wordF_lt _ hu
  simp only [List.append_assoc, wordF_append]
  calc wordF F wx (wordF F wy (wordF F (winv wx) (wordF F (winv wy) z)))
      = tb 0 (tb 1 (wordF F (winv wx) (wordF F (winv wy) z))) := by
        rw [y_eq hv, x_eq (wordF_lt _ hv)]
    _ = tb 1 (tb 0 (wordF F (winv wx) (wordF F (winv wy) z))) := (rel_pt hv).2.2
    _ = z := by rw [x_eq hv, winv_right _ hu, y_eq hu, winv_right _ hz]

theorem rel_n {k : Nat} (hk : k < 18) {z : Nat} (hz : z < 3510) :
    wordF F (nRel (List.getD nData k (0, 0, []))) z = z := by
  have hj : (List.getD nData k (0, 0, [])).1 ≤ 5 := nData_ok k hk
  have hn : (List.getD nData k (0, 0, [])).2.2 = nWord k := rfl
  have hul : wordF F (winv (wpow (qWord (List.getD nData k (0, 0, [])).1)
      (List.getD nData k (0, 0, [])).2.1)) z < 3510 := wordF_lt _ hz
  have hvl := wordF_lt (winv (List.getD nData k (0, 0, [])).2.2) hul
  have hq : ∀ y < 3510, qMap (List.getD nData k (0, 0, [])).1 y =
      wordF F (qWord (List.getD nData k (0, 0, [])).1) y ∧
        wordF F (qWord (List.getD nData k (0, 0, [])).1) y < 3510 :=
    fun y hy => ⟨qWord_eq hj hy, wordF_lt _ hy⟩
  unfold nRel
  simp only [List.append_assoc, wordF_append]
  rw [hn] at hvl ⊢
  calc _ = nT k (qMap (List.getD nData k (0, 0, [])).1 _) := by
        rw [qWord_eq hj hvl, nT_eq hk (wordF_lt _ hvl)]
    _ = iterK (qMap (List.getD nData k (0, 0, [])).1) (List.getD nData k (0, 0, [])).2.1
          (nT k _) := rel_nq hk hvl
    _ = z := by
        rw [nT_eq hk hvl, winv_right _ hul, (iterK_congr hq _ hul).1, ← wpow_eq,
          winv_right _ hz]

theorem q_moves {k : Nat} (hk : k < 18) :
    movesPt 3510 (wordTab 3510 orbL.alpha orbL.alpha orbL.beta (invT 3510 orbL.beta)
      (qWord (List.getD nData k (0, 0, [])).1)) = true := by
  have h0 := qmv_ok
  rw [qMvChk.eq_1] at h0
  have h := allN_spec h0 k hk
  rw [Raw.Orb.strictB_eq] at h
  obtain ⟨w, hw, hf⟩ := movesK_spec h
  refine movesPt_of (wordTab_TR (by norm_num) hL _) hw fun e => hf ?_
  rw [qWord_eq (nData_ok k hk) hw]
  exact e

theorem guest_check : fi22GuestCheck = true := by
  unfold fi22GuestCheck
  rw [CertificateChecks.KernelFi22C.orbitData_eq]
  unfold guestCheck
  rw [Bool.and_eq_true, Bool.and_eq_true]
  refine ⟨⟨?_, ?_⟩, e_checks⟩
  · refine relCheck_of_TR (by norm_num) hL ?_
    intro v hv x hx
    unfold wordRels at hv
    rcases List.mem_append.1 hv with h | h
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl
      · exact rel_x5 hx
      · exact rel_y5 hx
      · exact rel_comm hx
    · obtain ⟨t, htm, rfl⟩ := List.mem_map.1 h
      obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 htm
      have hk' : k < 18 := by
        have e : nData.length = 18 := rfl
        omega
      have e : List.getD nData k (0, 0, []) = nData[k] := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]
        rfl
      have := rel_n hk' hx
      rw [e] at this
      exact this
  · rw [List.all_eq_true]
    intro t htm
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 htm
    have hk' : k < 18 := by
      have e : nData.length = 18 := rfl
      omega
    have e : List.getD nData k (0, 0, []) = nData[k] := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]
      rfl
    have := q_moves hk'
    rw [e] at this
    exact this

end CertificateChecks.KernelFi22Guest

end
