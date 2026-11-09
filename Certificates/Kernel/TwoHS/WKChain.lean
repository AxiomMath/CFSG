module

public import Certificates.Kernel.TwoHS.HYOps
public import Certificates.Kernel.Sporadic.OddCore.MulHGlue
public import Certificates.Kernel.TwoHS.HYOpsGlue
public import CFSG.Certificates.Kernel.Spor.PinvSSound

public section

namespace CFSG.KD.TwoHS

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.MulH CFSG.EvenSporadicStandard.TwoHS

theorem wfoldK_append_hy (n w m : Nat) (S : Nat → Nat) :
    ∀ (u v : List Nat) (acc : Nat),
      wfoldK n w m S (u ++ v) acc = wfoldK n w m S v (wfoldK n w m S u acc)
  | [], _, _ => rfl
  | l :: u, v, acc => by
    rw [List.cons_append, CFSG.KS.MulH.wfoldK_cons, CFSG.KS.MulH.wfoldK_cons,
      wfoldK_append_hy n w m S u v]

theorem wfoldK_chain (n w m : Nat) (S : Nat → Nat) (s : Nat) (C : Nat → Nat) :
    ∀ (K : Nat) (wd : List Nat) (j : Nat), wd.length ≤ s * K →
      (∀ k < K, wfoldK n w m S ((wd.drop (s * k)).take s) (C (j + k)) = C (j + k + 1)) →
      wfoldK n w m S wd (C j) = C (j + K)
  | 0, wd, j, hl, _ => by
    have e : wd = [] := List.eq_nil_of_length_eq_zero (by simpa using hl)
    subst e
    rfl
  | K + 1, wd, j, hl, h => by
    have h0 := h 0 (Nat.succ_pos K)
    simp only [Nat.mul_zero, List.drop_zero, Nat.add_zero] at h0
    rw [← List.take_append_drop s wd, wfoldK_append_hy, h0]
    have hl' : (wd.drop s).length ≤ s * K := by
      rw [List.length_drop]
      rw [Nat.mul_succ] at hl
      omega
    have ih := wfoldK_chain n w m S s C K (wd.drop s) (j + 1) hl' (fun k hk => by
      have hk' := h (k + 1) (Nat.succ_lt_succ hk)
      rw [List.drop_drop]
      have e1 : j + (k + 1) = j + 1 + k := by omega
      have e2 : s * (k + 1) = s + s * k := by rw [Nat.mul_succ, Nat.add_comm]
      rw [e1, e2] at hk'
      exact hk')
    rw [ih]
    congr 1
    omega

theorem WK_chain {wd : List Nat} {s K : Nat} {C : Nat → Nat} (hl : wd.length ≤ s * K)
    (h0 : Nat.beq (C 0) idK = true)
    (h : ∀ k < K, Nat.beq (wfoldK 11200 14 (mask 14) L ((wd.drop (s * k)).take s) (C k))
      (C (k + 1)) = true) :
    WK wd = C K := by
  have e0 : idK = C 0 := (Nat.eq_of_beq_eq_true h0).symm
  have hc := wfoldK_chain 11200 14 (mask 14) L s C K wd 0 hl (fun k hk => by
    rw [Nat.zero_add]
    exact Nat.eq_of_beq_eq_true (h k hk))
  rw [Nat.zero_add] at hc
  change wfoldK 11200 14 (mask 14) L wd idK = C K
  rw [e0]
  exact hc

theorem pc_assoc_hy {a b c : Nat} (hc : Cn c) : pc (pc a b) c = pc a (pc b c) := by
  obtain ⟨hn, hw, -, hcl⟩ := CFSG.KS.PF.canon_facts hc
  have hw0 := CFSG.KS.PF.w_pos hw
  unfold pc
  refine CFSG.KS.PF.eq_of_fields hw0 (CFSG.KS.PF.pcomp_shr _ _ (by omega) hw0)
    (CFSG.KS.PF.pcomp_shr _ _ (by omega) hw0) fun i hi => ?_
  rw [CFSG.KS.PF.pg_pcomp (by omega) hi, CFSG.KS.PF.pg_pcomp (by omega) (hcl i hi),
    CFSG.KS.PF.pg_pcomp (by omega) hi, CFSG.KS.PF.pg_pcomp (by omega) hi]

theorem pc_idK_left_hy {x : Nat} (hx : Cn x) : pc idK x = x := by
  obtain ⟨hn, hw, hx0, hxl⟩ := CFSG.KS.PF.canon_facts hx
  have hw0 := CFSG.KS.PF.w_pos hw
  unfold pc idK
  refine CFSG.KS.PF.eq_of_fields hw0 (CFSG.KS.PF.pcomp_shr _ _ (by omega) hw0) hx0 fun i hi => ?_
  rw [CFSG.KS.PF.pg_pcomp (by omega) hi, CFSG.KS.PF.pg_pidn hn hw (hxl i hi)]

theorem pc_idK_right_hy {x : Nat} (hx : Cn x) : pc x idK = x := by
  obtain ⟨hn, hw, hx0, -⟩ := CFSG.KS.PF.canon_facts hx
  have hw0 := CFSG.KS.PF.w_pos hw
  unfold pc idK
  refine CFSG.KS.PF.eq_of_fields hw0 (CFSG.KS.PF.pcomp_shr _ _ (by omega) hw0) hx0 fun i hi => ?_
  rw [CFSG.KS.PF.pg_pcomp (by omega) hi, CFSG.KS.PF.pg_pidn hn hw hi]

theorem wfoldK_cn_hy {S : Nat → Nat} : ∀ (wd : List Nat), (∀ l ∈ wd, Cn (S l)) → ∀ acc, Cn acc →
    Cn (wfoldK 11200 14 (mask 14) S wd acc)
  | [], _, _, h => h
  | l :: rest, hS, acc, h => by
    rw [CFSG.KS.MulH.wfoldK_cons]
    change Cn (wfoldK 11200 14 (mask 14) S rest (pc acc (S l)))
    exact wfoldK_cn_hy rest (fun l' hl' => hS l' (List.mem_cons_of_mem _ hl')) _
      (cPc h (hS l (List.mem_cons_self ..)))

theorem wfoldK_pc_hy {S : Nat → Nat} : ∀ (wd : List Nat), (∀ l ∈ wd, Cn (S l)) → ∀ acc, Cn acc →
    wfoldK 11200 14 (mask 14) S wd acc = pc acc (wfoldK 11200 14 (mask 14) S wd idK)
  | [], _, acc, h => (pc_idK_right_hy h).symm
  | l :: rest, hS, acc, h => by
    have hS' : ∀ l' ∈ rest, Cn (S l') := fun l' hl' => hS l' (List.mem_cons_of_mem _ hl')
    have hl : Cn (S l) := hS l (List.mem_cons_self ..)
    rw [CFSG.KS.MulH.wfoldK_cons, CFSG.KS.MulH.wfoldK_cons]
    change wfoldK 11200 14 (mask 14) S rest (pc acc (S l)) =
      pc acc (wfoldK 11200 14 (mask 14) S rest (pc idK (S l)))
    rw [wfoldK_pc_hy rest hS' _ (cPc h hl),
      wfoldK_pc_hy rest hS' _ (cPc cId hl), pc_idK_left_hy hl,
      pc_assoc_hy (wfoldK_cn_hy rest hS' _ cId)]

theorem L_cn_hy {l : Nat} (h1 : 1 ≤ l) (h6 : l ≤ 6) : Cn (L l) := (harYs_getD h1 h6).2

theorem WK_cn_hy {wd : List Nat} (h : lettersOK wd = true) : Cn (WK wd) :=
  wfoldK_cn_hy wd (fun l hl => L_cn_hy (lettersOK_spec h l hl).1 (lettersOK_spec h l hl).2) _ cId

theorem WK_append_hy {u v : List Nat} (hu : lettersOK u = true) (hv : lettersOK v = true) :
    WK (u ++ v) = pc (WK u) (WK v) := by
  change wfoldK 11200 14 (mask 14) L (u ++ v) idK = pc (WK u) (WK v)
  rw [wfoldK_append_hy]
  exact wfoldK_pc_hy v (fun l hl => L_cn_hy (lettersOK_spec hv l hl).1 (lettersOK_spec hv l hl).2) _
    (WK_cn_hy hu)

@[expose] noncomputable def SGW_hy (l : Nat) : Nat := WK (sigWords.getD (l - 1) [])

theorem SGW_cn_hy (l : Nat) : Cn (SGW_hy l) := WK_cn_hy (lettersOK_getD sigWords_letters (l - 1))

theorem WK_sigWord_hy : ∀ w : List Nat, WK (sigWord w) = wfoldK 11200 14 (mask 14) SGW_hy w idK
  | [] => rfl
  | a :: rest => by
    have e : sigWord (a :: rest) = sigWords.getD (a - 1) [] ++ sigWord rest := by
      simp [sigWord]
    rw [e, WK_append_hy (lettersOK_getD sigWords_letters (a - 1)) (lettersOK_sigWord rest),
      WK_sigWord_hy rest, CFSG.KS.MulH.wfoldK_cons]
    change pc (SGW_hy a) (wfoldK 11200 14 (mask 14) SGW_hy rest idK) =
      wfoldK 11200 14 (mask 14) SGW_hy rest (pc idK (SGW_hy a))
    rw [wfoldK_pc_hy rest (fun l _ => SGW_cn_hy l) _ (cPc cId (SGW_cn_hy a)), pc_idK_left_hy (SGW_cn_hy a)]

theorem wEq_of_beq_hy {u v : List Nat} (hl : (lettersOK u && lettersOK v) = true)
    (h : Nat.beq (WK u) (WK v) = true) : wEq u v = true := by
  unfold wEq
  simp only [hl, ↓reduceIte]
  exact h

theorem not_wEq_of_beq_hy {u v : List Nat} (hl : (lettersOK u && lettersOK v) = true)
    (h : (!Nat.beq (WK u) (WK v)) = true) : (!wEq u v) = true := by
  unfold wEq
  simp only [hl, ↓reduceIte]
  exact h

theorem pinvS_eq_of_pcomp' {n w g gi : Nat} (hg : canonK n w (mask w) (n * w) g = true)
    (hgi : canonK n w (mask w) (n * w) gi = true) (h : pcomp n w (mask w) g gi = pidn n w) :
    pinvS n w (mask w) g = gi := by
  obtain ⟨hn, hw, hg0, hgl⟩ := CFSG.KS.PF.canon_facts hg
  obtain ⟨-, -, hgi0, hgil⟩ := CFSG.KS.PF.canon_facts hgi
  have h1 : ∀ i < n, pg w (mask w) g (pg w (mask w) gi i) = i := fun i hi => by
    have h' : pg w (mask w) (pcomp n w (mask w) g gi) i = pg w (mask w) (pidn n w) i :=
      congrArg (fun p => pg w (mask w) p i) h
    rwa [CFSG.KS.PF.pg_pcomp (by omega) hi, CFSG.KS.PF.pg_pidn hn hw hi] at h'
  have hI : CFSG.KS.PinvS.InjK n w gi :=
    ⟨hgil, fun a ha b hb e => by rw [← h1 a ha, ← h1 b hb, e]⟩
  have h2 : ∀ i < n, pg w (mask w) gi (pg w (mask w) g i) = i := fun i hi => by
    obtain ⟨x, hx, rfl⟩ := CFSG.KS.PinvS.surj_of_injK hI i hi
    rw [h1 x hx]
  have hJ : CFSG.KS.PinvS.InjK n w g :=
    ⟨hgl, fun a ha b hb e => by rw [← h2 a ha, ← h2 b hb, e]⟩
  have hinv := CFSG.KS.PinvS.canonK_pinvS hg hJ
  obtain ⟨-, -, hv0, -⟩ := CFSG.KS.PF.canon_facts hinv
  refine CFSG.KS.PF.eq_of_fields (CFSG.KS.PF.w_pos hw) hv0 hgi0 fun i hi => ?_
  obtain ⟨x, hx, rfl⟩ := CFSG.KS.PinvS.surj_of_injK hJ i hi
  rw [CFSG.KS.PinvS.pg_pinvS (by omega) hJ hx, h2 x hx]

theorem bAnd_true {a b : Bool} (ha : a = true) (hb : b = true) : bAnd(a, b) = true := by
  subst ha
  exact hb

end CFSG.KD.TwoHS

end
