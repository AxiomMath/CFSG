module

public import Certificates.Kernel.TwoHS.HYGlue
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.S9Check
public import CFSG.Certificates.Kernel.Spor.PcompFacts
public import CFSG.Certificates.Kernel.Spor.PK.Perm.CompC

public section

namespace CFSG.KD.TwoHS

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.MulH CFSG.EvenSporadicStandard.TwoHS

theorem wkPc_cn {p q : Nat} (hp : Cn p) (hq : Cn q) : Cn (pc p q) :=
  CFSG.KC.BfsPin.canonK_pcomp hp hq

theorem wkLettersOK_getD {Ls : List (List Nat)} (h : Ls.all lettersOK = true) (j : Nat) :
    lettersOK (Ls.getD j []) = true := by
  rw [List.getD_eq_getElem?_getD]
  cases hj : Ls[j]? with
  | none => rfl
  | some w => exact List.all_eq_true.1 h w (List.mem_of_getElem? hj)

theorem wkSigWords_letters : sigWords.all lettersOK = true := by decide

theorem wkLettersOK_sigWord (wd : List Nat) : lettersOK (sigWord wd) = true := by
  unfold sigWord lettersOK
  rw [List.all_eq_true]
  intro l hl
  simp only [List.mem_flatten, List.mem_map] at hl
  obtain ⟨_, ⟨a, _, rfl⟩, hl⟩ := hl
  exact List.all_eq_true.1 (wkLettersOK_getD wkSigWords_letters (a - 1)) l hl

theorem wfoldK_append (n w m : Nat) (S : Nat → Nat) :
    ∀ (u v : List Nat) (acc : Nat),
      wfoldK n w m S (u ++ v) acc = wfoldK n w m S v (wfoldK n w m S u acc)
  | [], _, _ => rfl
  | l :: u, v, acc => by
    rw [List.cons_append, CFSG.KS.MulH.wfoldK_cons, CFSG.KS.MulH.wfoldK_cons,
      wfoldK_append n w m S u v]

theorem pc_assoc {a b c : Nat} (hc : Cn c) : pc (pc a b) c = pc a (pc b c) := by
  obtain ⟨hn, hw, -, hcl⟩ := CFSG.KS.PF.canon_facts hc
  have hw0 := CFSG.KS.PF.w_pos hw
  unfold pc
  refine CFSG.KS.PF.eq_of_fields hw0 (CFSG.KS.PF.pcomp_shr _ _ (by omega) hw0)
    (CFSG.KS.PF.pcomp_shr _ _ (by omega) hw0) fun i hi => ?_
  rw [CFSG.KS.PF.pg_pcomp (by omega) hi, CFSG.KS.PF.pg_pcomp (by omega) (hcl i hi),
    CFSG.KS.PF.pg_pcomp (by omega) hi, CFSG.KS.PF.pg_pcomp (by omega) hi]

theorem pc_idK_left {x : Nat} (hx : Cn x) : pc idK x = x := by
  obtain ⟨hn, hw, hx0, hxl⟩ := CFSG.KS.PF.canon_facts hx
  have hw0 := CFSG.KS.PF.w_pos hw
  unfold pc idK
  refine CFSG.KS.PF.eq_of_fields hw0 (CFSG.KS.PF.pcomp_shr _ _ (by omega) hw0) hx0 fun i hi => ?_
  rw [CFSG.KS.PF.pg_pcomp (by omega) hi, CFSG.KS.PF.pg_pidn hn hw (hxl i hi)]

theorem pc_idK_right {x : Nat} (hx : Cn x) : pc x idK = x := by
  obtain ⟨hn, hw, hx0, -⟩ := CFSG.KS.PF.canon_facts hx
  have hw0 := CFSG.KS.PF.w_pos hw
  unfold pc idK
  refine CFSG.KS.PF.eq_of_fields hw0 (CFSG.KS.PF.pcomp_shr _ _ (by omega) hw0) hx0 fun i hi => ?_
  rw [CFSG.KS.PF.pg_pcomp (by omega) hi, CFSG.KS.PF.pg_pidn hn hw hi]

theorem wfoldK_cn {S : Nat → Nat} : ∀ (wd : List Nat), (∀ l ∈ wd, Cn (S l)) → ∀ acc, Cn acc →
    Cn (wfoldK 11200 14 (mask 14) S wd acc)
  | [], _, _, h => h
  | l :: rest, hS, acc, h => by
    rw [CFSG.KS.MulH.wfoldK_cons]
    change Cn (wfoldK 11200 14 (mask 14) S rest (pc acc (S l)))
    exact wfoldK_cn rest (fun l' hl' => hS l' (List.mem_cons_of_mem _ hl')) _
      (wkPc_cn h (hS l (List.mem_cons_self ..)))

theorem wfoldK_pc {S : Nat → Nat} : ∀ (wd : List Nat), (∀ l ∈ wd, Cn (S l)) → ∀ acc, Cn acc →
    wfoldK 11200 14 (mask 14) S wd acc = pc acc (wfoldK 11200 14 (mask 14) S wd idK)
  | [], _, acc, h => (pc_idK_right h).symm
  | l :: rest, hS, acc, h => by
    have hS' : ∀ l' ∈ rest, Cn (S l') := fun l' hl' => hS l' (List.mem_cons_of_mem _ hl')
    have hl : Cn (S l) := hS l (List.mem_cons_self ..)
    rw [CFSG.KS.MulH.wfoldK_cons, CFSG.KS.MulH.wfoldK_cons]
    change wfoldK 11200 14 (mask 14) S rest (pc acc (S l)) =
      pc acc (wfoldK 11200 14 (mask 14) S rest (pc idK (S l)))
    rw [wfoldK_pc rest hS' _ (wkPc_cn h hl),
      wfoldK_pc rest hS' _ (wkPc_cn cId hl), pc_idK_left hl,
      pc_assoc (wfoldK_cn rest hS' _ cId)]

theorem L_cn {l : Nat} (h1 : 1 ≤ l) (h6 : l ≤ 6) : Cn (L l) := (harYs_getD h1 h6).2

theorem WK_cn {wd : List Nat} (h : lettersOK wd = true) : Cn (WK wd) :=
  wfoldK_cn wd (fun l hl => L_cn (lettersOK_spec h l hl).1 (lettersOK_spec h l hl).2) _ cId

theorem WK_append {u v : List Nat} (hu : lettersOK u = true) (hv : lettersOK v = true) :
    WK (u ++ v) = pc (WK u) (WK v) := by
  change wfoldK 11200 14 (mask 14) L (u ++ v) idK = pc (WK u) (WK v)
  rw [wfoldK_append]
  exact wfoldK_pc v (fun l hl => L_cn (lettersOK_spec hv l hl).1 (lettersOK_spec hv l hl).2) _
    (WK_cn hu)

@[expose] noncomputable def SGW (l : Nat) : Nat := WK (sigWords.getD (l - 1) [])

theorem SGW_cn (l : Nat) : Cn (SGW l) := WK_cn (wkLettersOK_getD wkSigWords_letters (l - 1))

theorem WK_sigWord : ∀ w : List Nat, WK (sigWord w) = wfoldK 11200 14 (mask 14) SGW w idK
  | [] => rfl
  | a :: rest => by
    have e : sigWord (a :: rest) = sigWords.getD (a - 1) [] ++ sigWord rest := by
      simp [sigWord]
    rw [e, WK_append (wkLettersOK_getD wkSigWords_letters (a - 1)) (wkLettersOK_sigWord rest),
      WK_sigWord rest, CFSG.KS.MulH.wfoldK_cons]
    change pc (SGW a) (wfoldK 11200 14 (mask 14) SGW rest idK) =
      wfoldK 11200 14 (mask 14) SGW rest (pc idK (SGW a))
    rw [wfoldK_pc rest (fun l _ => SGW_cn l) _ (wkPc_cn cId (SGW_cn a)), pc_idK_left (SGW_cn a)]

@[expose] noncomputable def wfC (S : Nat → Nat) (wd : List Nat) (acc : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun acc => acc)
    (fun l _ ih acc => strictN (pcompC 11200 14 (mask 14) acc (S l)) ih) wd acc

theorem wfoldK_eq_C (S : Nat → Nat) : ∀ (wd : List Nat) (acc : Nat),
    wfoldK 11200 14 (mask 14) S wd acc = wfC S wd acc
  | [], _ => rfl
  | l :: wd, acc => by
    rw [CFSG.KS.MulH.wfoldK_cons, wfoldK_eq_C S wd]
    change _ = strictN (pcompC 11200 14 (mask 14) acc (S l)) (wfC S wd)
    rw [CFSG.KS.PEnum.strictN_app', CFSG.KS.PK.pcompC_eq]

theorem pc_eq_C (p q : Nat) : pc p q = pcompC 11200 14 (mask 14) p q :=
  (CFSG.KS.PK.pcompC_eq 11200 14 p q).symm

theorem WK_nil : WK [] = idK := rfl

theorem wEq_of_beq {u v : List Nat} (hl : (lettersOK u && lettersOK v) = true)
    (h : Nat.beq (WK u) (WK v) = true) : wEq u v = true := by
  unfold wEq
  simp only [hl, ↓reduceIte]
  exact h

theorem not_wEq_of_beq {u v : List Nat} (hl : (lettersOK u && lettersOK v) = true)
    (h : (!Nat.beq (WK u) (WK v)) = true) : (!wEq u v) = true := by
  unfold wEq
  simp only [hl, ↓reduceIte]
  exact h

end CFSG.KD.TwoHS

end
