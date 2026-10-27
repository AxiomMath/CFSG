module

public import Certificates.Kernel.J4Q.IsetChk
public import Certificates.Kernel.J4Q.ListAux
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.J4Q.RepConjClos
public import CFSG.Certificates.Kernel.J4Q.RepPack
public import Certificates.Kernel.J4Q.X0Orb

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ4Q

open CFSG.KC.J4Q CFSG.KD.J4Q CFSG.KD.IS CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.QT2

@[expose] def vStep (acc : List (List (List Nat))) (y : List Nat) : List (List (List Nat)) :=
  if y != idT && commProd y && !(acc.any fun G => G.contains y) then acc ++ [spanT y] else acc

@[expose] noncomputable def vY (y : List Nat) : Bool := !commProd y || VGL.any fun G => G.contains y

@[expose] noncomputable def cI (k : Nat) (d : List Nat) : Bool :=
  VGL.all fun G =>
    !(G.all fun g => G.contains (cjT d g)) || !(G.contains (cubeT (compT (xiK k) d))) ||
      IDL.any fun c => actT (xiK k) c == c && actT d c == c && G.all fun g => actT g c == c

@[expose] noncomputable def cII (k : Nat) (d : List Nat) : Bool :=
  !(cubeT (compT (xiK k) d) == idT) ||
    IDL.any (fun c => actT (xiK k) c == c && actT d c == c) ||
    L17.all fun S => !(S.all fun s => S.contains (actT d s)) ||
      S.all fun s => s == 0 || actT (compT (xiK k) d) s != s

theorem compT_U (a b : Nat) : compT (unpackP a) (unpackP b) = unpackP (compB a b) := (compB_sound a b).symm

theorem actT_U (a c : Nat) : actT (unpackP a) c = actB a c := actB_sound a c

theorem beq_U (a b : Nat) : (unpackP a == unpackP b) = eqP a b := by
  unfold eqP
  rw [← unpackP_low a, ← unpackP_low b]
  by_cases h : a % 2 ^ 121 = b % 2 ^ 121
  · rw [h]
    simp
  · have h' : unpackP (a % 2 ^ 121) ≠ unpackP (b % 2 ^ 121) := fun e =>
      h (unpackP_inj (Nat.mod_lt _ (by positivity)) (Nat.mod_lt _ (by positivity)) e)
    rw [beq_eq_false_iff_ne.2 h', beq_eq_false_iff_ne.2 h]

theorem contains_U (L : List Nat) (x : Nat) : (L.map unpackP).contains (unpackP x) = hasP L x := by
  unfold hasP
  induction L with
  | nil => rfl
  | cons y L ih =>
    rw [List.map_cons, List.contains_cons, List.any_cons, ih, beq_U]

theorem idT_U : idT = unpackP idP := beq_iff_eq.1 (by quickRfl)

theorem xk_chk : ((List.range 5).all fun k => xiK k == unpackP (xkP k)) = true := by quickRfl

theorem xiK_U {k : Nat} (hk : k < 5) : xiK k = unpackP (xkP k) :=
  beq_iff_eq.1 (List.all_eq_true.1 xk_chk k (List.mem_range.2 hk))

theorem xiT_U : xiT = unpackP (xkP 1) := beq_iff_eq.1 (by quickRfl)

theorem xiConj_U (p : Nat) : xiConj (unpackP p) = unpackP (xcB p) := by
  unfold xiConj xcB
  have h4 : powT xiT 4 = unpackP (xkP 4) := xiK_U (k := 4) (by decide)
  rw [h4, xiT_U, compT_U, compT_U]

theorem xiConjs_U (p : Nat) : xiConjs (unpackP p) = (xcsB p).map unpackP := by
  unfold xiConjs xcsB
  simp only [xiConj_U, List.map_cons, List.map_nil]

theorem getD_U (l : List Nat) (i : Nat) :
    (l.map unpackP).getD i (unpackP idP) = unpackP (l.getD i idP) := by
  induction l generalizing i with
  | nil => rfl
  | cons x l ih =>
    cases i with
    | zero => rfl
    | succ i => simp only [List.map_cons, List.getD_cons_succ, ih]

theorem foldr_U (l : List Nat) :
    (l.map unpackP).foldr compT (unpackP idP) = unpackP (l.foldr compB idP) := by
  induction l with
  | nil => rfl
  | cons x l ih => rw [List.map_cons, List.foldr_cons, List.foldr_cons, ih, compT_U]

theorem allC {α : Type} {f g : α → Bool} : ∀ {l : List α}, (∀ x ∈ l, f x = g x) → l.all f = l.all g
  | [], _ => rfl
  | x :: l, h => by
    rw [List.all_cons, List.all_cons, h x List.mem_cons_self, allC fun y hy => h y (List.mem_cons_of_mem _ hy)]

theorem anyC {α : Type} {f g : α → Bool} : ∀ {l : List α}, (∀ x ∈ l, f x = g x) → l.any f = l.any g
  | [], _ => rfl
  | x :: l, h => by
    rw [List.any_cons, List.any_cons, h x List.mem_cons_self, anyC fun y hy => h y (List.mem_cons_of_mem _ hy)]

theorem commProd_U (p : Nat) : commProd (unpackP p) = commB p := by
  unfold commProd commB
  simp only [xiConj_U, xiConjs_U, idT_U, getD_U, foldr_U, compT_U, beq_U]

theorem subset_U (c : List Nat) : subsetProds (c.map unpackP) = (subsetB c).map unpackP := by
  unfold subsetProds subsetB
  induction c with
  | nil => rw [idT_U]; rfl
  | cons x c ih =>
    rw [List.map_cons, List.foldr_cons, List.foldr_cons, ih, List.map_append, List.map_map, List.map_map]
    congr 1
    apply List.map_congr_left
    intro y _
    exact compT_U x y

theorem spanT_U (p : Nat) : spanT (unpackP p) = (spanB p).map unpackP := by
  unfold spanT spanB
  rw [xiConjs_U, subset_U]
  have e : (subsetB (xcsB p)).map unpackP = ((subsetB (xcsB p)).map (· % 2 ^ 121)).map unpackP := by
    rw [List.map_map]
    apply List.map_congr_left
    intro y _
    exact (unpackP_low y).symm
  rw [e]
  refine eraseDups_map_inj _ _ (le_refl _) fun a ha b hb h => ?_
  obtain ⟨a', -, rfl⟩ := List.mem_map.1 ha
  obtain ⟨b', -, rfl⟩ := List.mem_map.1 hb
  exact unpackP_inj (Nat.mod_lt _ (by positivity)) (Nat.mod_lt _ (by positivity)) h

theorem any_contains_U (acc : List (List Nat)) (p : Nat) :
    ((acc.map (List.map unpackP)).any fun G => G.contains (unpackP p)) = acc.any fun G => hasP G p := by
  rw [List.any_map]
  exact anyC fun G _ => contains_U G p

theorem vStep_U (acc : List (List Nat)) (p : Nat) :
    vStep (acc.map (List.map unpackP)) (unpackP p) = (vStepB acc p).map (List.map unpackP) := by
  unfold vStep vStepB
  rw [commProd_U, any_contains_U, idT_U, bne, beq_U]
  split
  · rw [List.map_append, List.map_singleton, spanT_U]
  · rfl

theorem fold_U : ∀ (l : List Nat) (acc : List (List Nat)),
    (l.map unpackP).foldl vStep (acc.map (List.map unpackP)) = (l.foldl vStepB acc).map (List.map unpackP)
  | [], _ => rfl
  | x :: l, acc => by
    rw [List.map_cons, List.foldl_cons, List.foldl_cons, vStep_U, fold_U l]

theorem vY_U (p : Nat) : vY (unpackP p) = vYB p := by
  unfold vY vYB VGL
  rw [commProd_U, any_contains_U]

theorem cubeT_U (t : Nat) : cubeT (unpackP t) = unpackP (cubeB t) := by
  unfold cubeT cubeB
  simp only [powT, idT_U, compT_U]

theorem cI_U {k : Nat} (hk : k < 5) (p : Nat) : cI k (unpackP p) = cIB k p := by
  unfold cI cIB VGL
  rw [List.all_map]
  refine allC fun G _ => ?_
  simp only [Function.comp_def, List.all_map, cjT, compT_U, contains_U, xiK_U hk, cubeT_U, actT_U]

theorem cII_U {k : Nat} (hk : k < 5) (p : Nat) : cII k (unpackP p) = cIIB k p := by
  unfold cII cIIB
  simp only [xiK_U hk, compT_U, cubeT_U, beq_U, idT_U, actT_U]

end CertificateChecks.KernelJ4Q

end
