module

public import Certificates.Kernel.HN1408.SpecDefs
public import Certificates.Kernel.HN1408.Glue
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.BlockCheck
import CFSG.Certificates.Kernel.J2CoverSound
import CFSG.Certificates.Kernel.J2ModelsSound

public section

namespace CFSG.KD.HN1408

open CFSG.KC.Enum CFSG.KS CFSG.KS.MulH
open CFSG.EvenSporadicStandard.HNRecog

theorem pc_assoc {p q r : Nat} (hp : Cn p) (hq : Cn q) (hr : Cn r) :
    pc (pc p q) r = pc p (pc q r) :=
  CFSG.KC.J2Cover.pcomp_assoc hp hq hr

theorem pc_idL {p : Nat} (hp : Cn p) : pc idK p = p := CFSG.KC.J2Models.pcomp_idL hp

theorem pc_idR {p : Nat} (hp : Cn p) : pc p idK = p := CFSG.KC.J2Models.pcomp_idR hp

theorem cn_pc {p q : Nat} (hp : Cn p) (hq : Cn q) : Cn (pc p q) := CFSG.KC.BfsPin.canonK_pcomp hp hq

theorem lettersOK_append {a b : List Nat} :
    lettersOK (a ++ b) = (lettersOK a && lettersOK b) := List.all_append

theorem cn_WK {wd : List Nat} (h : lettersOK wd = true) : Cn (WK wd) := (tabW_eq h).2

theorem wfoldK_append (a b : List Nat) (acc : Nat) :
    wfoldK 1408 11 (mask 11) L (a ++ b) acc =
      wfoldK 1408 11 (mask 11) L b (wfoldK 1408 11 (mask 11) L a acc) := by
  induction a generalizing acc with
  | nil => rfl
  | cons l a ih =>
    rw [List.cons_append, wfoldK_cons, wfoldK_cons, ih]

theorem wfoldK_eq {acc : Nat} (ha : Cn acc) {wd : List Nat} (h : lettersOK wd = true) :
    wfoldK 1408 11 (mask 11) L wd acc = pc acc (WK wd) := by
  induction wd generalizing acc with
  | nil => exact (pc_idR ha).symm
  | cons l wd ih =>
    have h' : lettersOK ([l] ++ wd) = true := h
    rw [lettersOK_append, Bool.and_eq_true] at h'
    have hl := h'
    have hL : Cn (L l) := by
      have := lettersOK_spec hl.1 l (List.mem_singleton_self l)
      exact (gens_getD this.1 this.2).2
    unfold WK
    rw [wfoldK_cons, wfoldK_cons]
    change wfoldK 1408 11 (mask 11) L wd (pc acc (L l)) =
      pc acc (wfoldK 1408 11 (mask 11) L wd (pc idK (L l)))
    rw [ih (cn_pc ha hL) hl.2, ih (cn_pc cId hL) hl.2, pc_idL hL,
      pc_assoc ha hL (cn_WK hl.2)]

theorem WK_append {a b : List Nat} (ha : lettersOK a = true) (hb : lettersOK b = true) :
    WK (a ++ b) = pc (WK a) (WK b) := by
  unfold WK
  rw [wfoldK_append]
  exact wfoldK_eq (cn_WK ha) hb

theorem lettersOK_rep {w : List Nat} (hw : lettersOK w = true) :
    ∀ e, lettersOK (List.replicate e w).flatten = true
  | 0 => rfl
  | e + 1 => by
    rw [List.replicate_succ, List.flatten_cons, lettersOK_append, hw, lettersOK_rep hw e]
    rfl

theorem WK_rep {w : List Nat} (hw : lettersOK w = true) :
    ∀ e, WK (List.replicate e w).flatten = powK (WK w) e
  | 0 => rfl
  | e + 1 => by
    rw [List.replicate_succ, List.flatten_cons, WK_append hw (lettersOK_rep hw e), WK_rep hw e]
    rfl

theorem lettersOK_getD {ws : List (List Nat)} (hws : ∀ w ∈ ws, lettersOK w = true) (i : Nat) :
    lettersOK (ws.getD i []) = true := by
  rw [List.getD_eq_getElem?_getD]
  cases h : ws[i]? with
  | none => rfl
  | some w => exact hws w (List.mem_of_getElem? h)

theorem lettersOK_specWord {ws : List (List Nat)} (hws : ∀ w ∈ ws, lettersOK w = true) :
    ∀ spec : List (Nat × Nat), lettersOK (specWord ws spec) = true
  | [] => rfl
  | p :: spec => by
    have e : specWord ws (p :: spec) =
        (List.replicate p.2 (ws.getD (p.1 - 1) [])).flatten ++ specWord ws spec := by
      simp [specWord]
    rw [e, lettersOK_append, lettersOK_rep (lettersOK_getD hws _), lettersOK_specWord hws spec]
    rfl

theorem getD_map_WK (ws : List (List Nat)) (i : Nat) :
    (ws.map WK).getD i idK = WK (ws.getD i []) := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases ws[i]? <;> rfl

theorem foldl_spec {ws : List (List Nat)} (hws : ∀ w ∈ ws, lettersOK w = true) :
    ∀ (spec : List (Nat × Nat)) {acc : Nat}, Cn acc →
      spec.foldl (fun acc p => pc acc (powK ((ws.map WK).getD (p.1 - 1) idK) p.2)) acc =
        pc acc (WK (specWord ws spec))
  | [], acc, ha => (pc_idR ha).symm
  | p :: spec, acc, ha => by
    have hg := lettersOK_getD hws (p.1 - 1)
    have e : specWord ws (p :: spec) =
        (List.replicate p.2 (ws.getD (p.1 - 1) [])).flatten ++ specWord ws spec := by
      simp [specWord]
    rw [List.foldl_cons, getD_map_WK, ← WK_rep hg,
      foldl_spec hws spec (cn_pc ha (cn_WK (lettersOK_rep hg p.2))), e,
      WK_append (lettersOK_rep hg p.2) (lettersOK_specWord hws spec),
      pc_assoc ha (cn_WK (lettersOK_rep hg p.2)) (cn_WK (lettersOK_specWord hws spec))]

theorem WK_specWord {ws : List (List Nat)} (hws : ∀ w ∈ ws, lettersOK w = true)
    (spec : List (Nat × Nat)) : WK (specWord ws spec) = specK (ws.map WK) spec := by
  unfold specK
  rw [foldl_spec hws spec cId, pc_idL (cn_WK (lettersOK_specWord hws spec))]

theorem cn_specK {ws : List (List Nat)} (hws : ∀ w ∈ ws, lettersOK w = true)
    (spec : List (Nat × Nat)) : Cn (specK (ws.map WK) spec) := by
  rw [← WK_specWord hws spec]
  exact cn_WK (lettersOK_specWord hws spec)

end CFSG.KD.HN1408

end
