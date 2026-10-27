module

public import Certificates.Data.Kernel.NortonSLPK
public import CFSG.Certificates.Kernel.Common.StrSplit
public import Certificates.Kernel.KDenseP.Axis.Base
import Std.Data.String.ToNat
import all Init.Data.String.Slice
import all Init.Data.String.Search
public import CFSG.Monster.B.TwoA.Unitary.Orbit1408Points
public import CFSG.Monster.B.TwoA.Unitary.Semilinear

public section

namespace CFSG.KC.NortonSLPK

open CFSG.Monster.AxisCount CFSG.AGLEmbedding.Norton

theorem splitK_eq (c : Char) : ∀ (l acc : List Char),
    splitK c l acc = List.splitOnPPrepend (· == c) l acc
  | [], _ => by simp [splitK]
  | x :: xs, acc => by
    unfold splitK
    rw [List.splitOnPPrepend_cons_eq_ite]
    split
    · rw [splitK_eq, List.splitOnPPrepend_nil_right]
    · rw [splitK_eq]

theorem splitK_nil (c : Char) (l : List Char) : splitK c l [] = l.splitOn c := by
  rw [splitK_eq, List.splitOn_eq_splitOnP, List.splitOnPPrepend_nil_right]

theorem space_eq : (" " : String) = String.singleton ' ' := by decide

theorem nl_eq : ("\n" : String) = String.singleton '\n' := by decide

theorem ofList_ne_empty (l : List Char) :
    decide (String.ofList l ≠ "") = !l.isEmpty := by
  cases l with
  | nil => simp
  | cons x xs =>
    have : String.ofList (x :: xs) ≠ "" := by
      intro h
      have := congrArg String.toList h
      simp at this
    simp [this]

theorem tokens_ofList (l : List Char) : tokens (String.ofList l) = (toksK l).map String.ofList := by
  unfold tokens toksK
  rw [space_eq, CFSG.KC.Str.splitOn_ofList, ← splitK_nil, List.filter_map]
  congr 1
  apply List.filter_congr
  intro t _
  exact ofList_ne_empty t

theorem isNumK_spec {p : List Char} (h : isNumK p = true) :
    p ≠ [] ∧ ∀ c ∈ p, c.isDigit = true := by
  unfold isNumK at h
  simp only [Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff, List.all_eq_true] at h
  exact h

theorem toNat?_num {p : List Char} (h : isNumK p = true) :
    (String.ofList p).toNat? = some (decK p) := by
  obtain ⟨hne, hd⟩ := isNumK_spec h
  open String in
  simp only [String.toNat?, Slice.toNat?, Slice.isNat]
  open String in
  simp only [Slice.forIn_eq_forIn_toList, Slice.foldl_eq_foldl_toList, copy_toSlice, toList_ofList]
  rw [CFSG.KC.Str.forIn_yield (y := ((none : Option Bool), true)) p]
  · simp only [hne, ↓reduceIte]
    split
    · congr 1
      exact CFSG.KC.Str.foldl_congr _ _ p 0 fun x hx n => by
        simp [CFSG.KC.Str.ne_underscore (hd x hx)]
    · rename_i h
      exact absurd rfl h
  · intro c hc x
    simp [CFSG.KC.Str.ne_underscore (hd c hc), hd c hc]
    rfl

theorem numK_spec {t : List Char} {n : ℕ} (h : numK t = some n) : tokNat (String.ofList t) = n := by
  unfold numK at h
  split at h
  · rename_i hn
    simp only [Option.some.injEq] at h
    rw [tokNat, toNat?_num hn, Option.getD_some, h]
  · simp at h

theorem numsK_spec : ∀ {ts : List (List Char)} {ns : List ℕ}, numsK ts = some ns →
    (ts.map String.ofList).map tokNat = ns
  | [], ns, h => by simp only [numsK, Option.some.injEq] at h; simp [← h]
  | t :: ts, ns, h => by
    unfold numsK at h
    split at h
    · rename_i n ns' e1 e2
      simp only [Option.some.injEq] at h
      rw [← h, List.map_cons, List.map_cons, numK_spec e1, numsK_spec e2]
    · simp at h

theorem ofList_ne {t u : List Char} (h : ¬t = u) : String.ofList t ≠ String.ofList u :=
  fun e => h (String.ofList_injective e)

theorem lettersK_spec (perms : Array (Array ℕ)) : ∀ {ts : List (List Char)} {w : List Native.Gen},
    lettersK perms ts = some w → decodeLetters perms (ts.map String.ofList) = w
  | [], w, h => by
    simp only [lettersK, Option.some.injEq] at h
    simp [decodeLetters, ← h]
  | [t], w, h => by
    rw [lettersK.eq_def] at h; dsimp only at h
    split_ifs at h with h1 h2 h3
    · subst h1; simp only [Option.some.injEq] at h; subst h; rfl
    · subst h2; simp only [Option.some.injEq] at h; subst h; rfl
    · simp only [Option.some.injEq] at h
      subst h
      rcases h3 with rfl | rfl | rfl <;> rfl
  | [t, u], w, h => by
    rw [lettersK.eq_def] at h; dsimp only at h
    split_ifs at h with h1 h2 h3 h4 h5
    · subst h1
      cases e : lettersK perms [u] with
      | none => rw [e] at h; simp at h
      | some w' =>
        rw [e] at h
        simp only [Option.map_some, Option.some.injEq] at h
        have ih := lettersK_spec perms e
        subst h
        simp only [List.map_cons, List.map_nil] at ih ⊢
        change Native.Gen.xi :: decodeLetters perms [String.ofList u] = _
        rw [ih]
    · subst h2
      cases e : lettersK perms [u] with
      | none => rw [e] at h; simp at h
      | some w' =>
        rw [e] at h
        simp only [Option.map_some, Option.some.injEq] at h
        have ih := lettersK_spec perms e
        subst h
        simp only [List.map_cons, List.map_nil] at ih ⊢
        change Native.Gen.tau :: decodeLetters perms [String.ofList u] = _
        rw [ih]
    · subst h3
      cases e : numK u with
      | none => rw [e] at h; simp at h
      | some k =>
        rw [e] at h
        simp only [Option.map_some, Option.some.injEq] at h
        subst h
        change Native.Gen.perm perms[tokNat (String.ofList u)]! :: decodeLetters perms [] = _
        rw [numK_spec e]
        rfl
    · subst h4
      cases e : numK u with
      | none => rw [e] at h; simp at h
      | some k =>
        rw [e] at h
        simp only [Option.map_some, Option.some.injEq] at h
        subst h
        change Native.Gen.sign (tokNat (String.ofList u)) :: decodeLetters perms [] = _
        rw [numK_spec e]
        rfl
    · subst h5
      simp only [Option.some.injEq] at h
      subst h
      rfl
  | t :: s :: a :: rest, w, h => by
    rw [lettersK.eq_def] at h; dsimp only at h
    split_ifs at h with h1 h2 h3 h4 h5
    · subst h1
      cases e : lettersK perms (s :: a :: rest) with
      | none => rw [e] at h; simp at h
      | some w' =>
        rw [e] at h
        simp only [Option.map_some, Option.some.injEq] at h
        have ih := lettersK_spec perms e
        subst h
        change Native.Gen.xi :: decodeLetters perms ((s :: a :: rest).map String.ofList) = _
        rw [ih]
    · subst h2
      cases e : lettersK perms (s :: a :: rest) with
      | none => rw [e] at h; simp at h
      | some w' =>
        rw [e] at h
        simp only [Option.map_some, Option.some.injEq] at h
        have ih := lettersK_spec perms e
        subst h
        change Native.Gen.tau :: decodeLetters perms ((s :: a :: rest).map String.ofList) = _
        rw [ih]
    · subst h3
      split at h
      · rename_i k w' e1 e2
        simp only [Option.some.injEq] at h
        subst h
        change Native.Gen.perm perms[tokNat (String.ofList s)]! ::
          decodeLetters perms ((a :: rest).map String.ofList) = _
        rw [numK_spec e1, lettersK_spec perms e2]
      · simp at h
    · subst h4
      split at h
      · rename_i k w' e1 e2
        simp only [Option.some.injEq] at h
        subst h
        change Native.Gen.sign (tokNat (String.ofList s)) ::
          decodeLetters perms ((a :: rest).map String.ofList) = _
        rw [numK_spec e1, lettersK_spec perms e2]
      · simp at h
    · subst h5
      cases rest with
      | nil =>
        simp only [Option.some.injEq] at h
        subst h
        rfl
      | cons d rest' =>
        simp only at h
        split at h
        · rename_i s' a' d' w' e1 e2 e3 e4
          simp only [Option.some.injEq] at h
          subst h
          change Native.Gen.rho (tokNat (String.ofList s) != 0, tokNat (String.ofList a),
              tokNat (String.ofList d)) :: decodeLetters perms (rest'.map String.ofList) = _
          rw [numK_spec e1, numK_spec e2, numK_spec e3, lettersK_spec perms e4]
        · simp at h

theorem splitBar_cons {s : String} (hs : s ≠ "|") (r : List String) :
    splitBar (s :: r) = ((splitBar r).1.cons (tokNat s), (splitBar r).2) := by
  conv_lhs => unfold splitBar
  split
  · next h => exact absurd h (List.cons_ne_nil _ _)
  · next w h => exact absurd (List.cons.inj h).1 hs
  · next t rest _ h =>
    obtain ⟨rfl, rfl⟩ := List.cons.inj h
    rfl

theorem barK_spec : ∀ {ts : List (List Char)} {l : List ℕ} {w : List (List Char)},
    barK ts = some (l, w) → splitBar (ts.map String.ofList) = (l, w.map String.ofList)
  | [], l, w, h => by
    simp only [barK, Option.some.injEq, Prod.mk.injEq] at h
    simp [splitBar, ← h.1, ← h.2]
  | t :: rest, l, w, h => by
    simp only [barK] at h
    split_ifs at h with ht
    · subst ht
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      rw [← h.1, ← h.2]
      rfl
    · split at h
      · rename_i n l' w' e1 e2
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        have hne : String.ofList t ≠ "|" := ofList_ne (u := ['|']) ht
        rw [List.map_cons, splitBar_cons hne, barK_spec e2, numK_spec e1, ← h.1, ← h.2]
      · simp at h

theorem lineK_spec {acc acc' : Array (Array ℕ) × Array (ProdStep × List Native.Gen)} {l : List Char}
    (h : lineK acc l = some acc') : decodeProdLine acc (String.ofList l) = acc' := by
  unfold decodeProdLine
  rw [tokens_ofList]
  unfold lineK at h
  generalize toksK l = ts at h ⊢
  cases ts with
  | nil =>
    simp only [lineTK, Option.some.injEq] at h
    subst h
    rfl
  | cons t rest =>
    rw [lineTK.eq_def] at h; dsimp only at h
    rw [List.map_cons]
    split_ifs at h with hP hE hM hI
    · subst hP
      cases e : numsK rest with
      | none => rw [e] at h; simp at h
      | some ns =>
        rw [e] at h
        simp only [Option.map_some, Option.some.injEq] at h
        subst h
        change (acc.1.push (List.map tokNat (rest.map String.ofList)).toArray, acc.2) = _
        rw [numsK_spec e]
    · subst hE
      cases rest with
      | nil => simp at h
      | cons i r =>
        simp only at h
        cases e : numK i with
        | none => rw [e] at h; simp at h
        | some n =>
          rw [e] at h
          simp only [Option.map_some, Option.some.injEq] at h
          subst h
          change (acc.1, acc.2.push (.gen (tokNat (String.ofList i)), [])) = _
          rw [numK_spec e]
    · subst hM
      split at h
      · next ix w eb =>
        cases e : lettersK acc.1 w with
        | none => rw [e] at h; simp at h
        | some ws =>
          rw [e] at h
          simp only [Option.map_some, Option.some.injEq] at h
          subst h
          change (acc.1, acc.2.push (.prod (splitBar (rest.map String.ofList)).1,
            decodeLetters acc.1 (splitBar (rest.map String.ofList)).2)) = _
          rw [barK_spec eb, lettersK_spec acc.1 e]
      · simp at h
    · subst hI
      split at h
      · next ix w eb =>
        cases e : lettersK acc.1 w with
        | none => rw [e] at h; simp at h
        | some ws =>
          rw [e] at h
          simp only [Option.map_some, Option.some.injEq] at h
          subst h
          change (acc.1, acc.2.push (.inv (splitBar (rest.map String.ofList)).1,
            decodeLetters acc.1 (splitBar (rest.map String.ofList)).2)) = _
          rw [barK_spec eb, lettersK_spec acc.1 e]
      · simp at h
    · simp only [Option.some.injEq] at h
      subst h
      have h1 : String.ofList t ≠ "P" := ofList_ne (u := ['P']) hP
      have h2 : String.ofList t ≠ "E" := ofList_ne (u := ['E']) hE
      have h3 : String.ofList t ≠ "M" := ofList_ne (u := ['M']) hM
      have h4 : String.ofList t ≠ "I" := ofList_ne (u := ['I']) hI
      split
      · next h => exact absurd (List.cons.inj h).1 h1
      · next h => exact absurd (List.cons.inj h).1 h2
      · next h => exact absurd (List.cons.inj h).1 h3
      · next h => exact absurd (List.cons.inj h).1 h4
      · rfl

theorem linesK_spec : ∀ {acc acc' : Array (Array ℕ) × Array (ProdStep × List Native.Gen)}
    {ls : List (List Char)}, linesK acc ls = some acc' →
    (ls.map String.ofList).foldl decodeProdLine acc = acc'
  | acc, acc', [], h => by simp only [linesK, Option.some.injEq] at h; simp [h]
  | acc, acc', l :: ls, h => by
    simp only [linesK] at h
    split at h
    · rename_i a e
      rw [List.map_cons, List.foldl_cons, lineK_spec e, linesK_spec h]
    · simp at h

theorem decodeProdSteps_ofList {cs : List Char} {S : Array (ProdStep × List Native.Gen)}
    (h : decodeK cs = some S) : decodeProdSteps (String.ofList cs) = S := by
  unfold decodeK at h
  cases e : linesK (#[], #[]) (splitK '\n' cs []) with
  | none => rw [e] at h; simp at h
  | some acc =>
    rw [e] at h
    simp only [Option.map_some, Option.some.injEq] at h
    unfold decodeProdSteps
    rw [nl_eq, CFSG.KC.Str.splitOn_ofList, ← splitK_nil, linesK_spec e, h]

theorem tagEqB_eq : ∀ {s t : ProdStep}, tagEqB s t = true → s = t
  | .gen i, .gen j, h => by simp only [tagEqB, beq_iff_eq] at h; rw [h]
  | .prod l, .prod m, h => by simp only [tagEqB, beq_iff_eq] at h; rw [h]
  | .inv l, .inv m, h => by simp only [tagEqB, beq_iff_eq] at h; rw [h]
  | .gen _, .prod _, h | .gen _, .inv _, h | .prod _, .gen _, h | .prod _, .inv _, h
  | .inv _, .gen _, h | .inv _, .prod _, h => by simp [tagEqB] at h

theorem stepListEqB_eq : ∀ {a b : List (ProdStep × List Native.Gen)}, stepListEqB a b = true → a = b
  | [], [], _ => rfl
  | s :: ss, t :: ts, h => by
    simp only [stepListEqB, Bool.and_eq_true] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    rw [stepListEqB_eq h3, Prod.ext (tagEqB_eq h1)
      (CertificateChecks.KernelKDenseP.Axis.wordEqB_eq h2)]
  | [], _ :: _, h | _ :: _, [], h => by simp [stepListEqB] at h

theorem eq_of_parseEqB {o : Option (Array (ProdStep × List Native.Gen))}
    {b : Array (ProdStep × List Native.Gen)} (h : parseEqB o b = true) : o = some b := by
  unfold parseEqB at h
  split at h
  · rename_i a
    rw [← Array.toList_inj.1 (stepListEqB_eq h)]
  · simp at h

theorem ofList_nl (L₀ L₁ : List Char) :
    String.ofList L₀ ++ "\n" ++ String.ofList L₁ = String.ofList (L₀ ++ '\n' :: L₁) := by
  rw [show ("\n" : String) = String.ofList ['\n'] from rfl, ← String.ofList_append,
    ← String.ofList_append, List.append_assoc]
  rfl

end CFSG.KC.NortonSLPK

end
